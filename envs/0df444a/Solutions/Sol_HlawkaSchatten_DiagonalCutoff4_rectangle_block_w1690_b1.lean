-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1690_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:23.178544+00:00
-- url     : https://prove2.me/submissions/3a9eaeac-d626-46d1-901a-e889d67e6784

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1690_s3_0 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1487745951/10000000000 : ℝ)*x 0 + (342700517/625000000 : ℝ)*x 1 + (2567647471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1487745951/10000000000 : ℝ)^5143 ≤ (1852874872797/20000000000000 : ℝ)^4119 := by
    have hnat : (1487745951 : ℕ)^5143*20000000000000^4119 ≤ 1852874872797^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487745951 10000000000 1852874872797 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342700517/625000000 : ℝ)^5143 ≤ (47223451669611/100000000000000 : ℝ)^4119 := by
    have hnat : (342700517 : ℕ)^5143*100000000000000^4119 ≤ 47223451669611^4119*625000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342700517 625000000 47223451669611 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567647471/5000000000 : ℝ)^5143 ≤ (21756086977509/50000000000000 : ℝ)^4119 := by
    have hnat : (2567647471 : ℕ)^5143*50000000000000^4119 ≤ 21756086977509^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567647471 5000000000 21756086977509 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1487745951/10000000000 : ℝ), (342700517/625000000 : ℝ), (2567647471/5000000000 : ℝ)] ![(1852874872797/20000000000000 : ℝ), (47223451669611/100000000000000 : ℝ), (21756086977509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1487745951/10000000000 : ℝ)|^5143 ≤ (1852874872797/20000000000000 : ℝ)^4119
        have hw : |(-1487745951/10000000000 : ℝ)|=(1487745951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342700517/625000000 : ℝ)|^5143 ≤ (47223451669611/100000000000000 : ℝ)^4119
        have hw : |(342700517/625000000 : ℝ)|=(342700517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567647471/5000000000 : ℝ)|^5143 ≤ (21756086977509/50000000000000 : ℝ)^4119
        have hw : |(2567647471/5000000000 : ℝ)|=(2567647471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_1 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668777371/1250000000 : ℝ)*x 0 + (-1668468111/10000000000 : ℝ)*x 1 + (2567647441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668777371/1250000000 : ℝ)^5143 ≤ (715589001739/1562500000000 : ℝ)^4119 := by
    have hnat : (668777371 : ℕ)^5143*1562500000000^4119 ≤ 715589001739^4119*1250000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668777371 1250000000 715589001739 1562500000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1668468111/10000000000 : ℝ)^5143 ≤ (5345065274919/50000000000000 : ℝ)^4119 := by
    have hnat : (1668468111 : ℕ)^5143*50000000000000^4119 ≤ 5345065274919^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668468111 10000000000 5345065274919 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567647441/5000000000 : ℝ)^5143 ≤ (43512173320241/100000000000000 : ℝ)^4119 := by
    have hnat : (2567647441 : ℕ)^5143*100000000000000^4119 ≤ 43512173320241^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567647441 5000000000 43512173320241 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668777371/1250000000 : ℝ), (-1668468111/10000000000 : ℝ), (2567647441/5000000000 : ℝ)] ![(715589001739/1562500000000 : ℝ), (5345065274919/50000000000000 : ℝ), (43512173320241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668777371/1250000000 : ℝ)|^5143 ≤ (715589001739/1562500000000 : ℝ)^4119
        have hw : |(668777371/1250000000 : ℝ)|=(668777371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1668468111/10000000000 : ℝ)|^5143 ≤ (5345065274919/50000000000000 : ℝ)^4119
        have hw : |(-1668468111/10000000000 : ℝ)|=(1668468111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567647441/5000000000 : ℝ)|^5143 ≤ (43512173320241/100000000000000 : ℝ)^4119
        have hw : |(2567647441/5000000000 : ℝ)|=(2567647441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_2 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337554901/2500000000 : ℝ)*x 0 + (5135295033/10000000000 : ℝ)*x 1 + (-1668467061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337554901/2500000000 : ℝ)^5143 ≤ (4579770290887/10000000000000 : ℝ)^4119 := by
    have hnat : (1337554901 : ℕ)^5143*10000000000000^4119 ≤ 4579770290887^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337554901 2500000000 4579770290887 10000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135295033/10000000000 : ℝ)^5143 ≤ (10878043729441/25000000000000 : ℝ)^4119 := by
    have hnat : (5135295033 : ℕ)^5143*25000000000000^4119 ≤ 10878043729441^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135295033 10000000000 10878043729441 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1668467061/10000000000 : ℝ)^5143 ≤ (5345061074921/50000000000000 : ℝ)^4119 := by
    have hnat : (1668467061 : ℕ)^5143*50000000000000^4119 ≤ 5345061074921^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668467061 10000000000 5345061074921 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337554901/2500000000 : ℝ), (5135295033/10000000000 : ℝ), (-1668467061/10000000000 : ℝ)] ![(4579770290887/10000000000000 : ℝ), (10878043729441/25000000000000 : ℝ), (5345061074921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337554901/2500000000 : ℝ)|^5143 ≤ (4579770290887/10000000000000 : ℝ)^4119
        have hw : |(1337554901/2500000000 : ℝ)|=(1337554901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135295033/10000000000 : ℝ)|^5143 ≤ (10878043729441/25000000000000 : ℝ)^4119
        have hw : |(5135295033/10000000000 : ℝ)|=(5135295033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1668467061/10000000000 : ℝ)|^5143 ≤ (5345061074921/50000000000000 : ℝ)^4119
        have hw : |(-1668467061/10000000000 : ℝ)|=(1668467061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_3 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131241183/10000000000 : ℝ)*x 0 + (3668565573/10000000000 : ℝ)*x 1 + (2315677263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131241183/10000000000 : ℝ)^5143 ≤ (3316168788411/10000000000000 : ℝ)^4119 := by
    have hnat : (4131241183 : ℕ)^5143*10000000000000^4119 ≤ 3316168788411^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131241183 10000000000 3316168788411 10000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3668565573/10000000000 : ℝ)^5143 ≤ (14295465841817/50000000000000 : ℝ)^4119 := by
    have hnat : (3668565573 : ℕ)^5143*50000000000000^4119 ≤ 14295465841817^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668565573 10000000000 14295465841817 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2315677263/5000000000 : ℝ)^5143 ≤ (7649476082919/20000000000000 : ℝ)^4119 := by
    have hnat : (2315677263 : ℕ)^5143*20000000000000^4119 ≤ 7649476082919^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315677263 5000000000 7649476082919 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131241183/10000000000 : ℝ), (3668565573/10000000000 : ℝ), (2315677263/5000000000 : ℝ)] ![(3316168788411/10000000000000 : ℝ), (14295465841817/50000000000000 : ℝ), (7649476082919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131241183/10000000000 : ℝ)|^5143 ≤ (3316168788411/10000000000000 : ℝ)^4119
        have hw : |(4131241183/10000000000 : ℝ)|=(4131241183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3668565573/10000000000 : ℝ)|^5143 ≤ (14295465841817/50000000000000 : ℝ)^4119
        have hw : |(3668565573/10000000000 : ℝ)|=(3668565573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2315677263/5000000000 : ℝ)|^5143 ≤ (7649476082919/20000000000000 : ℝ)^4119
        have hw : |(2315677263/5000000000 : ℝ)|=(2315677263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_4 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1487908519/10000000000 : ℝ)*x 0 + (2569540553/5000000000 : ℝ)*x 1 + (5479365089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1487908519/10000000000 : ℝ)^5143 ≤ (926563838127/10000000000000 : ℝ)^4119 := by
    have hnat : (1487908519 : ℕ)^5143*10000000000000^4119 ≤ 926563838127^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487908519 10000000000 926563838127 10000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569540553/5000000000 : ℝ)^5143 ≤ (1361007306457/3125000000000 : ℝ)^4119 := by
    have hnat : (2569540553 : ℕ)^5143*3125000000000^4119 ≤ 1361007306457^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569540553 5000000000 1361007306457 3125000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479365089/10000000000 : ℝ)^5143 ≤ (47182127804357/100000000000000 : ℝ)^4119 := by
    have hnat : (5479365089 : ℕ)^5143*100000000000000^4119 ≤ 47182127804357^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479365089 10000000000 47182127804357 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1487908519/10000000000 : ℝ), (2569540553/5000000000 : ℝ), (5479365089/10000000000 : ℝ)] ![(926563838127/10000000000000 : ℝ), (1361007306457/3125000000000 : ℝ), (47182127804357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1487908519/10000000000 : ℝ)|^5143 ≤ (926563838127/10000000000000 : ℝ)^4119
        have hw : |(-1487908519/10000000000 : ℝ)|=(1487908519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569540553/5000000000 : ℝ)|^5143 ≤ (1361007306457/3125000000000 : ℝ)^4119
        have hw : |(2569540553/5000000000 : ℝ)|=(2569540553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479365089/10000000000 : ℝ)|^5143 ≤ (47182127804357/100000000000000 : ℝ)^4119
        have hw : |(5479365089/10000000000 : ℝ)|=(5479365089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_5 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628603177/5000000000 : ℝ)*x 0 + (-1324397153/10000000000 : ℝ)*x 1 + (1369841267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628603177/5000000000 : ℝ)^5143 ≤ (448057341527/1000000000000 : ℝ)^4119 := by
    have hnat : (2628603177 : ℕ)^5143*1000000000000^4119 ≤ 448057341527^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628603177 5000000000 448057341527 1000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324397153/10000000000 : ℝ)^5143 ≤ (8012138245597/100000000000000 : ℝ)^4119 := by
    have hnat : (1324397153 : ℕ)^5143*100000000000000^4119 ≤ 8012138245597^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324397153 10000000000 8012138245597 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369841267/2500000000 : ℝ)^5143 ≤ (23591063789287/50000000000000 : ℝ)^4119 := by
    have hnat : (1369841267 : ℕ)^5143*50000000000000^4119 ≤ 23591063789287^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369841267 2500000000 23591063789287 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628603177/5000000000 : ℝ), (-1324397153/10000000000 : ℝ), (1369841267/2500000000 : ℝ)] ![(448057341527/1000000000000 : ℝ), (8012138245597/100000000000000 : ℝ), (23591063789287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628603177/5000000000 : ℝ)|^5143 ≤ (448057341527/1000000000000 : ℝ)^4119
        have hw : |(2628603177/5000000000 : ℝ)|=(2628603177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324397153/10000000000 : ℝ)|^5143 ≤ (8012138245597/100000000000000 : ℝ)^4119
        have hw : |(-1324397153/10000000000 : ℝ)|=(1324397153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369841267/2500000000 : ℝ)|^5143 ≤ (23591063789287/50000000000000 : ℝ)^4119
        have hw : |(1369841267/2500000000 : ℝ)|=(1369841267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_6 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628603199/5000000000 : ℝ)*x 0 + (5479365111/10000000000 : ℝ)*x 1 + (-1324397031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628603199/5000000000 : ℝ)^5143 ≤ (44805734620927/100000000000000 : ℝ)^4119 := by
    have hnat : (2628603199 : ℕ)^5143*100000000000000^4119 ≤ 44805734620927^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628603199 5000000000 44805734620927 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479365111/10000000000 : ℝ)^5143 ≤ (47182128040891/100000000000000 : ℝ)^4119 := by
    have hnat : (5479365111 : ℕ)^5143*100000000000000^4119 ≤ 47182128040891^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479365111 10000000000 47182128040891 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324397031/10000000000 : ℝ)^5143 ≤ (1001517165507/12500000000000 : ℝ)^4119 := by
    have hnat : (1324397031 : ℕ)^5143*12500000000000^4119 ≤ 1001517165507^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324397031 10000000000 1001517165507 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628603199/5000000000 : ℝ), (5479365111/10000000000 : ℝ), (-1324397031/10000000000 : ℝ)] ![(44805734620927/100000000000000 : ℝ), (47182128040891/100000000000000 : ℝ), (1001517165507/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628603199/5000000000 : ℝ)|^5143 ≤ (44805734620927/100000000000000 : ℝ)^4119
        have hw : |(2628603199/5000000000 : ℝ)|=(2628603199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479365111/10000000000 : ℝ)|^5143 ≤ (47182128040891/100000000000000 : ℝ)^4119
        have hw : |(5479365111/10000000000 : ℝ)|=(5479365111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324397031/10000000000 : ℝ)|^5143 ≤ (1001517165507/12500000000000 : ℝ)^4119
        have hw : |(-1324397031/10000000000 : ℝ)|=(1324397031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s3_7 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131689649/10000000000 : ℝ)*x 0 + (4620876013/10000000000 : ℝ)*x 1 + (3679200243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131689649/10000000000 : ℝ)^5143 ≤ (1036443210761/3125000000000 : ℝ)^4119 := by
    have hnat : (4131689649 : ℕ)^5143*3125000000000^4119 ≤ 1036443210761^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131689649 10000000000 1036443210761 3125000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4620876013/10000000000 : ℝ)^5143 ≤ (3813936248923/10000000000000 : ℝ)^4119 := by
    have hnat : (4620876013 : ℕ)^5143*10000000000000^4119 ≤ 3813936248923^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4620876013 10000000000 3813936248923 10000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679200243/10000000000 : ℝ)^5143 ≤ (28694454748649/100000000000000 : ℝ)^4119 := by
    have hnat : (3679200243 : ℕ)^5143*100000000000000^4119 ≤ 28694454748649^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679200243 10000000000 28694454748649 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131689649/10000000000 : ℝ), (4620876013/10000000000 : ℝ), (3679200243/10000000000 : ℝ)] ![(1036443210761/3125000000000 : ℝ), (3813936248923/10000000000000 : ℝ), (28694454748649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131689649/10000000000 : ℝ)|^5143 ≤ (1036443210761/3125000000000 : ℝ)^4119
        have hw : |(4131689649/10000000000 : ℝ)|=(4131689649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4620876013/10000000000 : ℝ)|^5143 ≤ (3813936248923/10000000000000 : ℝ)^4119
        have hw : |(4620876013/10000000000 : ℝ)|=(4620876013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679200243/10000000000 : ℝ)|^5143 ≤ (28694454748649/100000000000000 : ℝ)^4119
        have hw : |(3679200243/10000000000 : ℝ)|=(3679200243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1690_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9831/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3447/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8629/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8629/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8629/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8629/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8629/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8629/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (9811/100000 : ℝ) ^ (5135/1024 : ℝ) ≤ (175722166528631/20000000000000000000 : ℝ) := by
    have hpowers : (9811/100000 : ℝ)^5135 ≤ (175722166528631/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9811 : ℕ)^5135*20000000000000000000^1024 ≤ 175722166528631^1024*100000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9811 100000 175722166528631 20000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9811/100000 : ℝ)) (X := (175722166528631/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8629/50000 : ℝ) ^ (5135/1024 : ℝ) ≤ (14920226832533443/100000000000000000000 : ℝ) := by
    have hpowers : (8629/50000 : ℝ)^5135 ≤ (14920226832533443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8629 : ℕ)^5135*100000000000000000000^1024 ≤ 14920226832533443^1024*50000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8629 50000 14920226832533443 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8629/50000 : ℝ)) (X := (14920226832533443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000175722166528631/10000000000000000000 : ℝ) ≤ (10000035041525383/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (10000175722166528631/10000000000000000000 : ℝ)^1024 ≤ (10000035041525383/10000000000000000 : ℝ)^5135 := by
      have hnat : (10000175722166528631 : ℕ)^1024*10000000000000000^5135 ≤ 10000035041525383^5135*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000175722166528631 10000000000000000000 10000035041525383 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000035041525383/10000000000000000 : ℝ)) (X := (10000175722166528631/10000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007899418832588299/50000000000000000000 : ℝ) ≤ (2000063006764341/2000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50007899418832588299/50000000000000000000 : ℝ)^1024 ≤ (2000063006764341/2000000000000000 : ℝ)^5135 := by
      have hnat : (50007899418832588299 : ℕ)^1024*2000000000000000^5135 ≤ 2000063006764341^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007899418832588299 50000000000000000000 2000063006764341 2000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000063006764341/2000000000000000 : ℝ)) (X := (50007899418832588299/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014920226832533443/50000000000000000000 : ℝ) ≤ (10000595026118027/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50014920226832533443/50000000000000000000 : ℝ)^1024 ≤ (10000595026118027/10000000000000000 : ℝ)^5135 := by
      have hnat : (50014920226832533443 : ℕ)^1024*10000000000000000^5135 ≤ 10000595026118027^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014920226832533443 50000000000000000000 10000595026118027 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000595026118027/10000000000000000 : ℝ)) (X := (50014920226832533443/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(175722166528631/20000000000000000000 : ℝ) ≤ ((74464766945401096917/74470000000000000000 : ℝ)+2*(139996148161/372350000000000 : ℝ)*(9811/100000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (74464766945401096917/74470000000000000000 : ℝ)+2*(139996148161/372350000000000 : ℝ)*(9811/100000 : ℝ)=(10000035041525383/10000000000000000 : ℝ) by norm_num, show 1+2*(175722166528631/20000000000000000000 : ℝ)=(10000175722166528631/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14920226832533443/100000000000000000000 : ℝ)+(175722166528631/20000000000000000000 : ℝ) ≤ ((74464766945401096917/74470000000000000000 : ℝ)+(139996148161/372350000000000 : ℝ)*((8629/50000 : ℝ)+(9811/100000 : ℝ)))^(5135/1024 : ℝ) := by
    rw [show (74464766945401096917/74470000000000000000 : ℝ)+(139996148161/372350000000000 : ℝ)*((8629/50000 : ℝ)+(9811/100000 : ℝ))=(2000063006764341/2000000000000000 : ℝ) by norm_num, show 1+(14920226832533443/100000000000000000000 : ℝ)+(175722166528631/20000000000000000000 : ℝ)=(50007899418832588299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14920226832533443/100000000000000000000 : ℝ) ≤ ((74464766945401096917/74470000000000000000 : ℝ)+2*(139996148161/372350000000000 : ℝ)*(8629/50000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (74464766945401096917/74470000000000000000 : ℝ)+2*(139996148161/372350000000000 : ℝ)*(8629/50000 : ℝ)=(10000595026118027/10000000000000000 : ℝ) by norm_num, show 1+2*(14920226832533443/100000000000000000000 : ℝ)=(50014920226832533443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74464766945401096917/74470000000000000000 : ℝ)*(X 1 0+X 2 0)+(139996148161/372350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (8629/50000 : ℝ)) (c := (74464766945401096917/74470000000000000000 : ℝ)) (alpha := (139996148161/372350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74464766945401096917/74470000000000000000 : ℝ)*(X 0 1+X 2 1)+(139996148161/372350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (8629/50000 : ℝ)) (c := (74464766945401096917/74470000000000000000 : ℝ)) (alpha := (139996148161/372350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74464766945401096917/74470000000000000000 : ℝ)*(X 0 2+X 1 2)+(139996148161/372350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (8629/50000 : ℝ)) (c := (74464766945401096917/74470000000000000000 : ℝ)) (alpha := (139996148161/372350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1487745951/10000000000 : ℝ)*X 0 0+(342700517/625000000 : ℝ)*X 0 1+(2567647471/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668777371/1250000000 : ℝ)*X 1 0+(-1668468111/10000000000 : ℝ)*X 1 1+(2567647441/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337554901/2500000000 : ℝ)*X 2 0+(5135295033/10000000000 : ℝ)*X 2 1+(-1668467061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4131241183/10000000000 : ℝ)*X 0 0+(3668565573/10000000000 : ℝ)*X 0 1+(2315677263/5000000000 : ℝ)*X 0 2+(4131241183/10000000000 : ℝ)*X 1 0+(3668565573/10000000000 : ℝ)*X 1 1+(2315677263/5000000000 : ℝ)*X 1 2+(4131241183/10000000000 : ℝ)*X 2 0+(3668565573/10000000000 : ℝ)*X 2 1+(2315677263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1487908519/10000000000 : ℝ)*X 0 0+(2569540553/5000000000 : ℝ)*X 0 1+(5479365089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628603177/5000000000 : ℝ)*X 1 0+(-1324397153/10000000000 : ℝ)*X 1 1+(1369841267/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628603199/5000000000 : ℝ)*X 2 0+(5479365111/10000000000 : ℝ)*X 2 1+(-1324397031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4131689649/10000000000 : ℝ)*X 0 0+(4620876013/10000000000 : ℝ)*X 0 1+(3679200243/10000000000 : ℝ)*X 0 2+(4131689649/10000000000 : ℝ)*X 1 0+(4620876013/10000000000 : ℝ)*X 1 1+(3679200243/10000000000 : ℝ)*X 1 2+(4131689649/10000000000 : ℝ)*X 2 0+(4620876013/10000000000 : ℝ)*X 2 1+(3679200243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317849737650550216288860663/93087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23240831/100000000000000 : ℝ)*(base15) + (124408369/100000000000000 : ℝ)*(base29) + (52829387/25000000000000 : ℝ)*(lower2) + (92128167/100000000000000 : ℝ)*(lower3) + (489116557831889/25000000000000 : ℝ)*(major0) + (489116588933981/25000000000000 : ℝ)*(major1) + (489116588933981/25000000000000 : ℝ)*(major2) + (1437138966832003/50000000000000 : ℝ)*(sp0) + (1437138880031093/50000000000000 : ℝ)*(sp1) + (1437141005326569/50000000000000 : ℝ)*(sp2) + (1038649520153629/100000000000000 : ℝ)*(sp3) + (4201397501/100000000000000 : ℝ)*(sp4) + (4227350121/100000000000000 : ℝ)*(sp5) + (471219577/50000000000000 : ℝ)*(sp7) + (64915653912049/6250000000000 : ℝ)*(f.failure) + (1437141067530753/50000000000000 : ℝ)*(f.sum) + (2073803880431/4654375000000000000000000000 : ℝ)*base65 + (836986903839086577/1861750000000000000000000000000000 : ℝ)*base67 + (400614374609086577/1861750000000000000000000000000000 : ℝ)*base69 + (6498032322934136213/1861750000000000000000000000000000 : ℝ)*base71 + (2187406744709/1861750000000000000000000000 : ℝ)*base73 + (4094617682688436577/1861750000000000000000000000000000 : ℝ)*base75 + (27589603575911636213/1861750000000000000000000000000000 : ℝ)*base77 + (3017819171661313423/1861750000000000000000000000000000 : ℝ)*base80 + (1844390371553/744700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (706711/125000000000000000000 : ℝ)*base89 + (1956711/125000000000000000000 : ℝ)*base91 + (1956711/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (499884432209512563682893321/169250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282010989/100000000000000 : ℝ)*(base19) + (1437351/312500000000 : ℝ)*(base23) + (81904373/100000000000000 : ℝ)*(lower1) + (9852797/25000000000000 : ℝ)*(upper3) + (31719507/50000000000000 : ℝ)*(lower4) + (15649023/25000000000000 : ℝ)*(upper5) + (1000163725549219/50000000000000 : ℝ)*(major0) + (1000163725549219/50000000000000 : ℝ)*(major1) + (1000163725549219/50000000000000 : ℝ)*(major2) + (461710067/25000000000000 : ℝ)*(sp2) + (2938719326895451/100000000000000 : ℝ)*(sp4) + (1469359522442231/50000000000000 : ℝ)*(sp5) + (2938717020102863/100000000000000 : ℝ)*(sp6) + (265483869212631/25000000000000 : ℝ)*(sp7) + (265483869212631/25000000000000 : ℝ)*(f.failure) + (2938719326895451/100000000000000 : ℝ)*(f.sum) + (1866535816419/3385000000000000000000000000 : ℝ)*base66 + (515563253136231107/338500000000000000000000000000000 : ℝ)*base68 + (147741763623268893/338500000000000000000000000000000 : ℝ)*base69 + (3023634326832768893/338500000000000000000000000000000 : ℝ)*base71 + (2093586872117/1692500000000000000000000000 : ℝ)*base74 + (3987531055641231107/338500000000000000000000000000000 : ℝ)*base76 + (156654485209768893/338500000000000000000000000000000 : ℝ)*base77 + (64370913570268893/338500000000000000000000000000000 : ℝ)*base79 + (14903816684659/3385000000000000000000000000 : ℝ)*base82 + (518191/500000000000000000000 : ℝ)*base90 + (518191/500000000000000000000 : ℝ)*base92 + (518191/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1690_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3447/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1690_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1690_s4_0 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350205079/10000000000 : ℝ)*x 0 + (1027068039/2000000000 : ℝ)*x 1 + (-1668426743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350205079/10000000000 : ℝ)^5143 ≤ (11449386916397/25000000000000 : ℝ)^4119 := by
    have hnat : (5350205079 : ℕ)^5143*25000000000000^4119 ≤ 11449386916397^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350205079 10000000000 11449386916397 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027068039/2000000000 : ℝ)^5143 ≤ (8702530543029/20000000000000 : ℝ)^4119 := by
    have hnat : (1027068039 : ℕ)^5143*20000000000000^4119 ≤ 8702530543029^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027068039 2000000000 8702530543029 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1668426743/10000000000 : ℝ)^5143 ≤ (10689799606977/100000000000000 : ℝ)^4119 := by
    have hnat : (1668426743 : ℕ)^5143*100000000000000^4119 ≤ 10689799606977^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668426743 10000000000 10689799606977 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350205079/10000000000 : ℝ), (1027068039/2000000000 : ℝ), (-1668426743/10000000000 : ℝ)] ![(11449386916397/25000000000000 : ℝ), (8702530543029/20000000000000 : ℝ), (10689799606977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350205079/10000000000 : ℝ)|^5143 ≤ (11449386916397/25000000000000 : ℝ)^4119
        have hw : |(5350205079/10000000000 : ℝ)|=(5350205079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027068039/2000000000 : ℝ)|^5143 ≤ (8702530543029/20000000000000 : ℝ)^4119
        have hw : |(1027068039/2000000000 : ℝ)|=(1027068039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1668426743/10000000000 : ℝ)|^5143 ≤ (10689799606977/100000000000000 : ℝ)^4119
        have hw : |(-1668426743/10000000000 : ℝ)|=(1668426743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s4_1 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131253771/10000000000 : ℝ)*x 0 + (1834346507/5000000000 : ℝ)*x 1 + (4631222023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131253771/10000000000 : ℝ)^5143 ≤ (16580907024383/50000000000000 : ℝ)^4119 := by
    have hnat : (4131253771 : ℕ)^5143*50000000000000^4119 ≤ 16580907024383^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131253771 10000000000 16580907024383 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1834346507/5000000000 : ℝ)^5143 ≤ (7148042953827/25000000000000 : ℝ)^4119 := by
    have hnat : (1834346507 : ℕ)^5143*25000000000000^4119 ≤ 7148042953827^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834346507 5000000000 7148042953827 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4631222023/10000000000 : ℝ)^5143 ≤ (38246014125609/100000000000000 : ℝ)^4119 := by
    have hnat : (4631222023 : ℕ)^5143*100000000000000^4119 ≤ 38246014125609^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631222023 10000000000 38246014125609 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131253771/10000000000 : ℝ), (1834346507/5000000000 : ℝ), (4631222023/10000000000 : ℝ)] ![(16580907024383/50000000000000 : ℝ), (7148042953827/25000000000000 : ℝ), (38246014125609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131253771/10000000000 : ℝ)|^5143 ≤ (16580907024383/50000000000000 : ℝ)^4119
        have hw : |(4131253771/10000000000 : ℝ)|=(4131253771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1834346507/5000000000 : ℝ)|^5143 ≤ (7148042953827/25000000000000 : ℝ)^4119
        have hw : |(1834346507/5000000000 : ℝ)|=(1834346507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4631222023/10000000000 : ℝ)|^5143 ≤ (38246014125609/100000000000000 : ℝ)^4119
        have hw : |(4631222023/10000000000 : ℝ)|=(4631222023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s4_2 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1487922001/10000000000 : ℝ)*x 0 + (1284780521/2500000000 : ℝ)*x 1 + (85614297/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1487922001/10000000000 : ℝ)^5143 ≤ (9265743209599/100000000000000 : ℝ)^4119 := by
    have hnat : (1487922001 : ℕ)^5143*100000000000000^4119 ≤ 9265743209599^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487922001 10000000000 9265743209599 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284780521/2500000000 : ℝ)^5143 ≤ (5444083427277/12500000000000 : ℝ)^4119 := by
    have hnat : (1284780521 : ℕ)^5143*12500000000000^4119 ≤ 5444083427277^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284780521 2500000000 5444083427277 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85614297/156250000 : ℝ)^5143 ≤ (4718158935543/10000000000000 : ℝ)^4119 := by
    have hnat : (85614297 : ℕ)^5143*10000000000000^4119 ≤ 4718158935543^4119*156250000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85614297 156250000 4718158935543 10000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1487922001/10000000000 : ℝ), (1284780521/2500000000 : ℝ), (85614297/156250000 : ℝ)] ![(9265743209599/100000000000000 : ℝ), (5444083427277/12500000000000 : ℝ), (4718158935543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1487922001/10000000000 : ℝ)|^5143 ≤ (9265743209599/100000000000000 : ℝ)^4119
        have hw : |(-1487922001/10000000000 : ℝ)|=(1487922001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284780521/2500000000 : ℝ)|^5143 ≤ (5444083427277/12500000000000 : ℝ)^4119
        have hw : |(1284780521/2500000000 : ℝ)|=(1284780521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85614297/156250000 : ℝ)|^5143 ≤ (4718158935543/10000000000000 : ℝ)^4119
        have hw : |(85614297/156250000 : ℝ)|=(85614297/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s4_3 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257217681/10000000000 : ℝ)*x 0 + (-1324452081/10000000000 : ℝ)*x 1 + (1369828817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257217681/10000000000 : ℝ)^5143 ≤ (4480585468913/10000000000000 : ℝ)^4119 := by
    have hnat : (5257217681 : ℕ)^5143*10000000000000^4119 ≤ 4480585468913^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257217681 10000000000 4480585468913 10000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324452081/10000000000 : ℝ)^5143 ≤ (400627657639/5000000000000 : ℝ)^4119 := by
    have hnat : (1324452081 : ℕ)^5143*5000000000000^4119 ≤ 400627657639^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324452081 10000000000 400627657639 5000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369828817/2500000000 : ℝ)^5143 ≤ (47181592150833/100000000000000 : ℝ)^4119 := by
    have hnat : (1369828817 : ℕ)^5143*100000000000000^4119 ≤ 47181592150833^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369828817 2500000000 47181592150833 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257217681/10000000000 : ℝ), (-1324452081/10000000000 : ℝ), (1369828817/2500000000 : ℝ)] ![(4480585468913/10000000000000 : ℝ), (400627657639/5000000000000 : ℝ), (47181592150833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257217681/10000000000 : ℝ)|^5143 ≤ (4480585468913/10000000000000 : ℝ)^4119
        have hw : |(5257217681/10000000000 : ℝ)|=(5257217681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324452081/10000000000 : ℝ)|^5143 ≤ (400627657639/5000000000000 : ℝ)^4119
        have hw : |(-1324452081/10000000000 : ℝ)|=(1324452081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369828817/2500000000 : ℝ)|^5143 ≤ (47181592150833/100000000000000 : ℝ)^4119
        have hw : |(1369828817/2500000000 : ℝ)|=(1369828817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s4_4 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328576099/625000000 : ℝ)*x 0 + (2739657791/5000000000 : ℝ)*x 1 + (-1324451771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328576099/625000000 : ℝ)^5143 ≤ (44805853656903/100000000000000 : ℝ)^4119 := by
    have hnat : (328576099 : ℕ)^5143*100000000000000^4119 ≤ 44805853656903^4119*625000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328576099 625000000 44805853656903 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739657791/5000000000 : ℝ)^5143 ≤ (47181595526819/100000000000000 : ℝ)^4119 := by
    have hnat : (2739657791 : ℕ)^5143*100000000000000^4119 ≤ 47181595526819^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739657791 5000000000 47181595526819 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324451771/10000000000 : ℝ)^5143 ≤ (1602510162227/20000000000000 : ℝ)^4119 := by
    have hnat : (1324451771 : ℕ)^5143*20000000000000^4119 ≤ 1602510162227^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324451771 10000000000 1602510162227 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328576099/625000000 : ℝ), (2739657791/5000000000 : ℝ), (-1324451771/10000000000 : ℝ)] ![(44805853656903/100000000000000 : ℝ), (47181595526819/100000000000000 : ℝ), (1602510162227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328576099/625000000 : ℝ)|^5143 ≤ (44805853656903/100000000000000 : ℝ)^4119
        have hw : |(328576099/625000000 : ℝ)|=(328576099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739657791/5000000000 : ℝ)|^5143 ≤ (47181595526819/100000000000000 : ℝ)^4119
        have hw : |(2739657791/5000000000 : ℝ)|=(2739657791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324451771/10000000000 : ℝ)|^5143 ≤ (1602510162227/20000000000000 : ℝ)^4119
        have hw : |(-1324451771/10000000000 : ℝ)|=(1324451771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_s4_5 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131698749/10000000000 : ℝ)*x 0 + (4620750379/10000000000 : ℝ)*x 1 + (3679323833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131698749/10000000000 : ℝ)^5143 ≤ (6633254790517/20000000000000 : ℝ)^4119 := by
    have hnat : (4131698749 : ℕ)^5143*20000000000000^4119 ≤ 6633254790517^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131698749 10000000000 6633254790517 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4620750379/10000000000 : ℝ)^5143 ≤ (38138067758173/100000000000000 : ℝ)^4119 := by
    have hnat : (4620750379 : ℕ)^5143*100000000000000^4119 ≤ 38138067758173^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4620750379 10000000000 38138067758173 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679323833/10000000000 : ℝ)^5143 ≤ (14347829135873/50000000000000 : ℝ)^4119 := by
    have hnat : (3679323833 : ℕ)^5143*50000000000000^4119 ≤ 14347829135873^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679323833 10000000000 14347829135873 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131698749/10000000000 : ℝ), (4620750379/10000000000 : ℝ), (3679323833/10000000000 : ℝ)] ![(6633254790517/20000000000000 : ℝ), (38138067758173/100000000000000 : ℝ), (14347829135873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131698749/10000000000 : ℝ)|^5143 ≤ (6633254790517/20000000000000 : ℝ)^4119
        have hw : |(4131698749/10000000000 : ℝ)|=(4131698749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4620750379/10000000000 : ℝ)|^5143 ≤ (38138067758173/100000000000000 : ℝ)^4119
        have hw : |(4620750379/10000000000 : ℝ)|=(4620750379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679323833/10000000000 : ℝ)|^5143 ≤ (14347829135873/50000000000000 : ℝ)^4119
        have hw : |(3679323833/10000000000 : ℝ)|=(3679323833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1690_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3447/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9831/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8617/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3447/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3447/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3447/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3447/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3447/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3447/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (9831/100000 : ℝ) ^ (5135/1024 : ℝ) ≤ (887629261742251/100000000000000000000 : ℝ) := by
    have hpowers : (9831/100000 : ℝ)^5135 ≤ (887629261742251/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9831 : ℕ)^5135*100000000000000000000^1024 ≤ 887629261742251^1024*100000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9831 100000 887629261742251 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9831/100000 : ℝ)) (X := (887629261742251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3447/20000 : ℝ) ^ (5135/1024 : ℝ) ≤ (14820779882146133/100000000000000000000 : ℝ) := by
    have hpowers : (3447/20000 : ℝ)^5135 ≤ (14820779882146133/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3447 : ℕ)^5135*100000000000000000000^1024 ≤ 14820779882146133^1024*20000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3447 20000 14820779882146133 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3447/20000 : ℝ)) (X := (14820779882146133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000887629261742251/50000000000000000000 : ℝ) ≤ (10000035401203701/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50000887629261742251/50000000000000000000 : ℝ)^1024 ≤ (10000035401203701/10000000000000000 : ℝ)^5135 := by
      have hnat : (50000887629261742251 : ℕ)^1024*10000000000000000^5135 ≤ 10000035401203701^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000887629261742251 50000000000000000000 10000035401203701 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000035401203701/10000000000000000 : ℝ)) (X := (50000887629261742251/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (195343180486609157/195312500000000000 : ℝ) ≤ (2500078307690437/2500000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (195343180486609157/195312500000000000 : ℝ)^1024 ≤ (2500078307690437/2500000000000000 : ℝ)^5135 := by
      have hnat : (195343180486609157 : ℕ)^1024*2500000000000000^5135 ≤ 2500078307690437^5135*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195343180486609157 195312500000000000 2500078307690437 2500000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500078307690437/2500000000000000 : ℝ)) (X := (195343180486609157/195312500000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014820779882146133/50000000000000000000 : ℝ) ≤ (2000118212063959/2000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50014820779882146133/50000000000000000000 : ℝ)^1024 ≤ (2000118212063959/2000000000000000 : ℝ)^5135 := by
      have hnat : (50014820779882146133 : ℕ)^1024*2000000000000000^5135 ≤ 2000118212063959^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014820779882146133 50000000000000000000 2000118212063959 2000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000118212063959/2000000000000000 : ℝ)) (X := (50014820779882146133/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(887629261742251/100000000000000000000 : ℝ) ≤ ((2467826647524729403/2468000000000000000 : ℝ)+2*(277829558047/740400000000000 : ℝ)*(9831/100000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (2467826647524729403/2468000000000000000 : ℝ)+2*(277829558047/740400000000000 : ℝ)*(9831/100000 : ℝ)=(10000035401203701/10000000000000000 : ℝ) by norm_num, show 1+2*(887629261742251/100000000000000000000 : ℝ)=(50000887629261742251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14820779882146133/100000000000000000000 : ℝ)+(887629261742251/100000000000000000000 : ℝ) ≤ ((2467826647524729403/2468000000000000000 : ℝ)+(277829558047/740400000000000 : ℝ)*((3447/20000 : ℝ)+(9831/100000 : ℝ)))^(5135/1024 : ℝ) := by
    rw [show (2467826647524729403/2468000000000000000 : ℝ)+(277829558047/740400000000000 : ℝ)*((3447/20000 : ℝ)+(9831/100000 : ℝ))=(2500078307690437/2500000000000000 : ℝ) by norm_num, show 1+(14820779882146133/100000000000000000000 : ℝ)+(887629261742251/100000000000000000000 : ℝ)=(195343180486609157/195312500000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14820779882146133/100000000000000000000 : ℝ) ≤ ((2467826647524729403/2468000000000000000 : ℝ)+2*(277829558047/740400000000000 : ℝ)*(3447/20000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (2467826647524729403/2468000000000000000 : ℝ)+2*(277829558047/740400000000000 : ℝ)*(3447/20000 : ℝ)=(2000118212063959/2000000000000000 : ℝ) by norm_num, show 1+2*(14820779882146133/100000000000000000000 : ℝ)=(50014820779882146133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2467826647524729403/2468000000000000000 : ℝ)*(X 1 0+X 2 0)+(277829558047/740400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (3447/20000 : ℝ)) (c := (2467826647524729403/2468000000000000000 : ℝ)) (alpha := (277829558047/740400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2467826647524729403/2468000000000000000 : ℝ)*(X 0 1+X 2 1)+(277829558047/740400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (3447/20000 : ℝ)) (c := (2467826647524729403/2468000000000000000 : ℝ)) (alpha := (277829558047/740400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2467826647524729403/2468000000000000000 : ℝ)*(X 0 2+X 1 2)+(277829558047/740400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (3447/20000 : ℝ)) (c := (2467826647524729403/2468000000000000000 : ℝ)) (alpha := (277829558047/740400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5350205079/10000000000 : ℝ)*X 2 0+(1027068039/2000000000 : ℝ)*X 2 1+(-1668426743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s4_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4131253771/10000000000 : ℝ)*X 0 0+(1834346507/5000000000 : ℝ)*X 0 1+(4631222023/10000000000 : ℝ)*X 0 2+(4131253771/10000000000 : ℝ)*X 1 0+(1834346507/5000000000 : ℝ)*X 1 1+(4631222023/10000000000 : ℝ)*X 1 2+(4131253771/10000000000 : ℝ)*X 2 0+(1834346507/5000000000 : ℝ)*X 2 1+(4631222023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s4_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1487922001/10000000000 : ℝ)*X 0 0+(1284780521/2500000000 : ℝ)*X 0 1+(85614297/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s4_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5257217681/10000000000 : ℝ)*X 1 0+(-1324452081/10000000000 : ℝ)*X 1 1+(1369828817/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s4_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((328576099/625000000 : ℝ)*X 2 0+(2739657791/5000000000 : ℝ)*X 2 1+(-1324451771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s4_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4131698749/10000000000 : ℝ)*X 0 0+(4620750379/10000000000 : ℝ)*X 0 1+(3679323833/10000000000 : ℝ)*X 0 2+(4131698749/10000000000 : ℝ)*X 1 0+(4620750379/10000000000 : ℝ)*X 1 1+(3679323833/10000000000 : ℝ)*X 1 2+(4131698749/10000000000 : ℝ)*X 2 0+(4620750379/10000000000 : ℝ)*X 2 1+(3679323833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52825985840566434701047821/15425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121791821/20000000000000 : ℝ)*(base19) + (139445057/20000000000000 : ℝ)*(base23) + (146997127/100000000000000 : ℝ)*(lower1) + (204721091/100000000000000 : ℝ)*(upper3) + (10260361/50000000000000 : ℝ)*(lower4) + (250107374520331/12500000000000 : ℝ)*(major0) + (250107374520331/12500000000000 : ℝ)*(major1) + (250107374520331/12500000000000 : ℝ)*(major2) + (1462451367/25000000000000 : ℝ)*(sp0) + (20565841/12500000000000 : ℝ)*(sp1) + (367437526779843/12500000000000 : ℝ)*(sp2) + (1469749802639819/50000000000000 : ℝ)*(sp3) + (2939493667207991/100000000000000 : ℝ)*(sp4) + (132777187425397/12500000000000 : ℝ)*(sp5) + (66388603995619/6250000000000 : ℝ)*(f.failure) + (367437526779843/12500000000000 : ℝ)*(f.sum) + (22075651298137/4627500000000000000000000000 : ℝ)*base65 + (116497921853052821/92550000000000000000000000000000 : ℝ)*base68 + (225484516791347179/92550000000000000000000000000000 : ℝ)*base69 + (827818122672047179/92550000000000000000000000000000 : ℝ)*base71 + (363741683869/2313750000000000000000000000 : ℝ)*base74 + (354254604179747179/92550000000000000000000000000000 : ℝ)*base75 + (209287385345147179/92550000000000000000000000000000 : ℝ)*base77 + (1017340706984352821/92550000000000000000000000000000 : ℝ)*base80 + (20748276145471/9255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (460059/125000000000000000000 : ℝ)*base90 + (460059/125000000000000000000 : ℝ)*base92 + (460059/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1690_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3447/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1690_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1690_box_0 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1152807291/10000000000 : ℝ)*x 0 + (2714031803/5000000000 : ℝ)*x 1 + (2714031531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1152807291/10000000000 : ℝ)^5143 ≤ (6737606647333/100000000000000 : ℝ)^4119 := by
    have hnat : (1152807291 : ℕ)^5143*100000000000000^4119 ≤ 6737606647333^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152807291 10000000000 6737606647333 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714031803/5000000000 : ℝ)^5143 ≤ (46631199583711/100000000000000 : ℝ)^4119 := by
    have hnat : (2714031803 : ℕ)^5143*100000000000000^4119 ≤ 46631199583711^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714031803 5000000000 46631199583711 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714031531/5000000000 : ℝ)^5143 ≤ (23315596874259/50000000000000 : ℝ)^4119 := by
    have hnat : (2714031531 : ℕ)^5143*50000000000000^4119 ≤ 23315596874259^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714031531 5000000000 23315596874259 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1152807291/10000000000 : ℝ), (2714031803/5000000000 : ℝ), (2714031531/5000000000 : ℝ)] ![(6737606647333/100000000000000 : ℝ), (46631199583711/100000000000000 : ℝ), (23315596874259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1152807291/10000000000 : ℝ)|^5143 ≤ (6737606647333/100000000000000 : ℝ)^4119
        have hw : |(-1152807291/10000000000 : ℝ)|=(1152807291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714031803/5000000000 : ℝ)|^5143 ≤ (46631199583711/100000000000000 : ℝ)^4119
        have hw : |(2714031803/5000000000 : ℝ)|=(2714031803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714031531/5000000000 : ℝ)|^5143 ≤ (23315596874259/50000000000000 : ℝ)^4119
        have hw : |(2714031531/5000000000 : ℝ)|=(2714031531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_1 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045208377/2000000000 : ℝ)*x 0 + (-719988957/5000000000 : ℝ)*x 1 + (2714031629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045208377/2000000000 : ℝ)^5143 ≤ (22237170919911/50000000000000 : ℝ)^4119 := by
    have hnat : (1045208377 : ℕ)^5143*50000000000000^4119 ≤ 22237170919911^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045208377 2000000000 22237170919911 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719988957/5000000000 : ℝ)^5143 ≤ (444723115081/5000000000000 : ℝ)^4119 := by
    have hnat : (719988957 : ℕ)^5143*5000000000000^4119 ≤ 444723115081^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719988957 5000000000 444723115081 5000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714031629/5000000000 : ℝ)^5143 ≤ (5828899481363/12500000000000 : ℝ)^4119 := by
    have hnat : (2714031629 : ℕ)^5143*12500000000000^4119 ≤ 5828899481363^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714031629 5000000000 5828899481363 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045208377/2000000000 : ℝ), (-719988957/5000000000 : ℝ), (2714031629/5000000000 : ℝ)] ![(22237170919911/50000000000000 : ℝ), (444723115081/5000000000000 : ℝ), (5828899481363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045208377/2000000000 : ℝ)|^5143 ≤ (22237170919911/50000000000000 : ℝ)^4119
        have hw : |(1045208377/2000000000 : ℝ)|=(1045208377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-719988957/5000000000 : ℝ)|^5143 ≤ (444723115081/5000000000000 : ℝ)^4119
        have hw : |(-719988957/5000000000 : ℝ)|=(719988957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714031629/5000000000 : ℝ)|^5143 ≤ (5828899481363/12500000000000 : ℝ)^4119
        have hw : |(2714031629/5000000000 : ℝ)|=(2714031629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_2 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226041607/10000000000 : ℝ)*x 0 + (5428063347/10000000000 : ℝ)*x 1 + (-719989087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226041607/10000000000 : ℝ)^5143 ≤ (44474338885851/100000000000000 : ℝ)^4119 := by
    have hnat : (5226041607 : ℕ)^5143*100000000000000^4119 ≤ 44474338885851^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226041607 10000000000 44474338885851 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428063347/10000000000 : ℝ)^5143 ≤ (46631196805559/100000000000000 : ℝ)^4119 := by
    have hnat : (5428063347 : ℕ)^5143*100000000000000^4119 ≤ 46631196805559^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428063347 10000000000 46631196805559 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719989087/5000000000 : ℝ)^5143 ≤ (222361607671/2500000000000 : ℝ)^4119 := by
    have hnat : (719989087 : ℕ)^5143*2500000000000^4119 ≤ 222361607671^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719989087 5000000000 222361607671 2500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226041607/10000000000 : ℝ), (5428063347/10000000000 : ℝ), (-719989087/5000000000 : ℝ)] ![(44474338885851/100000000000000 : ℝ), (46631196805559/100000000000000 : ℝ), (222361607671/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226041607/10000000000 : ℝ)|^5143 ≤ (44474338885851/100000000000000 : ℝ)^4119
        have hw : |(5226041607/10000000000 : ℝ)|=(5226041607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428063347/10000000000 : ℝ)|^5143 ≤ (46631196805559/100000000000000 : ℝ)^4119
        have hw : |(5428063347/10000000000 : ℝ)|=(5428063347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-719989087/5000000000 : ℝ)|^5143 ≤ (222361607671/2500000000000 : ℝ)^4119
        have hw : |(-719989087/5000000000 : ℝ)|=(719989087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_3 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1128888553/2500000000 : ℝ)*x 0 + (3961727963/10000000000 : ℝ)*x 1 + (158469087/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128888553/2500000000 : ℝ)^5143 ≤ (9264262398691/25000000000000 : ℝ)^4119 := by
    have hnat : (1128888553 : ℕ)^5143*25000000000000^4119 ≤ 9264262398691^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128888553 2500000000 9264262398691 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3961727963/10000000000 : ℝ)^5143 ≤ (1258859164221/4000000000000 : ℝ)^4119 := by
    have hnat : (3961727963 : ℕ)^5143*4000000000000^4119 ≤ 1258859164221^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3961727963 10000000000 1258859164221 4000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158469087/400000000 : ℝ)^5143 ≤ (6294294257909/20000000000000 : ℝ)^4119 := by
    have hnat : (158469087 : ℕ)^5143*20000000000000^4119 ≤ 6294294257909^4119*400000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158469087 400000000 6294294257909 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1128888553/2500000000 : ℝ), (3961727963/10000000000 : ℝ), (158469087/400000000 : ℝ)] ![(9264262398691/25000000000000 : ℝ), (1258859164221/4000000000000 : ℝ), (6294294257909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1128888553/2500000000 : ℝ)|^5143 ≤ (9264262398691/25000000000000 : ℝ)^4119
        have hw : |(1128888553/2500000000 : ℝ)|=(1128888553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3961727963/10000000000 : ℝ)|^5143 ≤ (1258859164221/4000000000000 : ℝ)^4119
        have hw : |(3961727963/10000000000 : ℝ)|=(3961727963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158469087/400000000 : ℝ)|^5143 ≤ (6294294257909/20000000000000 : ℝ)^4119
        have hw : |(158469087/400000000 : ℝ)|=(158469087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_4 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1843668679/10000000000 : ℝ)*x 0 + (5176186327/10000000000 : ℝ)*x 1 + (1294046529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1843668679/10000000000 : ℝ)^5143 ≤ (6054784439641/50000000000000 : ℝ)^4119 := by
    have hnat : (1843668679 : ℕ)^5143*50000000000000^4119 ≤ 6054784439641^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843668679 10000000000 6054784439641 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176186327/10000000000 : ℝ)^5143 ≤ (21972608335829/50000000000000 : ℝ)^4119 := by
    have hnat : (5176186327 : ℕ)^5143*50000000000000^4119 ≤ 21972608335829^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176186327 10000000000 21972608335829 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294046529/2500000000 : ℝ)^5143 ≤ (5493151804369/12500000000000 : ℝ)^4119 := by
    have hnat : (1294046529 : ℕ)^5143*12500000000000^4119 ≤ 5493151804369^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294046529 2500000000 5493151804369 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1843668679/10000000000 : ℝ), (5176186327/10000000000 : ℝ), (1294046529/2500000000 : ℝ)] ![(6054784439641/50000000000000 : ℝ), (21972608335829/50000000000000 : ℝ), (5493151804369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1843668679/10000000000 : ℝ)|^5143 ≤ (6054784439641/50000000000000 : ℝ)^4119
        have hw : |(-1843668679/10000000000 : ℝ)|=(1843668679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176186327/10000000000 : ℝ)|^5143 ≤ (21972608335829/50000000000000 : ℝ)^4119
        have hw : |(5176186327/10000000000 : ℝ)|=(5176186327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294046529/2500000000 : ℝ)|^5143 ≤ (5493151804369/12500000000000 : ℝ)^4119
        have hw : |(1294046529/2500000000 : ℝ)|=(1294046529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_5 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397698061/10000000000 : ℝ)*x 0 + (-387441643/2500000000 : ℝ)*x 1 + (5176186411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397698061/10000000000 : ℝ)^5143 ≤ (23152855804291/50000000000000 : ℝ)^4119 := by
    have hnat : (5397698061 : ℕ)^5143*50000000000000^4119 ≤ 23152855804291^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397698061 10000000000 23152855804291 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387441643/2500000000 : ℝ)^5143 ≤ (9749070819213/100000000000000 : ℝ)^4119 := by
    have hnat : (387441643 : ℕ)^5143*100000000000000^4119 ≤ 9749070819213^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387441643 2500000000 9749070819213 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176186411/10000000000 : ℝ)^5143 ≤ (439452175621/1000000000000 : ℝ)^4119 := by
    have hnat : (5176186411 : ℕ)^5143*1000000000000^4119 ≤ 439452175621^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176186411 10000000000 439452175621 1000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397698061/10000000000 : ℝ), (-387441643/2500000000 : ℝ), (5176186411/10000000000 : ℝ)] ![(23152855804291/50000000000000 : ℝ), (9749070819213/100000000000000 : ℝ), (439452175621/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397698061/10000000000 : ℝ)|^5143 ≤ (23152855804291/50000000000000 : ℝ)^4119
        have hw : |(5397698061/10000000000 : ℝ)|=(5397698061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387441643/2500000000 : ℝ)|^5143 ≤ (9749070819213/100000000000000 : ℝ)^4119
        have hw : |(-387441643/2500000000 : ℝ)|=(387441643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176186411/10000000000 : ℝ)|^5143 ≤ (439452175621/1000000000000 : ℝ)^4119
        have hw : |(5176186411/10000000000 : ℝ)|=(5176186411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_6 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397698293/10000000000 : ℝ)*x 0 + (2588093109/5000000000 : ℝ)*x 1 + (-309953303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397698293/10000000000 : ℝ)^5143 ≤ (11576428523413/25000000000000 : ℝ)^4119 := by
    have hnat : (5397698293 : ℕ)^5143*25000000000000^4119 ≤ 11576428523413^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397698293 10000000000 11576428523413 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588093109/5000000000 : ℝ)^5143 ≤ (43945215516203/100000000000000 : ℝ)^4119 := by
    have hnat : (2588093109 : ℕ)^5143*100000000000000^4119 ≤ 43945215516203^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588093109 5000000000 43945215516203 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309953303/2000000000 : ℝ)^5143 ≤ (9749070371503/100000000000000 : ℝ)^4119 := by
    have hnat : (309953303 : ℕ)^5143*100000000000000^4119 ≤ 9749070371503^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309953303 2000000000 9749070371503 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397698293/10000000000 : ℝ), (2588093109/5000000000 : ℝ), (-309953303/2000000000 : ℝ)] ![(11576428523413/25000000000000 : ℝ), (43945215516203/100000000000000 : ℝ), (9749070371503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397698293/10000000000 : ℝ)|^5143 ≤ (11576428523413/25000000000000 : ℝ)^4119
        have hw : |(5397698293/10000000000 : ℝ)|=(5397698293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588093109/5000000000 : ℝ)|^5143 ≤ (43945215516203/100000000000000 : ℝ)^4119
        have hw : |(2588093109/5000000000 : ℝ)|=(2588093109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-309953303/2000000000 : ℝ)|^5143 ≤ (9749070371503/100000000000000 : ℝ)^4119
        have hw : |(-309953303/2000000000 : ℝ)|=(309953303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_7 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (746474387/2000000000 : ℝ)*x 0 + (2176228819/5000000000 : ℝ)*x 1 + (1088114331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (746474387/2000000000 : ℝ)^5143 ≤ (7303291728493/25000000000000 : ℝ)^4119 := by
    have hnat : (746474387 : ℕ)^5143*25000000000000^4119 ≤ 7303291728493^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746474387 2000000000 7303291728493 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176228819/5000000000 : ℝ)^5143 ≤ (7078683625857/20000000000000 : ℝ)^4119 := by
    have hnat : (2176228819 : ℕ)^5143*20000000000000^4119 ≤ 7078683625857^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176228819 5000000000 7078683625857 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088114331/2500000000 : ℝ)^5143 ≤ (8848353735277/25000000000000 : ℝ)^4119 := by
    have hnat : (1088114331 : ℕ)^5143*25000000000000^4119 ≤ 8848353735277^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088114331 2500000000 8848353735277 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(746474387/2000000000 : ℝ), (2176228819/5000000000 : ℝ), (1088114331/2500000000 : ℝ)] ![(7303291728493/25000000000000 : ℝ), (7078683625857/20000000000000 : ℝ), (8848353735277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(746474387/2000000000 : ℝ)|^5143 ≤ (7303291728493/25000000000000 : ℝ)^4119
        have hw : |(746474387/2000000000 : ℝ)|=(746474387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2176228819/5000000000 : ℝ)|^5143 ≤ (7078683625857/20000000000000 : ℝ)^4119
        have hw : |(2176228819/5000000000 : ℝ)|=(2176228819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088114331/2500000000 : ℝ)|^5143 ≤ (8848353735277/25000000000000 : ℝ)^4119
        have hw : |(1088114331/2500000000 : ℝ)|=(1088114331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_8 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-847714883/5000000000 : ℝ)*x 0 + (1247838223/2500000000 : ℝ)*x 1 + (683954931/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847714883/5000000000 : ℝ)^5143 ≤ (5453127612799/50000000000000 : ℝ)^4119 := by
    have hnat : (847714883 : ℕ)^5143*50000000000000^4119 ≤ 5453127612799^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847714883 5000000000 5453127612799 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247838223/2500000000 : ℝ)^5143 ≤ (41994665181433/100000000000000 : ℝ)^4119 := by
    have hnat : (1247838223 : ℕ)^5143*100000000000000^4119 ≤ 41994665181433^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247838223 2500000000 41994665181433 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683954931/1250000000 : ℝ)^5143 ≤ (47099079572231/100000000000000 : ℝ)^4119 := by
    have hnat : (683954931 : ℕ)^5143*100000000000000^4119 ≤ 47099079572231^4119*1250000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683954931 1250000000 47099079572231 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-847714883/5000000000 : ℝ), (1247838223/2500000000 : ℝ), (683954931/1250000000 : ℝ)] ![(5453127612799/50000000000000 : ℝ), (41994665181433/100000000000000 : ℝ), (47099079572231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-847714883/5000000000 : ℝ)|^5143 ≤ (5453127612799/50000000000000 : ℝ)^4119
        have hw : |(-847714883/5000000000 : ℝ)|=(847714883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1247838223/2500000000 : ℝ)|^5143 ≤ (41994665181433/100000000000000 : ℝ)^4119
        have hw : |(1247838223/2500000000 : ℝ)|=(1247838223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683954931/1250000000 : ℝ)|^5143 ≤ (47099079572231/100000000000000 : ℝ)^4119
        have hw : |(683954931/1250000000 : ℝ)|=(683954931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_9 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039271529/2000000000 : ℝ)*x 0 + (-710074719/5000000000 : ℝ)*x 1 + (547163703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039271529/2000000000 : ℝ)^5143 ≤ (11039786562229/25000000000000 : ℝ)^4119 := by
    have hnat : (1039271529 : ℕ)^5143*25000000000000^4119 ≤ 11039786562229^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039271529 2000000000 11039786562229 25000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710074719/5000000000 : ℝ)^5143 ≤ (4370900078197/50000000000000 : ℝ)^4119 := by
    have hnat : (710074719 : ℕ)^5143*50000000000000^4119 ≤ 4370900078197^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710074719 5000000000 4370900078197 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547163703/1000000000 : ℝ)^5143 ≤ (23549526792023/50000000000000 : ℝ)^4119 := by
    have hnat : (547163703 : ℕ)^5143*50000000000000^4119 ≤ 23549526792023^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547163703 1000000000 23549526792023 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039271529/2000000000 : ℝ), (-710074719/5000000000 : ℝ), (547163703/1000000000 : ℝ)] ![(11039786562229/25000000000000 : ℝ), (4370900078197/50000000000000 : ℝ), (23549526792023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039271529/2000000000 : ℝ)|^5143 ≤ (11039786562229/25000000000000 : ℝ)^4119
        have hw : |(1039271529/2000000000 : ℝ)|=(1039271529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-710074719/5000000000 : ℝ)|^5143 ≤ (4370900078197/50000000000000 : ℝ)^4119
        have hw : |(-710074719/5000000000 : ℝ)|=(710074719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547163703/1000000000 : ℝ)|^5143 ≤ (23549526792023/50000000000000 : ℝ)^4119
        have hw : |(547163703/1000000000 : ℝ)|=(547163703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_10 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196360027/10000000000 : ℝ)*x 0 + (1367909001/2500000000 : ℝ)*x 1 + (-11094903/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196360027/10000000000 : ℝ)^5143 ≤ (44159171523741/100000000000000 : ℝ)^4119 := by
    have hnat : (5196360027 : ℕ)^5143*100000000000000^4119 ≤ 44159171523741^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196360027 10000000000 44159171523741 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367909001/2500000000 : ℝ)^5143 ≤ (23549521278401/50000000000000 : ℝ)^4119 := by
    have hnat : (1367909001 : ℕ)^5143*50000000000000^4119 ≤ 23549521278401^4119*2500000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367909001 2500000000 23549521278401 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11094903/78125000 : ℝ)^5143 ≤ (4370892953421/50000000000000 : ℝ)^4119 := by
    have hnat : (11094903 : ℕ)^5143*50000000000000^4119 ≤ 4370892953421^4119*78125000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11094903 78125000 4370892953421 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196360027/10000000000 : ℝ), (1367909001/2500000000 : ℝ), (-11094903/78125000 : ℝ)] ![(44159171523741/100000000000000 : ℝ), (23549521278401/50000000000000 : ℝ), (4370892953421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196360027/10000000000 : ℝ)|^5143 ≤ (44159171523741/100000000000000 : ℝ)^4119
        have hw : |(5196360027/10000000000 : ℝ)|=(5196360027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367909001/2500000000 : ℝ)|^5143 ≤ (23549521278401/50000000000000 : ℝ)^4119
        have hw : |(1367909001/2500000000 : ℝ)|=(1367909001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11094903/78125000 : ℝ)|^5143 ≤ (4370892953421/50000000000000 : ℝ)^4119
        have hw : |(-11094903/78125000 : ℝ)|=(11094903/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_11 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2323009031/5000000000 : ℝ)*x 0 + (389395133/1000000000 : ℝ)*x 1 + (389395623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2323009031/5000000000 : ℝ)^5143 ≤ (2399915107881/6250000000000 : ℝ)^4119 := by
    have hnat : (2323009031 : ℕ)^5143*6250000000000^4119 ≤ 2399915107881^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323009031 5000000000 2399915107881 6250000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389395133/1000000000 : ℝ)^5143 ≤ (30800654934581/100000000000000 : ℝ)^4119 := by
    have hnat : (389395133 : ℕ)^5143*100000000000000^4119 ≤ 30800654934581^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389395133 1000000000 30800654934581 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389395623/1000000000 : ℝ)^5143 ≤ (15400351664223/50000000000000 : ℝ)^4119 := by
    have hnat : (389395623 : ℕ)^5143*50000000000000^4119 ≤ 15400351664223^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389395623 1000000000 15400351664223 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2323009031/5000000000 : ℝ), (389395133/1000000000 : ℝ), (389395623/1000000000 : ℝ)] ![(2399915107881/6250000000000 : ℝ), (30800654934581/100000000000000 : ℝ), (15400351664223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2323009031/5000000000 : ℝ)|^5143 ≤ (2399915107881/6250000000000 : ℝ)^4119
        have hw : |(2323009031/5000000000 : ℝ)|=(2323009031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389395133/1000000000 : ℝ)|^5143 ≤ (30800654934581/100000000000000 : ℝ)^4119
        have hw : |(389395133/1000000000 : ℝ)|=(389395133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389395623/1000000000 : ℝ)|^5143 ≤ (15400351664223/50000000000000 : ℝ)^4119
        have hw : |(389395623/1000000000 : ℝ)|=(389395623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_12 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129623357/1000000000 : ℝ)*x 0 + (5603720813/10000000000 : ℝ)*x 1 + (2575440713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129623357/1000000000 : ℝ)^5143 ≤ (7799966694679/100000000000000 : ℝ)^4119 := by
    have hnat : (129623357 : ℕ)^5143*100000000000000^4119 ≤ 7799966694679^4119*1000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129623357 1000000000 7799966694679 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5603720813/10000000000 : ℝ)^5143 ≤ (9704579614069/20000000000000 : ℝ)^4119 := by
    have hnat : (5603720813 : ℕ)^5143*20000000000000^4119 ≤ 9704579614069^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603720813 10000000000 9704579614069 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575440713/5000000000 : ℝ)^5143 ≤ (8735427043731/20000000000000 : ℝ)^4119 := by
    have hnat : (2575440713 : ℕ)^5143*20000000000000^4119 ≤ 8735427043731^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575440713 5000000000 8735427043731 20000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129623357/1000000000 : ℝ), (5603720813/10000000000 : ℝ), (2575440713/5000000000 : ℝ)] ![(7799966694679/100000000000000 : ℝ), (9704579614069/20000000000000 : ℝ), (8735427043731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129623357/1000000000 : ℝ)|^5143 ≤ (7799966694679/100000000000000 : ℝ)^4119
        have hw : |(-129623357/1000000000 : ℝ)|=(129623357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5603720813/10000000000 : ℝ)|^5143 ≤ (9704579614069/20000000000000 : ℝ)^4119
        have hw : |(5603720813/10000000000 : ℝ)|=(5603720813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575440713/5000000000 : ℝ)|^5143 ≤ (8735427043731/20000000000000 : ℝ)^4119
        have hw : |(2575440713/5000000000 : ℝ)|=(2575440713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_13 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707485051/5000000000 : ℝ)*x 0 + (-62412941/400000000 : ℝ)*x 1 + (1030176453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707485051/5000000000 : ℝ)^5143 ≤ (23245397391039/50000000000000 : ℝ)^4119 := by
    have hnat : (2707485051 : ℕ)^5143*50000000000000^4119 ≤ 23245397391039^4119*5000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707485051 5000000000 23245397391039 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62412941/400000000 : ℝ)^5143 ≤ (9832061095571/100000000000000 : ℝ)^4119 := by
    have hnat : (62412941 : ℕ)^5143*100000000000000^4119 ≤ 9832061095571^4119*400000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62412941 400000000 9832061095571 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030176453/2000000000 : ℝ)^5143 ≤ (43677144101647/100000000000000 : ℝ)^4119 := by
    have hnat : (1030176453 : ℕ)^5143*100000000000000^4119 ≤ 43677144101647^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030176453 2000000000 43677144101647 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707485051/5000000000 : ℝ), (-62412941/400000000 : ℝ), (1030176453/2000000000 : ℝ)] ![(23245397391039/50000000000000 : ℝ), (9832061095571/100000000000000 : ℝ), (43677144101647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707485051/5000000000 : ℝ)|^5143 ≤ (23245397391039/50000000000000 : ℝ)^4119
        have hw : |(2707485051/5000000000 : ℝ)|=(2707485051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62412941/400000000 : ℝ)|^5143 ≤ (9832061095571/100000000000000 : ℝ)^4119
        have hw : |(-62412941/400000000 : ℝ)|=(62412941/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030176453/2000000000 : ℝ)|^5143 ≤ (43677144101647/100000000000000 : ℝ)^4119
        have hw : |(1030176453/2000000000 : ℝ)|=(1030176453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_14 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5414971631/10000000000 : ℝ)*x 0 + (25754399/50000000 : ℝ)*x 1 + (-1560324759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414971631/10000000000 : ℝ)^5143 ≤ (46490811172991/100000000000000 : ℝ)^4119 := by
    have hnat : (5414971631 : ℕ)^5143*100000000000000^4119 ≤ 46490811172991^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414971631 10000000000 46490811172991 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25754399/50000000 : ℝ)^5143 ≤ (21838559001613/50000000000000 : ℝ)^4119 := by
    have hnat : (25754399 : ℕ)^5143*50000000000000^4119 ≤ 21838559001613^4119*50000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25754399 50000000 21838559001613 50000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1560324759/10000000000 : ℝ)^5143 ≤ (9832070804467/100000000000000 : ℝ)^4119 := by
    have hnat : (1560324759 : ℕ)^5143*100000000000000^4119 ≤ 9832070804467^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560324759 10000000000 9832070804467 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414971631/10000000000 : ℝ), (25754399/50000000 : ℝ), (-1560324759/10000000000 : ℝ)] ![(46490811172991/100000000000000 : ℝ), (21838559001613/50000000000000 : ℝ), (9832070804467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414971631/10000000000 : ℝ)|^5143 ≤ (46490811172991/100000000000000 : ℝ)^4119
        have hw : |(5414971631/10000000000 : ℝ)|=(5414971631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25754399/50000000 : ℝ)|^5143 ≤ (21838559001613/50000000000000 : ℝ)^4119
        have hw : |(25754399/50000000 : ℝ)|=(25754399/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1560324759/10000000000 : ℝ)|^5143 ≤ (9832070804467/100000000000000 : ℝ)^4119
        have hw : |(-1560324759/10000000000 : ℝ)|=(1560324759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1690_box_15 (p : ℝ) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3650707413/10000000000 : ℝ)*x 0 + (878321961/2000000000 : ℝ)*x 1 + (4391605857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3650707413/10000000000 : ℝ)^5143 ≤ (3552157436919/12500000000000 : ℝ)^4119 := by
    have hnat : (3650707413 : ℕ)^5143*12500000000000^4119 ≤ 3552157436919^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650707413 10000000000 3552157436919 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878321961/2000000000 : ℝ)^5143 ≤ (4473923791233/12500000000000 : ℝ)^4119 := by
    have hnat : (878321961 : ℕ)^5143*12500000000000^4119 ≤ 4473923791233^4119*2000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878321961 2000000000 4473923791233 12500000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391605857/10000000000 : ℝ)^5143 ≤ (35791350154793/100000000000000 : ℝ)^4119 := by
    have hnat : (4391605857 : ℕ)^5143*100000000000000^4119 ≤ 35791350154793^4119*10000000000^5143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391605857 10000000000 35791350154793 100000000000000 5143 4119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5143/1024 : ℝ)) 5143 4119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3650707413/10000000000 : ℝ), (878321961/2000000000 : ℝ), (4391605857/10000000000 : ℝ)] ![(3552157436919/12500000000000 : ℝ), (4473923791233/12500000000000 : ℝ), (35791350154793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3650707413/10000000000 : ℝ)|^5143 ≤ (3552157436919/12500000000000 : ℝ)^4119
        have hw : |(3650707413/10000000000 : ℝ)|=(3650707413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(878321961/2000000000 : ℝ)|^5143 ≤ (4473923791233/12500000000000 : ℝ)^4119
        have hw : |(878321961/2000000000 : ℝ)|=(878321961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4391605857/10000000000 : ℝ)|^5143 ≤ (35791350154793/100000000000000 : ℝ)^4119
        have hw : |(4391605857/10000000000 : ℝ)|=(4391605857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1690_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66573/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5793/10000 : ℝ) ∧ (16161/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22533/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8617/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8617/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8617/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8617/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8617/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8617/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (9831/100000 : ℝ) ^ (5135/1024 : ℝ) ≤ (887629261742251/100000000000000000000 : ℝ) := by
    have hpowers : (9831/100000 : ℝ)^5135 ≤ (887629261742251/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9831 : ℕ)^5135*100000000000000000000^1024 ≤ 887629261742251^1024*100000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9831 100000 887629261742251 100000000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9831/100000 : ℝ)) (X := (887629261742251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8617/50000 : ℝ) ^ (5135/1024 : ℝ) ≤ (463014630337279/3125000000000000000 : ℝ) := by
    have hpowers : (8617/50000 : ℝ)^5135 ≤ (463014630337279/3125000000000000000 : ℝ)^1024 := by
      have hnat : (8617 : ℕ)^5135*3125000000000000000^1024 ≤ 463014630337279^1024*50000^5135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8617 50000 463014630337279 3125000000000000000 5135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8617/50000 : ℝ)) (X := (463014630337279/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000887629261742251/50000000000000000000 : ℝ) ≤ (10000035401203701/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (50000887629261742251/50000000000000000000 : ℝ)^1024 ≤ (10000035401203701/10000000000000000 : ℝ)^5135 := by
      have hnat : (50000887629261742251 : ℕ)^1024*10000000000000000^5135 ≤ 10000035401203701^5135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000887629261742251 50000000000000000000 10000035401203701 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000035401203701/10000000000000000 : ℝ)) (X := (50000887629261742251/50000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015704097432535179/100000000000000000000 : ℝ) ≤ (1250039143098779/1250000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (100015704097432535179/100000000000000000000 : ℝ)^1024 ≤ (1250039143098779/1250000000000000 : ℝ)^5135 := by
      have hnat : (100015704097432535179 : ℕ)^1024*1250000000000000^5135 ≤ 1250039143098779^5135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015704097432535179 100000000000000000000 1250039143098779 1250000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250039143098779/1250000000000000 : ℝ)) (X := (100015704097432535179/100000000000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1562963014630337279/1562500000000000000 : ℝ) ≤ (10000590888376763/10000000000000000 : ℝ) ^ (5135/1024 : ℝ) := by
    have hpowers : (1562963014630337279/1562500000000000000 : ℝ)^1024 ≤ (10000590888376763/10000000000000000 : ℝ)^5135 := by
      have hnat : (1562963014630337279 : ℕ)^1024*10000000000000000^5135 ≤ 10000590888376763^5135*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562963014630337279 1562500000000000000 10000590888376763 10000000000000000 1024 5135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000590888376763/10000000000000000 : ℝ)) (X := (1562963014630337279/1562500000000000000 : ℝ)) (by norm_num) 5135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(887629261742251/100000000000000000000 : ℝ) ≤ ((74024801080712625981/74030000000000000000 : ℝ)+2*(277743586531/740300000000000 : ℝ)*(9831/100000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (74024801080712625981/74030000000000000000 : ℝ)+2*(277743586531/740300000000000 : ℝ)*(9831/100000 : ℝ)=(10000035401203701/10000000000000000 : ℝ) by norm_num, show 1+2*(887629261742251/100000000000000000000 : ℝ)=(50000887629261742251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(463014630337279/3125000000000000000 : ℝ)+(887629261742251/100000000000000000000 : ℝ) ≤ ((74024801080712625981/74030000000000000000 : ℝ)+(277743586531/740300000000000 : ℝ)*((8617/50000 : ℝ)+(9831/100000 : ℝ)))^(5135/1024 : ℝ) := by
    rw [show (74024801080712625981/74030000000000000000 : ℝ)+(277743586531/740300000000000 : ℝ)*((8617/50000 : ℝ)+(9831/100000 : ℝ))=(1250039143098779/1250000000000000 : ℝ) by norm_num, show 1+(463014630337279/3125000000000000000 : ℝ)+(887629261742251/100000000000000000000 : ℝ)=(100015704097432535179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(463014630337279/3125000000000000000 : ℝ) ≤ ((74024801080712625981/74030000000000000000 : ℝ)+2*(277743586531/740300000000000 : ℝ)*(8617/50000 : ℝ))^(5135/1024 : ℝ) := by
    rw [show (74024801080712625981/74030000000000000000 : ℝ)+2*(277743586531/740300000000000 : ℝ)*(8617/50000 : ℝ)=(10000590888376763/10000000000000000 : ℝ) by norm_num, show 1+2*(463014630337279/3125000000000000000 : ℝ)=(1562963014630337279/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74024801080712625981/74030000000000000000 : ℝ)*(X 1 0+X 2 0)+(277743586531/740300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (8617/50000 : ℝ)) (c := (74024801080712625981/74030000000000000000 : ℝ)) (alpha := (277743586531/740300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74024801080712625981/74030000000000000000 : ℝ)*(X 0 1+X 2 1)+(277743586531/740300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (8617/50000 : ℝ)) (c := (74024801080712625981/74030000000000000000 : ℝ)) (alpha := (277743586531/740300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74024801080712625981/74030000000000000000 : ℝ)*(X 0 2+X 1 2)+(277743586531/740300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5135/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (8617/50000 : ℝ)) (c := (74024801080712625981/74030000000000000000 : ℝ)) (alpha := (277743586531/740300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1152807291/10000000000 : ℝ)*X 0 0+(2714031803/5000000000 : ℝ)*X 0 1+(2714031531/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1045208377/2000000000 : ℝ)*X 1 0+(-719988957/5000000000 : ℝ)*X 1 1+(2714031629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226041607/10000000000 : ℝ)*X 2 0+(5428063347/10000000000 : ℝ)*X 2 1+(-719989087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1128888553/2500000000 : ℝ)*X 0 0+(3961727963/10000000000 : ℝ)*X 0 1+(158469087/400000000 : ℝ)*X 0 2+(1128888553/2500000000 : ℝ)*X 1 0+(3961727963/10000000000 : ℝ)*X 1 1+(158469087/400000000 : ℝ)*X 1 2+(1128888553/2500000000 : ℝ)*X 2 0+(3961727963/10000000000 : ℝ)*X 2 1+(158469087/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1843668679/10000000000 : ℝ)*X 0 0+(5176186327/10000000000 : ℝ)*X 0 1+(1294046529/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5397698061/10000000000 : ℝ)*X 1 0+(-387441643/2500000000 : ℝ)*X 1 1+(5176186411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5397698293/10000000000 : ℝ)*X 2 0+(2588093109/5000000000 : ℝ)*X 2 1+(-309953303/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((746474387/2000000000 : ℝ)*X 0 0+(2176228819/5000000000 : ℝ)*X 0 1+(1088114331/2500000000 : ℝ)*X 0 2+(746474387/2000000000 : ℝ)*X 1 0+(2176228819/5000000000 : ℝ)*X 1 1+(1088114331/2500000000 : ℝ)*X 1 2+(746474387/2000000000 : ℝ)*X 2 0+(2176228819/5000000000 : ℝ)*X 2 1+(1088114331/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-847714883/5000000000 : ℝ)*X 0 0+(1247838223/2500000000 : ℝ)*X 0 1+(683954931/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1039271529/2000000000 : ℝ)*X 1 0+(-710074719/5000000000 : ℝ)*X 1 1+(547163703/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196360027/10000000000 : ℝ)*X 2 0+(1367909001/2500000000 : ℝ)*X 2 1+(-11094903/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2323009031/5000000000 : ℝ)*X 0 0+(389395133/1000000000 : ℝ)*X 0 1+(389395623/1000000000 : ℝ)*X 0 2+(2323009031/5000000000 : ℝ)*X 1 0+(389395133/1000000000 : ℝ)*X 1 1+(389395623/1000000000 : ℝ)*X 1 2+(2323009031/5000000000 : ℝ)*X 2 0+(389395133/1000000000 : ℝ)*X 2 1+(389395623/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-129623357/1000000000 : ℝ)*X 0 0+(5603720813/10000000000 : ℝ)*X 0 1+(2575440713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2707485051/5000000000 : ℝ)*X 1 0+(-62412941/400000000 : ℝ)*X 1 1+(1030176453/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5414971631/10000000000 : ℝ)*X 2 0+(25754399/50000000 : ℝ)*X 2 1+(-1560324759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3650707413/10000000000 : ℝ)*X 0 0+(878321961/2000000000 : ℝ)*X 0 1+(4391605857/10000000000 : ℝ)*X 0 2+(3650707413/10000000000 : ℝ)*X 1 0+(878321961/2000000000 : ℝ)*X 1 1+(4391605857/10000000000 : ℝ)*X 1 2+(3650707413/10000000000 : ℝ)*X 2 0+(878321961/2000000000 : ℝ)*X 2 1+(4391605857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1690_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66573/100000 : ℝ) ≤ (-1232046078518615043665031618368907/1850750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3919893/100000000000000 : ℝ)*(lower0) + (52560977/100000000000000 : ℝ)*(lower2) + (1865179/10000000000000 : ℝ)*(lower4) + (1305542426657949/100000000000000 : ℝ)*(major0) + (1305542426657949/100000000000000 : ℝ)*(major1) + (1305542426657949/100000000000000 : ℝ)*(major2) + (1940186077270041/100000000000000 : ℝ)*(sp4) + (121261305449959/6250000000000 : ℝ)*(sp5) + (1940187315609583/100000000000000 : ℝ)*(sp6) + (138616143317571/20000000000000 : ℝ)*(sp7) + (1374948433/100000000000000 : ℝ)*(sp8) + (656501913/10000000000000 : ℝ)*(sp13) + (136608891/100000000000000 : ℝ)*(sp14) + (268679689/4000000000000 : ℝ)*(sp15) + (8663592919751/1250000000000 : ℝ)*(f.failure) + (970093726109237/50000000000000 : ℝ)*(f.sum) + (44635375062411/2313437500000000000000000000 : ℝ)*base66 + (11341949499975472969/7403000000000000000000000000000000 : ℝ)*base67 + (12633052488194472969/7403000000000000000000000000000000 : ℝ)*base69 + (28637309404567472969/7403000000000000000000000000000000 : ℝ)*base71 + (13558980365759/9253750000000000000000000000 : ℝ)*base74 + (12721088268312472969/7403000000000000000000000000000000 : ℝ)*base75 + (199993905855220527031/7403000000000000000000000000000000 : ℝ)*base78 + (27411780398822472969/7403000000000000000000000000000000 : ℝ)*base79 + (17463074253523/18507500000000000000000000000 : ℝ)*base82 + (6511/25000000000000000000 : ℝ)*base90 + (6511/25000000000000000000 : ℝ)*base92 + (6511/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5793/10000 : ℝ) ≤ (53609325758676941672861974418199/92537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21672911/100000000000000 : ℝ)*(upper2) + (112119643/100000000000000 : ℝ)*(upper3) + (11632953/50000000000000 : ℝ)*(lower5) + (70229041413407/5000000000000 : ℝ)*(major0) + (70229041413407/5000000000000 : ℝ)*(major1) + (70229041413407/5000000000000 : ℝ)*(major2) + (1022092797878229/50000000000000 : ℝ)*(sp0) + (1022084529871067/50000000000000 : ℝ)*(sp1) + (1022090451220953/50000000000000 : ℝ)*(sp2) + (745659883639391/100000000000000 : ℝ)*(sp3) + (192146739/100000000000000 : ℝ)*(sp8) + (16728161063/100000000000000 : ℝ)*(sp9) + (4885461291/100000000000000 : ℝ)*(sp10) + (5137766461/100000000000000 : ℝ)*(sp11) + (745665021405853/100000000000000 : ℝ)*(f.failure) + (2044185787903197/100000000000000 : ℝ)*(f.sum) + (21758160368151/3701500000000000000000000000 : ℝ)*base65 + (3285451480211777267/370150000000000000000000000000000 : ℝ)*base67 + (350366849353177267/370150000000000000000000000000000 : ℝ)*base69 + (678624835866777267/370150000000000000000000000000000 : ℝ)*base71 + (118987259378489/7403000000000000000000000000 : ℝ)*base73 + (313292257424077267/370150000000000000000000000000000 : ℝ)*base75 + (1207962072700677267/370150000000000000000000000000000 : ℝ)*base77 + (280593537559722733/370150000000000000000000000000000 : ℝ)*base80 + (33454113203067/7403000000000000000000000000 : ℝ)*base81 + (16067867/2000000000000000000000 : ℝ)*base89 + (16067867/2000000000000000000000 : ℝ)*base91 + (16067867/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (16161/20000 : ℝ) ≤ (747771185862896200763475026465091/925375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63431379/100000000000000 : ℝ)*(upper0) + (5208549/100000000000000 : ℝ)*(lower1) + (434951797/50000000000000 : ℝ)*(lower3) + (28477029/12500000000000 : ℝ)*(upper4) + (717792853028437/50000000000000 : ℝ)*(major0) + (717792853028437/50000000000000 : ℝ)*(major1) + (717792853028437/50000000000000 : ℝ)*(major2) + (7427933639/100000000000000 : ℝ)*(sp0) + (9033161661/10000000000000 : ℝ)*(sp1) + (30625931853/50000000000000 : ℝ)*(sp3) + (104105163917707/5000000000000 : ℝ)*(sp8) + (2082020374671169/100000000000000 : ℝ)*(sp9) + (1041055353143889/50000000000000 : ℝ)*(sp10) + (152412732895289/20000000000000 : ℝ)*(sp11) + (15242498326803/2000000000000 : ℝ)*(f.failure) + (1041055353143889/50000000000000 : ℝ)*(f.sum) + (189687154628001/37015000000000000000000000000 : ℝ)*base66 + (15748203630220278303/3701500000000000000000000000000000 : ℝ)*base68 + (54350489729014278303/3701500000000000000000000000000000 : ℝ)*base70 + (65403745715132778303/3701500000000000000000000000000000 : ℝ)*base72 + (53373368324901/9253750000000000000000000000 : ℝ)*base73 + (50930474412582278303/3701500000000000000000000000000000 : ℝ)*base76 + (28914000228559278303/3701500000000000000000000000000000 : ℝ)*base78 + (6602400961182721697/3701500000000000000000000000000000 : ℝ)*base79 + (121566528340063/18507500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (75083/40000000000000000000 : ℝ)*base90 + (75083/40000000000000000000 : ℝ)*base92 + (75083/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-22533/25000 : ℝ) ≤ (-2369416473920088263620292657061/2628906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (8408179/6250000000000 : ℝ)*(upper1) + (11518873/20000000000000 : ℝ)*(lower2) + (154831851/50000000000000 : ℝ)*(upper3) + (32122671/100000000000000 : ℝ)*(upper5) + (46334088960379/3125000000000 : ℝ)*(major0) + (46334088960379/3125000000000 : ℝ)*(major1) + (46334088960379/3125000000000 : ℝ)*(major2) + (4008315691/100000000000000 : ℝ)*(sp4) + (162130553931/100000000000000 : ℝ)*(sp6) + (269475949/1000000000000 : ℝ)*(sp7) + (2208288674330629/100000000000000 : ℝ)*(sp12) + (27603658533079/1250000000000 : ℝ)*(sp13) + (2208130552092389/100000000000000 : ℝ)*(sp14) + (78710518443767/10000000000000 : ℝ)*(sp15) + (78713213203257/10000000000000 : ℝ)*(f.failure) + (27603658533079/1250000000000 : ℝ)*(f.sum) + (15022183520127/3365000000000000000000000000 : ℝ)*base66 + (63963081642315291/21031250000000000000000000000000 : ℝ)*base68 + (115760632135065291/21031250000000000000000000000000 : ℝ)*base70 + (118433282333502791/21031250000000000000000000000000 : ℝ)*base72 + (7314072791831/1682500000000000000000000000 : ℝ)*base74 + (5501605490377791/21031250000000000000000000000000 : ℝ)*base76 + (193910896963065291/21031250000000000000000000000000 : ℝ)*base78 + (63065611409565291/21031250000000000000000000000000 : ℝ)*base80 + (4232369658461/1682500000000000000000000000 : ℝ)*base82 + (539423/200000000000000000000 : ℝ)*base89 + (539423/200000000000000000000 : ℝ)*base91 + (539423/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1690_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8617/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66573/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5793/10000 : ℝ) else (16161/20000 : ℝ) ≤ X j i ∧ X j i ≤ (22533/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1690_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1690_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66573/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5793/10000 : ℝ) else (16161/20000 : ℝ) ≤ X j i ∧ X j i ≤ (22533/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1690_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1690_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1690_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66573/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5793/10000 : ℝ) else (16161/20000 : ℝ) ≤ X j i ∧ X j i ≤ (22533/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1690_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
