-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1626_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:08.13123+00:00
-- url     : https://prove2.me/submissions/8d24f9ea-36e2-4c86-b41c-ebf2b3948542

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
theorem support_rectangle_w1626_s0_0 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1535720731/10000000000 : ℝ)*x 0 + (5815837089/10000000000 : ℝ)*x 1 + (4904766157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1535720731/10000000000 : ℝ)^4823 ≤ (579251424549/6250000000000 : ℝ)^3799 := by
    have hnat : (1535720731 : ℕ)^4823*6250000000000^3799 ≤ 579251424549^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535720731 10000000000 579251424549 6250000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5815837089/10000000000 : ℝ)^4823 ≤ (50253316334779/100000000000000 : ℝ)^3799 := by
    have hnat : (5815837089 : ℕ)^4823*100000000000000^3799 ≤ 50253316334779^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5815837089 10000000000 50253316334779 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4904766157/10000000000 : ℝ)^4823 ≤ (8095732170691/20000000000000 : ℝ)^3799 := by
    have hnat : (4904766157 : ℕ)^4823*20000000000000^3799 ≤ 8095732170691^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904766157 10000000000 8095732170691 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1535720731/10000000000 : ℝ), (5815837089/10000000000 : ℝ), (4904766157/10000000000 : ℝ)] ![(579251424549/6250000000000 : ℝ), (50253316334779/100000000000000 : ℝ), (8095732170691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1535720731/10000000000 : ℝ)|^4823 ≤ (579251424549/6250000000000 : ℝ)^3799
        have hw : |(-1535720731/10000000000 : ℝ)|=(1535720731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5815837089/10000000000 : ℝ)|^4823 ≤ (50253316334779/100000000000000 : ℝ)^3799
        have hw : |(5815837089/10000000000 : ℝ)|=(5815837089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4904766157/10000000000 : ℝ)|^4823 ≤ (8095732170691/20000000000000 : ℝ)^3799
        have hw : |(4904766157/10000000000 : ℝ)|=(4904766157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_1 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5447169961/10000000000 : ℝ)*x 0 + (-20383713/100000000 : ℝ)*x 1 + (4904767203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5447169961/10000000000 : ℝ)^4823 ≤ (46244194546141/100000000000000 : ℝ)^3799 := by
    have hnat : (5447169961 : ℕ)^4823*100000000000000^3799 ≤ 46244194546141^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447169961 10000000000 46244194546141 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20383713/100000000 : ℝ)^4823 ≤ (6638566816707/50000000000000 : ℝ)^3799 := by
    have hnat : (20383713 : ℕ)^4823*50000000000000^3799 ≤ 6638566816707^3799*100000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20383713 100000000 6638566816707 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4904767203/10000000000 : ℝ)^4823 ≤ (40478671812873/100000000000000 : ℝ)^3799 := by
    have hnat : (4904767203 : ℕ)^4823*100000000000000^3799 ≤ 40478671812873^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904767203 10000000000 40478671812873 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5447169961/10000000000 : ℝ), (-20383713/100000000 : ℝ), (4904767203/10000000000 : ℝ)] ![(46244194546141/100000000000000 : ℝ), (6638566816707/50000000000000 : ℝ), (40478671812873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5447169961/10000000000 : ℝ)|^4823 ≤ (46244194546141/100000000000000 : ℝ)^3799
        have hw : |(5447169961/10000000000 : ℝ)|=(5447169961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20383713/100000000 : ℝ)|^4823 ≤ (6638566816707/50000000000000 : ℝ)^3799
        have hw : |(-20383713/100000000 : ℝ)|=(20383713/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4904767203/10000000000 : ℝ)|^4823 ≤ (40478671812873/100000000000000 : ℝ)^3799
        have hw : |(4904767203/10000000000 : ℝ)|=(4904767203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_2 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1361792449/2500000000 : ℝ)*x 0 + (980953323/2000000000 : ℝ)*x 1 + (-2038372259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1361792449/2500000000 : ℝ)^4823 ≤ (46244192767787/100000000000000 : ℝ)^3799 := by
    have hnat : (1361792449 : ℕ)^4823*100000000000000^3799 ≤ 46244192767787^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361792449 2500000000 46244192767787 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980953323/2000000000 : ℝ)^4823 ≤ (4047866565213/10000000000000 : ℝ)^3799 := by
    have hnat : (980953323 : ℕ)^4823*10000000000000^3799 ≤ 4047866565213^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980953323 2000000000 4047866565213 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038372259/10000000000 : ℝ)^4823 ≤ (6638570781839/50000000000000 : ℝ)^3799 := by
    have hnat : (2038372259 : ℕ)^4823*50000000000000^3799 ≤ 6638570781839^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038372259 10000000000 6638570781839 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1361792449/2500000000 : ℝ), (980953323/2000000000 : ℝ), (-2038372259/10000000000 : ℝ)] ![(46244192767787/100000000000000 : ℝ), (4047866565213/10000000000000 : ℝ), (6638570781839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1361792449/2500000000 : ℝ)|^4823 ≤ (46244192767787/100000000000000 : ℝ)^3799
        have hw : |(1361792449/2500000000 : ℝ)|=(1361792449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(980953323/2000000000 : ℝ)|^4823 ≤ (4047866565213/10000000000000 : ℝ)^3799
        have hw : |(980953323/2000000000 : ℝ)|=(980953323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038372259/10000000000 : ℝ)|^4823 ≤ (6638570781839/50000000000000 : ℝ)^3799
        have hw : |(-2038372259/10000000000 : ℝ)|=(2038372259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_3 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102004387/10000000000 : ℝ)*x 0 + (1538601401/5000000000 : ℝ)*x 1 + (5363256067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102004387/10000000000 : ℝ)^4823 ≤ (32261258720477/100000000000000 : ℝ)^3799 := by
    have hnat : (4102004387 : ℕ)^4823*100000000000000^3799 ≤ 32261258720477^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102004387 10000000000 32261258720477 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1538601401/5000000000 : ℝ)^4823 ≤ (22397077687203/100000000000000 : ℝ)^3799 := by
    have hnat : (1538601401 : ℕ)^4823*100000000000000^3799 ≤ 22397077687203^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538601401 5000000000 22397077687203 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5363256067/10000000000 : ℝ)^4823 ≤ (22670831784687/50000000000000 : ℝ)^3799 := by
    have hnat : (5363256067 : ℕ)^4823*50000000000000^3799 ≤ 22670831784687^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363256067 10000000000 22670831784687 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102004387/10000000000 : ℝ), (1538601401/5000000000 : ℝ), (5363256067/10000000000 : ℝ)] ![(32261258720477/100000000000000 : ℝ), (22397077687203/100000000000000 : ℝ), (22670831784687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102004387/10000000000 : ℝ)|^4823 ≤ (32261258720477/100000000000000 : ℝ)^3799
        have hw : |(4102004387/10000000000 : ℝ)|=(4102004387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1538601401/5000000000 : ℝ)|^4823 ≤ (22397077687203/100000000000000 : ℝ)^3799
        have hw : |(1538601401/5000000000 : ℝ)|=(1538601401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5363256067/10000000000 : ℝ)|^4823 ≤ (22670831784687/50000000000000 : ℝ)^3799
        have hw : |(5363256067/10000000000 : ℝ)|=(5363256067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_4 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-307660817/2000000000 : ℝ)*x 0 + (2463824537/5000000000 : ℝ)*x 1 + (724018731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307660817/2000000000 : ℝ)^4823 ≤ (9287820055419/100000000000000 : ℝ)^3799 := by
    have hnat : (307660817 : ℕ)^4823*100000000000000^3799 ≤ 9287820055419^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307660817 2000000000 9287820055419 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463824537/5000000000 : ℝ)^4823 ≤ (814371323273/2000000000000 : ℝ)^3799 := by
    have hnat : (2463824537 : ℕ)^4823*2000000000000^3799 ≤ 814371323273^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463824537 5000000000 814371323273 2000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (724018731/1250000000 : ℝ)^4823 ≤ (49993613763511/100000000000000 : ℝ)^3799 := by
    have hnat : (724018731 : ℕ)^4823*100000000000000^3799 ≤ 49993613763511^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724018731 1250000000 49993613763511 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307660817/2000000000 : ℝ), (2463824537/5000000000 : ℝ), (724018731/1250000000 : ℝ)] ![(9287820055419/100000000000000 : ℝ), (814371323273/2000000000000 : ℝ), (49993613763511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307660817/2000000000 : ℝ)|^4823 ≤ (9287820055419/100000000000000 : ℝ)^3799
        have hw : |(-307660817/2000000000 : ℝ)|=(307660817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463824537/5000000000 : ℝ)|^4823 ≤ (814371323273/2000000000000 : ℝ)^3799
        have hw : |(2463824537/5000000000 : ℝ)|=(2463824537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(724018731/1250000000 : ℝ)|^4823 ≤ (49993613763511/100000000000000 : ℝ)^3799
        have hw : |(724018731/1250000000 : ℝ)|=(724018731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_5 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299600579/2500000000 : ℝ)*x 0 + (-287747099/2500000000 : ℝ)*x 1 + (362009369/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299600579/2500000000 : ℝ)^4823 ≤ (10894922713827/25000000000000 : ℝ)^3799 := by
    have hnat : (1299600579 : ℕ)^4823*25000000000000^3799 ≤ 10894922713827^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299600579 2500000000 10894922713827 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287747099/2500000000 : ℝ)^4823 ≤ (1606673687849/25000000000000 : ℝ)^3799 := by
    have hnat : (287747099 : ℕ)^4823*25000000000000^3799 ≤ 1606673687849^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287747099 2500000000 1606673687849 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362009369/625000000 : ℝ)^4823 ≤ (49993614377147/100000000000000 : ℝ)^3799 := by
    have hnat : (362009369 : ℕ)^4823*100000000000000^3799 ≤ 49993614377147^3799*625000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362009369 625000000 49993614377147 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299600579/2500000000 : ℝ), (-287747099/2500000000 : ℝ), (362009369/625000000 : ℝ)] ![(10894922713827/25000000000000 : ℝ), (1606673687849/25000000000000 : ℝ), (49993614377147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299600579/2500000000 : ℝ)|^4823 ≤ (10894922713827/25000000000000 : ℝ)^3799
        have hw : |(1299600579/2500000000 : ℝ)|=(1299600579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287747099/2500000000 : ℝ)|^4823 ≤ (1606673687849/25000000000000 : ℝ)^3799
        have hw : |(-287747099/2500000000 : ℝ)|=(287747099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362009369/625000000 : ℝ)|^4823 ≤ (49993614377147/100000000000000 : ℝ)^3799
        have hw : |(362009369/625000000 : ℝ)|=(362009369/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_6 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162450079/312500000 : ℝ)*x 0 + (5792149669/10000000000 : ℝ)*x 1 + (-575494221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162450079/312500000 : ℝ)^4823 ≤ (8715938622323/20000000000000 : ℝ)^3799 := by
    have hnat : (162450079 : ℕ)^4823*20000000000000^3799 ≤ 8715938622323^3799*312500000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162450079 312500000 8715938622323 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5792149669/10000000000 : ℝ)^4823 ≤ (12498402950517/25000000000000 : ℝ)^3799 := by
    have hnat : (5792149669 : ℕ)^4823*25000000000000^3799 ≤ 12498402950517^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5792149669 10000000000 12498402950517 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575494221/5000000000 : ℝ)^4823 ≤ (3213347538737/50000000000000 : ℝ)^3799 := by
    have hnat : (575494221 : ℕ)^4823*50000000000000^3799 ≤ 3213347538737^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575494221 5000000000 3213347538737 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162450079/312500000 : ℝ), (5792149669/10000000000 : ℝ), (-575494221/5000000000 : ℝ)] ![(8715938622323/20000000000000 : ℝ), (12498402950517/25000000000000 : ℝ), (3213347538737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162450079/312500000 : ℝ)|^4823 ≤ (8715938622323/20000000000000 : ℝ)^3799
        have hw : |(162450079/312500000 : ℝ)|=(162450079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5792149669/10000000000 : ℝ)|^4823 ≤ (12498402950517/25000000000000 : ℝ)^3799
        have hw : |(5792149669/10000000000 : ℝ)|=(5792149669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-575494221/5000000000 : ℝ)|^4823 ≤ (3213347538737/50000000000000 : ℝ)^3799
        have hw : |(-575494221/5000000000 : ℝ)|=(575494221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s0_7 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (821697753/2000000000 : ℝ)*x 0 + (1326459037/2500000000 : ℝ)*x 1 + (196039969/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821697753/2000000000 : ℝ)^4823 ≤ (32326016799693/100000000000000 : ℝ)^3799 := by
    have hnat : (821697753 : ℕ)^4823*100000000000000^3799 ≤ 32326016799693^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821697753 2000000000 32326016799693 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326459037/2500000000 : ℝ)^4823 ≤ (44726273159473/100000000000000 : ℝ)^3799 := by
    have hnat : (1326459037 : ℕ)^4823*100000000000000^3799 ≤ 44726273159473^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326459037 2500000000 44726273159473 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196039969/625000000 : ℝ)^4823 ≤ (1147385501341/5000000000000 : ℝ)^3799 := by
    have hnat : (196039969 : ℕ)^4823*5000000000000^3799 ≤ 1147385501341^3799*625000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196039969 625000000 1147385501341 5000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821697753/2000000000 : ℝ), (1326459037/2500000000 : ℝ), (196039969/625000000 : ℝ)] ![(32326016799693/100000000000000 : ℝ), (44726273159473/100000000000000 : ℝ), (1147385501341/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821697753/2000000000 : ℝ)|^4823 ≤ (32326016799693/100000000000000 : ℝ)^3799
        have hw : |(821697753/2000000000 : ℝ)|=(821697753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1326459037/2500000000 : ℝ)|^4823 ≤ (44726273159473/100000000000000 : ℝ)^3799
        have hw : |(1326459037/2500000000 : ℝ)|=(1326459037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196039969/625000000 : ℝ)|^4823 ≤ (1147385501341/5000000000000 : ℝ)^3799
        have hw : |(196039969/625000000 : ℝ)|=(196039969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1626_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23879/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4819/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4819 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4819*1^1024 ≤ 0^1024*1^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4819/1024 : ℝ) ≤ (335129428185025201/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4819 ≤ (335129428185025201/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4819*25000000000000000000^1024 ≤ 335129428185025201^1024*5^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 335129428185025201 25000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (335129428185025201/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4819 := by
      have hnat : (1 : ℕ)^1024*1^4819 ≤ 1^4819*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25335129428185025201/25000000000000000000 : ℝ) ≤ (10028335794741331/10000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (25335129428185025201/25000000000000000000 : ℝ)^1024 ≤ (10028335794741331/10000000000000000 : ℝ)^4819 := by
      have hnat : (25335129428185025201 : ℕ)^1024*10000000000000000^4819 ≤ 10028335794741331^4819*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25335129428185025201 25000000000000000000 10028335794741331 10000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028335794741331/10000000000000000 : ℝ)) (X := (25335129428185025201/25000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12835129428185025201/12500000000000000000 : ℝ) ≤ (5028335794741331/5000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (12835129428185025201/12500000000000000000 : ℝ)^1024 ≤ (5028335794741331/5000000000000000 : ℝ)^4819 := by
      have hnat : (12835129428185025201 : ℕ)^1024*5000000000000000^4819 ≤ 5028335794741331^4819*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12835129428185025201 12500000000000000000 5028335794741331 5000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028335794741331/5000000000000000 : ℝ)) (X := (12835129428185025201/12500000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28335794741331/4000000000000000 : ℝ)*(0 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28335794741331/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(335129428185025201/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28335794741331/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4819/1024 : ℝ) := by
    rw [show (1 : ℝ)+(28335794741331/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10028335794741331/10000000000000000 : ℝ) by norm_num, show 1+(335129428185025201/25000000000000000000 : ℝ)+(0 : ℝ)=(25335129428185025201/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(335129428185025201/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28335794741331/4000000000000000 : ℝ)*(2/5 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28335794741331/4000000000000000 : ℝ)*(2/5 : ℝ)=(5028335794741331/5000000000000000 : ℝ) by norm_num, show 1+2*(335129428185025201/25000000000000000000 : ℝ)=(12835129428185025201/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28335794741331/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28335794741331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28335794741331/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28335794741331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28335794741331/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28335794741331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1535720731/10000000000 : ℝ)*X 0 0+(5815837089/10000000000 : ℝ)*X 0 1+(4904766157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5447169961/10000000000 : ℝ)*X 1 0+(-20383713/100000000 : ℝ)*X 1 1+(4904767203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1361792449/2500000000 : ℝ)*X 2 0+(980953323/2000000000 : ℝ)*X 2 1+(-2038372259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4102004387/10000000000 : ℝ)*X 0 0+(1538601401/5000000000 : ℝ)*X 0 1+(5363256067/10000000000 : ℝ)*X 0 2+(4102004387/10000000000 : ℝ)*X 1 0+(1538601401/5000000000 : ℝ)*X 1 1+(5363256067/10000000000 : ℝ)*X 1 2+(4102004387/10000000000 : ℝ)*X 2 0+(1538601401/5000000000 : ℝ)*X 2 1+(5363256067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-307660817/2000000000 : ℝ)*X 0 0+(2463824537/5000000000 : ℝ)*X 0 1+(724018731/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299600579/2500000000 : ℝ)*X 1 0+(-287747099/2500000000 : ℝ)*X 1 1+(362009369/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((162450079/312500000 : ℝ)*X 2 0+(5792149669/10000000000 : ℝ)*X 2 1+(-575494221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((821697753/2000000000 : ℝ)*X 0 0+(1326459037/2500000000 : ℝ)*X 0 1+(196039969/625000000 : ℝ)*X 0 2+(821697753/2000000000 : ℝ)*X 1 0+(1326459037/2500000000 : ℝ)*X 1 1+(196039969/625000000 : ℝ)*X 1 2+(821697753/2000000000 : ℝ)*X 2 0+(1326459037/2500000000 : ℝ)*X 2 1+(196039969/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107415277845560106122631/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (371349/1000000000000 : ℝ)*(base16) + (129321633/50000000000000 : ℝ)*(base19) + (74074961/20000000000000 : ℝ)*(base23) + (58744671/100000000000000 : ℝ)*(upper2) + (54845417/50000000000000 : ℝ)*(upper3) + (383762631990767/50000000000000 : ℝ)*(major0) + (383762631990767/50000000000000 : ℝ)*(major1) + (383762631990767/50000000000000 : ℝ)*(major2) + (1097611968643421/100000000000000 : ℝ)*(sp0) + (1097613010398051/100000000000000 : ℝ)*(sp1) + (274403233950353/25000000000000 : ℝ)*(sp2) + (43743598456397/10000000000000 : ℝ)*(sp3) + (334383199/25000000000000 : ℝ)*(sp4) + (116561269/10000000000000 : ℝ)*(sp7) + (437437150176659/100000000000000 : ℝ)*(f.failure) + (1097613306176217/100000000000000 : ℝ)*(f.sum) + (24967162390877/100000000000000000000000000000 : ℝ)*base65 + (465336541309123/200000000000000000000000000000 : ℝ)*base68 + (248195625709123/200000000000000000000000000000 : ℝ)*base70 + (421608295090877/200000000000000000000000000000 : ℝ)*base71 + (47392230709123/100000000000000000000000000000 : ℝ)*base74 + (438596275309123/200000000000000000000000000000 : ℝ)*base76 + (466472893109123/200000000000000000000000000000 : ℝ)*base78 + (69505857290877/200000000000000000000000000000 : ℝ)*base79 + (92247858909123/100000000000000000000000000000 : ℝ)*base82 + (2843851/312500000000000000000 : ℝ)*base90 + (2843851/312500000000000000000 : ℝ)*base92 + (2843851/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92522016044999806204767/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (479624797/100000000000000 : ℝ)*(base19) + (529417343/100000000000000 : ℝ)*(base23) + (19106607/20000000000000 : ℝ)*(base32) + (80035677/100000000000000 : ℝ)*(upper3) + (10829097/20000000000000 : ℝ)*(upper5) + (404434191914227/50000000000000 : ℝ)*(major0) + (404434191914227/50000000000000 : ℝ)*(major1) + (404434191914227/50000000000000 : ℝ)*(major2) + (722692549/50000000000000 : ℝ)*(sp1) + (60004461/4000000000000 : ℝ)*(sp2) + (578368395986733/50000000000000 : ℝ)*(sp4) + (289183716740893/25000000000000 : ℝ)*(sp5) + (578367381222299/50000000000000 : ℝ)*(sp6) + (92199963693811/20000000000000 : ℝ)*(sp7) + (460999914002091/100000000000000 : ℝ)*(f.failure) + (578368395986733/50000000000000 : ℝ)*(f.sum) + (205041357316137/100000000000000000000000000000 : ℝ)*base65 + (1124693079016137/200000000000000000000000000000 : ℝ)*base67 + (2520570826216137/200000000000000000000000000000 : ℝ)*base69 + (717319002816137/200000000000000000000000000000 : ℝ)*base71 + (235786981016137/100000000000000000000000000000 : ℝ)*base73 + (121629863416137/200000000000000000000000000000 : ℝ)*base75 + (1749405260016137/200000000000000000000000000000 : ℝ)*base77 + (1491531988416137/200000000000000000000000000000 : ℝ)*base79 + (527364460916137/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (435101/312500000000000000000 : ℝ)*base89 + (435101/312500000000000000000 : ℝ)*base91 + (435101/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1626_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23879/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1626_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1626_s1_0 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1651875273/10000000000 : ℝ)*x 0 + (2757768787/5000000000 : ℝ)*x 1 + (5129797359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1651875273/10000000000 : ℝ)^4823 ≤ (2033373811733/20000000000000 : ℝ)^3799 := by
    have hnat : (1651875273 : ℕ)^4823*20000000000000^3799 ≤ 2033373811733^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651875273 10000000000 2033373811733 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757768787/5000000000 : ℝ)^4823 ≤ (11745574166231/25000000000000 : ℝ)^3799 := by
    have hnat : (2757768787 : ℕ)^4823*25000000000000^3799 ≤ 11745574166231^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757768787 5000000000 11745574166231 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129797359/10000000000 : ℝ)^4823 ≤ (21425417133817/50000000000000 : ℝ)^3799 := by
    have hnat : (5129797359 : ℕ)^4823*50000000000000^3799 ≤ 21425417133817^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129797359 10000000000 21425417133817 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1651875273/10000000000 : ℝ), (2757768787/5000000000 : ℝ), (5129797359/10000000000 : ℝ)] ![(2033373811733/20000000000000 : ℝ), (11745574166231/25000000000000 : ℝ), (21425417133817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1651875273/10000000000 : ℝ)|^4823 ≤ (2033373811733/20000000000000 : ℝ)^3799
        have hw : |(-1651875273/10000000000 : ℝ)|=(1651875273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757768787/5000000000 : ℝ)|^4823 ≤ (11745574166231/25000000000000 : ℝ)^3799
        have hw : |(2757768787/5000000000 : ℝ)|=(2757768787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129797359/10000000000 : ℝ)|^4823 ≤ (21425417133817/50000000000000 : ℝ)^3799
        have hw : |(5129797359/10000000000 : ℝ)|=(5129797359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_1 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073457597/2000000000 : ℝ)*x 0 + (-926547351/5000000000 : ℝ)*x 1 + (5129797139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073457597/2000000000 : ℝ)^4823 ≤ (11346235526513/25000000000000 : ℝ)^3799 := by
    have hnat : (1073457597 : ℕ)^4823*25000000000000^3799 ≤ 11346235526513^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073457597 2000000000 11346235526513 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (926547351/5000000000 : ℝ)^4823 ≤ (11764225951959/100000000000000 : ℝ)^3799 := by
    have hnat : (926547351 : ℕ)^4823*100000000000000^3799 ≤ 11764225951959^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926547351 5000000000 11764225951959 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129797139/10000000000 : ℝ)^4823 ≤ (21425415967277/50000000000000 : ℝ)^3799 := by
    have hnat : (5129797139 : ℕ)^4823*50000000000000^3799 ≤ 21425415967277^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129797139 10000000000 21425415967277 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073457597/2000000000 : ℝ), (-926547351/5000000000 : ℝ), (5129797139/10000000000 : ℝ)] ![(11346235526513/25000000000000 : ℝ), (11764225951959/100000000000000 : ℝ), (21425415967277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073457597/2000000000 : ℝ)|^4823 ≤ (11346235526513/25000000000000 : ℝ)^3799
        have hw : |(1073457597/2000000000 : ℝ)|=(1073457597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-926547351/5000000000 : ℝ)|^4823 ≤ (11764225951959/100000000000000 : ℝ)^3799
        have hw : |(-926547351/5000000000 : ℝ)|=(926547351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129797139/10000000000 : ℝ)|^4823 ≤ (21425415967277/50000000000000 : ℝ)^3799
        have hw : |(5129797139/10000000000 : ℝ)|=(5129797139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_2 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341822123/2500000000 : ℝ)*x 0 + (5129796483/10000000000 : ℝ)*x 1 + (-231636861/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341822123/2500000000 : ℝ)^4823 ≤ (11346236887183/25000000000000 : ℝ)^3799 := by
    have hnat : (1341822123 : ℕ)^4823*25000000000000^3799 ≤ 11346236887183^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341822123 2500000000 11346236887183 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129796483/10000000000 : ℝ)^4823 ≤ (10712706244433/25000000000000 : ℝ)^3799 := by
    have hnat : (5129796483 : ℕ)^4823*25000000000000^3799 ≤ 10712706244433^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129796483 10000000000 10712706244433 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231636861/1250000000 : ℝ)^4823 ≤ (2352845490209/20000000000000 : ℝ)^3799 := by
    have hnat : (231636861 : ℕ)^4823*20000000000000^3799 ≤ 2352845490209^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231636861 1250000000 2352845490209 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341822123/2500000000 : ℝ), (5129796483/10000000000 : ℝ), (-231636861/1250000000 : ℝ)] ![(11346236887183/25000000000000 : ℝ), (10712706244433/25000000000000 : ℝ), (2352845490209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341822123/2500000000 : ℝ)|^4823 ≤ (11346236887183/25000000000000 : ℝ)^3799
        have hw : |(1341822123/2500000000 : ℝ)|=(1341822123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129796483/10000000000 : ℝ)|^4823 ≤ (10712706244433/25000000000000 : ℝ)^3799
        have hw : |(5129796483/10000000000 : ℝ)|=(5129796483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231636861/1250000000 : ℝ)|^4823 ≤ (2352845490209/20000000000000 : ℝ)^3799
        have hw : |(-231636861/1250000000 : ℝ)|=(231636861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_3 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523753619/1250000000 : ℝ)*x 0 + (1863513933/5000000000 : ℝ)*x 1 + (4694925397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523753619/1250000000 : ℝ)^4823 ≤ (1325707299439/4000000000000 : ℝ)^3799 := by
    have hnat : (523753619 : ℕ)^4823*4000000000000^3799 ≤ 1325707299439^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523753619 1250000000 1325707299439 4000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863513933/5000000000 : ℝ)^4823 ≤ (28564442142547/100000000000000 : ℝ)^3799 := by
    have hnat : (1863513933 : ℕ)^4823*100000000000000^3799 ≤ 28564442142547^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863513933 5000000000 28564442142547 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4694925397/10000000000 : ℝ)^4823 ≤ (38292875363537/100000000000000 : ℝ)^3799 := by
    have hnat : (4694925397 : ℕ)^4823*100000000000000^3799 ≤ 38292875363537^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694925397 10000000000 38292875363537 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523753619/1250000000 : ℝ), (1863513933/5000000000 : ℝ), (4694925397/10000000000 : ℝ)] ![(1325707299439/4000000000000 : ℝ), (28564442142547/100000000000000 : ℝ), (38292875363537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523753619/1250000000 : ℝ)|^4823 ≤ (1325707299439/4000000000000 : ℝ)^3799
        have hw : |(523753619/1250000000 : ℝ)|=(523753619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1863513933/5000000000 : ℝ)|^4823 ≤ (28564442142547/100000000000000 : ℝ)^3799
        have hw : |(1863513933/5000000000 : ℝ)|=(1863513933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4694925397/10000000000 : ℝ)|^4823 ≤ (38292875363537/100000000000000 : ℝ)^3799
        have hw : |(4694925397/10000000000 : ℝ)|=(4694925397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_4 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1652067813/10000000000 : ℝ)*x 0 + (5133872593/10000000000 : ℝ)*x 1 + (5511401241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1652067813/10000000000 : ℝ)^4823 ≤ (10168373536299/100000000000000 : ℝ)^3799 := by
    have hnat : (1652067813 : ℕ)^4823*100000000000000^3799 ≤ 10168373536299^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652067813 10000000000 10168373536299 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133872593/10000000000 : ℝ)^4823 ≤ (2680878524311/6250000000000 : ℝ)^3799 := by
    have hnat : (5133872593 : ℕ)^4823*6250000000000^3799 ≤ 2680878524311^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133872593 10000000000 2680878524311 6250000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511401241/10000000000 : ℝ)^4823 ≤ (23468785028957/50000000000000 : ℝ)^3799 := by
    have hnat : (5511401241 : ℕ)^4823*50000000000000^3799 ≤ 23468785028957^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511401241 10000000000 23468785028957 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1652067813/10000000000 : ℝ), (5133872593/10000000000 : ℝ), (5511401241/10000000000 : ℝ)] ![(10168373536299/100000000000000 : ℝ), (2680878524311/6250000000000 : ℝ), (23468785028957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1652067813/10000000000 : ℝ)|^4823 ≤ (10168373536299/100000000000000 : ℝ)^3799
        have hw : |(-1652067813/10000000000 : ℝ)|=(1652067813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133872593/10000000000 : ℝ)|^4823 ≤ (2680878524311/6250000000000 : ℝ)^3799
        have hw : |(5133872593/10000000000 : ℝ)|=(5133872593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511401241/10000000000 : ℝ)|^4823 ≤ (23468785028957/50000000000000 : ℝ)^3799
        have hw : |(5511401241/10000000000 : ℝ)|=(5511401241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_5 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264438983/10000000000 : ℝ)*x 0 + (-735744933/5000000000 : ℝ)*x 1 + (2755700791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264438983/10000000000 : ℝ)^4823 ≤ (11070928924959/25000000000000 : ℝ)^3799 := by
    have hnat : (5264438983 : ℕ)^4823*25000000000000^3799 ≤ 11070928924959^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264438983 10000000000 11070928924959 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735744933/5000000000 : ℝ)^4823 ≤ (438935526783/5000000000000 : ℝ)^3799 := by
    have hnat : (735744933 : ℕ)^4823*5000000000000^3799 ≤ 438935526783^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735744933 5000000000 438935526783 5000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755700791/5000000000 : ℝ)^4823 ≤ (46937573744811/100000000000000 : ℝ)^3799 := by
    have hnat : (2755700791 : ℕ)^4823*100000000000000^3799 ≤ 46937573744811^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755700791 5000000000 46937573744811 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264438983/10000000000 : ℝ), (-735744933/5000000000 : ℝ), (2755700791/5000000000 : ℝ)] ![(11070928924959/25000000000000 : ℝ), (438935526783/5000000000000 : ℝ), (46937573744811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264438983/10000000000 : ℝ)|^4823 ≤ (11070928924959/25000000000000 : ℝ)^3799
        have hw : |(5264438983/10000000000 : ℝ)|=(5264438983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735744933/5000000000 : ℝ)|^4823 ≤ (438935526783/5000000000000 : ℝ)^3799
        have hw : |(-735744933/5000000000 : ℝ)|=(735744933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755700791/5000000000 : ℝ)|^4823 ≤ (46937573744811/100000000000000 : ℝ)^3799
        have hw : |(2755700791/5000000000 : ℝ)|=(2755700791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_6 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632219167/5000000000 : ℝ)*x 0 + (2755700911/5000000000 : ℝ)*x 1 + (-1471490439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632219167/5000000000 : ℝ)^4823 ≤ (5535463596127/12500000000000 : ℝ)^3799 := by
    have hnat : (2632219167 : ℕ)^4823*12500000000000^3799 ≤ 5535463596127^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632219167 5000000000 5535463596127 12500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755700911/5000000000 : ℝ)^4823 ≤ (23468788169847/50000000000000 : ℝ)^3799 := by
    have hnat : (2755700911 : ℕ)^4823*50000000000000^3799 ≤ 23468788169847^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755700911 5000000000 23468788169847 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1471490439/10000000000 : ℝ)^4823 ≤ (2194678718881/25000000000000 : ℝ)^3799 := by
    have hnat : (1471490439 : ℕ)^4823*25000000000000^3799 ≤ 2194678718881^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471490439 10000000000 2194678718881 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632219167/5000000000 : ℝ), (2755700911/5000000000 : ℝ), (-1471490439/10000000000 : ℝ)] ![(5535463596127/12500000000000 : ℝ), (23468788169847/50000000000000 : ℝ), (2194678718881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632219167/5000000000 : ℝ)|^4823 ≤ (5535463596127/12500000000000 : ℝ)^3799
        have hw : |(2632219167/5000000000 : ℝ)|=(2632219167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755700911/5000000000 : ℝ)|^4823 ≤ (23468788169847/50000000000000 : ℝ)^3799
        have hw : |(2755700911/5000000000 : ℝ)|=(2755700911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1471490439/10000000000 : ℝ)|^4823 ≤ (2194678718881/25000000000000 : ℝ)^3799
        have hw : |(-1471490439/10000000000 : ℝ)|=(1471490439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s1_7 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8184589/19531250 : ℝ)*x 0 + (4684700751/10000000000 : ℝ)*x 1 + (934351471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8184589/19531250 : ℝ)^4823 ≤ (16573754444247/50000000000000 : ℝ)^3799 := by
    have hnat : (8184589 : ℕ)^4823*50000000000000^3799 ≤ 16573754444247^3799*19531250^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8184589 19531250 16573754444247 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4684700751/10000000000 : ℝ)^4823 ≤ (19093516689263/50000000000000 : ℝ)^3799 := by
    have hnat : (4684700751 : ℕ)^4823*50000000000000^3799 ≤ 19093516689263^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4684700751 10000000000 19093516689263 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934351471/2500000000 : ℝ)^4823 ≤ (5733091543261/20000000000000 : ℝ)^3799 := by
    have hnat : (934351471 : ℕ)^4823*20000000000000^3799 ≤ 5733091543261^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934351471 2500000000 5733091543261 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8184589/19531250 : ℝ), (4684700751/10000000000 : ℝ), (934351471/2500000000 : ℝ)] ![(16573754444247/50000000000000 : ℝ), (19093516689263/50000000000000 : ℝ), (5733091543261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8184589/19531250 : ℝ)|^4823 ≤ (16573754444247/50000000000000 : ℝ)^3799
        have hw : |(8184589/19531250 : ℝ)|=(8184589/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4684700751/10000000000 : ℝ)|^4823 ≤ (19093516689263/50000000000000 : ℝ)^3799
        have hw : |(4684700751/10000000000 : ℝ)|=(4684700751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934351471/2500000000 : ℝ)|^4823 ≤ (5733091543261/20000000000000 : ℝ)^3799
        have hw : |(934351471/2500000000 : ℝ)|=(934351471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1626_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4701/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (4363/100000 : ℝ) ^ (4819/1024 : ℝ) ≤ (39696738422329/100000000000000000000 : ℝ) := by
    have hpowers : (4363/100000 : ℝ)^4819 ≤ (39696738422329/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4363 : ℕ)^4819*100000000000000000000^1024 ≤ 39696738422329^1024*100000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4363 100000 39696738422329 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4363/100000 : ℝ)) (X := (39696738422329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23879/100000 : ℝ) ^ (4819/1024 : ℝ) ≤ (118279619597883899/100000000000000000000 : ℝ) := by
    have hpowers : (23879/100000 : ℝ)^4819 ≤ (118279619597883899/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23879 : ℕ)^4819*100000000000000000000^1024 ≤ 118279619597883899^1024*100000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23879 100000 118279619597883899 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23879/100000 : ℝ)) (X := (118279619597883899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000039696738422329/50000000000000000000 : ℝ) ≤ (5000000843524537/5000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50000039696738422329/50000000000000000000 : ℝ)^1024 ≤ (5000000843524537/5000000000000000 : ℝ)^4819 := by
      have hnat : (50000039696738422329 : ℕ)^1024*5000000000000000^4819 ≤ 5000000843524537^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000039696738422329 50000000000000000000 5000000843524537 5000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000843524537/5000000000000000 : ℝ)) (X := (50000039696738422329/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25029579829084076557/25000000000000000000 : ℝ) ≤ (10002513022894931/10000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (25029579829084076557/25000000000000000000 : ℝ)^1024 ≤ (10002513022894931/10000000000000000 : ℝ)^4819 := by
      have hnat : (25029579829084076557 : ℕ)^1024*10000000000000000^4819 ≤ 10002513022894931^4819*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25029579829084076557 25000000000000000000 10002513022894931 10000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002513022894931/10000000000000000 : ℝ)) (X := (25029579829084076557/25000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50118279619597883899/50000000000000000000 : ℝ) ≤ (2501256089685197/2500000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50118279619597883899/50000000000000000000 : ℝ)^1024 ≤ (2501256089685197/2500000000000000 : ℝ)^4819 := by
      have hnat : (50118279619597883899 : ℕ)^1024*2500000000000000^4819 ≤ 2501256089685197^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50118279619597883899 50000000000000000000 2501256089685197 2500000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501256089685197/2500000000000000 : ℝ)) (X := (50118279619597883899/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(39696738422329/100000000000000000000 : ℝ) ≤ ((97569059503929390001/97580000000000000000 : ℝ)+2*(2511335845857/1951600000000000 : ℝ)*(4363/100000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (97569059503929390001/97580000000000000000 : ℝ)+2*(2511335845857/1951600000000000 : ℝ)*(4363/100000 : ℝ)=(5000000843524537/5000000000000000 : ℝ) by norm_num, show 1+2*(39696738422329/100000000000000000000 : ℝ)=(50000039696738422329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(118279619597883899/100000000000000000000 : ℝ)+(39696738422329/100000000000000000000 : ℝ) ≤ ((97569059503929390001/97580000000000000000 : ℝ)+(2511335845857/1951600000000000 : ℝ)*((23879/100000 : ℝ)+(4363/100000 : ℝ)))^(4819/1024 : ℝ) := by
    rw [show (97569059503929390001/97580000000000000000 : ℝ)+(2511335845857/1951600000000000 : ℝ)*((23879/100000 : ℝ)+(4363/100000 : ℝ))=(10002513022894931/10000000000000000 : ℝ) by norm_num, show 1+(118279619597883899/100000000000000000000 : ℝ)+(39696738422329/100000000000000000000 : ℝ)=(25029579829084076557/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(118279619597883899/100000000000000000000 : ℝ) ≤ ((97569059503929390001/97580000000000000000 : ℝ)+2*(2511335845857/1951600000000000 : ℝ)*(23879/100000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (97569059503929390001/97580000000000000000 : ℝ)+2*(2511335845857/1951600000000000 : ℝ)*(23879/100000 : ℝ)=(2501256089685197/2500000000000000 : ℝ) by norm_num, show 1+2*(118279619597883899/100000000000000000000 : ℝ)=(50118279619597883899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (97569059503929390001/97580000000000000000 : ℝ)*(X 1 0+X 2 0)+(2511335845857/1951600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (4363/100000 : ℝ)) (hi := (23879/100000 : ℝ)) (c := (97569059503929390001/97580000000000000000 : ℝ)) (alpha := (2511335845857/1951600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (97569059503929390001/97580000000000000000 : ℝ)*(X 0 1+X 2 1)+(2511335845857/1951600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (4363/100000 : ℝ)) (hi := (23879/100000 : ℝ)) (c := (97569059503929390001/97580000000000000000 : ℝ)) (alpha := (2511335845857/1951600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (97569059503929390001/97580000000000000000 : ℝ)*(X 0 2+X 1 2)+(2511335845857/1951600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (4363/100000 : ℝ)) (hi := (23879/100000 : ℝ)) (c := (97569059503929390001/97580000000000000000 : ℝ)) (alpha := (2511335845857/1951600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1651875273/10000000000 : ℝ)*X 0 0+(2757768787/5000000000 : ℝ)*X 0 1+(5129797359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073457597/2000000000 : ℝ)*X 1 0+(-926547351/5000000000 : ℝ)*X 1 1+(5129797139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1341822123/2500000000 : ℝ)*X 2 0+(5129796483/10000000000 : ℝ)*X 2 1+(-231636861/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((523753619/1250000000 : ℝ)*X 0 0+(1863513933/5000000000 : ℝ)*X 0 1+(4694925397/10000000000 : ℝ)*X 0 2+(523753619/1250000000 : ℝ)*X 1 0+(1863513933/5000000000 : ℝ)*X 1 1+(4694925397/10000000000 : ℝ)*X 1 2+(523753619/1250000000 : ℝ)*X 2 0+(1863513933/5000000000 : ℝ)*X 2 1+(4694925397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1652067813/10000000000 : ℝ)*X 0 0+(5133872593/10000000000 : ℝ)*X 0 1+(5511401241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264438983/10000000000 : ℝ)*X 1 0+(-735744933/5000000000 : ℝ)*X 1 1+(2755700791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632219167/5000000000 : ℝ)*X 2 0+(2755700911/5000000000 : ℝ)*X 2 1+(-1471490439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8184589/19531250 : ℝ)*X 0 0+(4684700751/10000000000 : ℝ)*X 0 1+(934351471/2500000000 : ℝ)*X 0 2+(8184589/19531250 : ℝ)*X 1 0+(4684700751/10000000000 : ℝ)*X 1 1+(934351471/2500000000 : ℝ)*X 1 2+(8184589/19531250 : ℝ)*X 2 0+(4684700751/10000000000 : ℝ)*X 2 1+(934351471/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3730031841632713998190308681/348500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51141311/12500000000000 : ℝ)*(base1) + (1767675703/100000000000000 : ℝ)*(base19) + (1006279987/50000000000000 : ℝ)*(base23) + (48219377/20000000000000 : ℝ)*(upper3) + (170630101/100000000000000 : ℝ)*(upper5) + (906403379743589/50000000000000 : ℝ)*(major0) + (906403379743589/50000000000000 : ℝ)*(major1) + (906403379743589/50000000000000 : ℝ)*(major2) + (1296213940072201/50000000000000 : ℝ)*(sp0) + (2592434950827577/100000000000000 : ℝ)*(sp1) + (1296217352971653/50000000000000 : ℝ)*(sp2) + (1033171226062511/100000000000000 : ℝ)*(sp3) + (1849497873/20000000000000 : ℝ)*(sp4) + (601063491/12500000000000 : ℝ)*(sp7) + (1033176443700927/100000000000000 : ℝ)*(f.failure) + (32405458981291/1250000000000 : ℝ)*(f.sum) + (24147718950911/6970000000000000000000000000 : ℝ)*base66 + (1737206972126586227/697000000000000000000000000000000 : ℝ)*base67 + (1150643055808413773/697000000000000000000000000000000 : ℝ)*base70 + (6218850270851413773/697000000000000000000000000000000 : ℝ)*base72 + (25274038296461/6970000000000000000000000000 : ℝ)*base74 + (5237409102048413773/697000000000000000000000000000000 : ℝ)*base76 + (430897600869586227/697000000000000000000000000000000 : ℝ)*base77 + (10465143175558413773/697000000000000000000000000000000 : ℝ)*base80 + (18395568970731/6970000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2293897/312500000000000000000 : ℝ)*base89 + (2293897/312500000000000000000 : ℝ)*base91 + (2293897/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1915477023448634060190576579/243950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1584040447/100000000000000 : ℝ)*(base19) + (1318733603/100000000000000 : ℝ)*(base23) + (18558783/50000000000000 : ℝ)*(upper2) + (172405267/50000000000000 : ℝ)*(upper3) + (7143263/12500000000000 : ℝ)*(upper5) + (185221898502807/10000000000000 : ℝ)*(major0) + (185221898502807/10000000000000 : ℝ)*(major1) + (185221898502807/10000000000000 : ℝ)*(major2) + (11963321293/100000000000000 : ℝ)*(sp1) + (5744366423/50000000000000 : ℝ)*(sp2) + (2648798979105219/100000000000000 : ℝ)*(sp4) + (1324392715871739/50000000000000 : ℝ)*(sp5) + (264878617163877/10000000000000 : ℝ)*(sp6) + (527819364610047/50000000000000 : ℝ)*(sp7) + (527819364610047/50000000000000 : ℝ)*(f.failure) + (2648798979105219/100000000000000 : ℝ)*(f.sum) + (32484415939911/9758000000000000000000000000 : ℝ)*base66 + (3998251470482382807/975800000000000000000000000000000 : ℝ)*base67 + (224094761701182807/975800000000000000000000000000000 : ℝ)*base69 + (4550385057004382807/975800000000000000000000000000000 : ℝ)*base71 + (11024267295081/9758000000000000000000000000 : ℝ)*base74 + (7669071962385982807/975800000000000000000000000000000 : ℝ)*base75 + (3777140867617017193/975800000000000000000000000000000 : ℝ)*base78 + (8141638111404582807/975800000000000000000000000000000 : ℝ)*base79 + (5081931175889/1951600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (41217/156250000000000000000 : ℝ)*base89 + (41217/156250000000000000000 : ℝ)*base91 + (41217/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1626_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1626_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1626_s2_0 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1663730227/10000000000 : ℝ)*x 0 + (5460109887/10000000000 : ℝ)*x 1 + (1294359871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663730227/10000000000 : ℝ)^4823 ≤ (5129794904967/50000000000000 : ℝ)^3799 := by
    have hnat : (1663730227 : ℕ)^4823*50000000000000^3799 ≤ 5129794904967^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663730227 10000000000 5129794904967 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460109887/10000000000 : ℝ)^4823 ≤ (927674088707/2000000000000 : ℝ)^3799 := by
    have hnat : (5460109887 : ℕ)^4823*2000000000000^3799 ≤ 927674088707^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460109887 10000000000 927674088707 2000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294359871/2500000000 : ℝ)^4823 ≤ (43356705749979/100000000000000 : ℝ)^3799 := by
    have hnat : (1294359871 : ℕ)^4823*100000000000000^3799 ≤ 43356705749979^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294359871 2500000000 43356705749979 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1663730227/10000000000 : ℝ), (5460109887/10000000000 : ℝ), (1294359871/2500000000 : ℝ)] ![(5129794904967/50000000000000 : ℝ), (927674088707/2000000000000 : ℝ), (43356705749979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1663730227/10000000000 : ℝ)|^4823 ≤ (5129794904967/50000000000000 : ℝ)^3799
        have hw : |(-1663730227/10000000000 : ℝ)|=(1663730227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460109887/10000000000 : ℝ)|^4823 ≤ (927674088707/2000000000000 : ℝ)^3799
        have hw : |(5460109887/10000000000 : ℝ)|=(5460109887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294359871/2500000000 : ℝ)|^4823 ≤ (43356705749979/100000000000000 : ℝ)^3799
        have hw : |(1294359871/2500000000 : ℝ)|=(1294359871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_1 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167273347/312500000 : ℝ)*x 0 + (-452387537/2500000000 : ℝ)*x 1 + (1294359883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167273347/312500000 : ℝ)^4823 ≤ (2261445088579/5000000000000 : ℝ)^3799 := by
    have hnat : (167273347 : ℕ)^4823*5000000000000^3799 ≤ 2261445088579^3799*312500000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167273347 312500000 2261445088579 5000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452387537/2500000000 : ℝ)^4823 ≤ (2282878388969/20000000000000 : ℝ)^3799 := by
    have hnat : (452387537 : ℕ)^4823*20000000000000^3799 ≤ 2282878388969^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452387537 2500000000 2282878388969 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294359883/2500000000 : ℝ)^4823 ≤ (8671341252057/20000000000000 : ℝ)^3799 := by
    have hnat : (1294359883 : ℕ)^4823*20000000000000^3799 ≤ 8671341252057^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294359883 2500000000 8671341252057 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167273347/312500000 : ℝ), (-452387537/2500000000 : ℝ), (1294359883/2500000000 : ℝ)] ![(2261445088579/5000000000000 : ℝ), (2282878388969/20000000000000 : ℝ), (8671341252057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167273347/312500000 : ℝ)|^4823 ≤ (2261445088579/5000000000000 : ℝ)^3799
        have hw : |(167273347/312500000 : ℝ)|=(167273347/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452387537/2500000000 : ℝ)|^4823 ≤ (2282878388969/20000000000000 : ℝ)^3799
        have hw : |(-452387537/2500000000 : ℝ)|=(452387537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294359883/2500000000 : ℝ)|^4823 ≤ (8671341252057/20000000000000 : ℝ)^3799
        have hw : |(1294359883/2500000000 : ℝ)|=(1294359883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_2 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535274713/1000000000 : ℝ)*x 0 + (1035487889/2000000000 : ℝ)*x 1 + (-1809550229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535274713/1000000000 : ℝ)^4823 ≤ (5653612756311/12500000000000 : ℝ)^3799 := by
    have hnat : (535274713 : ℕ)^4823*12500000000000^3799 ≤ 5653612756311^3799*1000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535274713 1000000000 5653612756311 12500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035487889/2000000000 : ℝ)^4823 ≤ (10839176333839/25000000000000 : ℝ)^3799 := by
    have hnat : (1035487889 : ℕ)^4823*25000000000000^3799 ≤ 10839176333839^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035487889 2000000000 10839176333839 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1809550229/10000000000 : ℝ)^4823 ≤ (5707196296751/50000000000000 : ℝ)^3799 := by
    have hnat : (1809550229 : ℕ)^4823*50000000000000^3799 ≤ 5707196296751^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809550229 10000000000 5707196296751 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535274713/1000000000 : ℝ), (1035487889/2000000000 : ℝ), (-1809550229/10000000000 : ℝ)] ![(5653612756311/12500000000000 : ℝ), (10839176333839/25000000000000 : ℝ), (5707196296751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535274713/1000000000 : ℝ)|^4823 ≤ (5653612756311/12500000000000 : ℝ)^3799
        have hw : |(535274713/1000000000 : ℝ)|=(535274713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035487889/2000000000 : ℝ)|^4823 ≤ (10839176333839/25000000000000 : ℝ)^3799
        have hw : |(1035487889/2000000000 : ℝ)|=(1035487889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1809550229/10000000000 : ℝ)|^4823 ≤ (5707196296751/50000000000000 : ℝ)^3799
        have hw : |(-1809550229/10000000000 : ℝ)|=(1809550229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_3 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2099406689/5000000000 : ℝ)*x 0 + (3855429477/10000000000 : ℝ)*x 1 + (4564703457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099406689/5000000000 : ℝ)^4823 ≤ (6646184055101/20000000000000 : ℝ)^3799 := by
    have hnat : (2099406689 : ℕ)^4823*20000000000000^3799 ≤ 6646184055101^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099406689 5000000000 6646184055101 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3855429477/10000000000 : ℝ)^4823 ≤ (14909768810559/50000000000000 : ℝ)^3799 := by
    have hnat : (3855429477 : ℕ)^4823*50000000000000^3799 ≤ 14909768810559^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855429477 10000000000 14909768810559 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564703457/10000000000 : ℝ)^4823 ≤ (36949542081223/100000000000000 : ℝ)^3799 := by
    have hnat : (4564703457 : ℕ)^4823*100000000000000^3799 ≤ 36949542081223^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564703457 10000000000 36949542081223 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099406689/5000000000 : ℝ), (3855429477/10000000000 : ℝ), (4564703457/10000000000 : ℝ)] ![(6646184055101/20000000000000 : ℝ), (14909768810559/50000000000000 : ℝ), (36949542081223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099406689/5000000000 : ℝ)|^4823 ≤ (6646184055101/20000000000000 : ℝ)^3799
        have hw : |(2099406689/5000000000 : ℝ)|=(2099406689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3855429477/10000000000 : ℝ)|^4823 ≤ (14909768810559/50000000000000 : ℝ)^3799
        have hw : |(3855429477/10000000000 : ℝ)|=(3855429477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564703457/10000000000 : ℝ)|^4823 ≤ (36949542081223/100000000000000 : ℝ)^3799
        have hw : |(4564703457/10000000000 : ℝ)|=(4564703457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_4 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1663805519/10000000000 : ℝ)*x 0 + (5179634921/10000000000 : ℝ)*x 1 + (5457890781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663805519/10000000000 : ℝ)^4823 ≤ (10260179259349/100000000000000 : ℝ)^3799 := by
    have hnat : (1663805519 : ℕ)^4823*100000000000000^3799 ≤ 10260179259349^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663805519 10000000000 10260179259349 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179634921/10000000000 : ℝ)^4823 ≤ (21690023792879/50000000000000 : ℝ)^3799 := by
    have hnat : (5179634921 : ℕ)^4823*50000000000000^3799 ≤ 21690023792879^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179634921 10000000000 21690023792879 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457890781/10000000000 : ℝ)^4823 ≤ (9271954627277/20000000000000 : ℝ)^3799 := by
    have hnat : (5457890781 : ℕ)^4823*20000000000000^3799 ≤ 9271954627277^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457890781 10000000000 9271954627277 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1663805519/10000000000 : ℝ), (5179634921/10000000000 : ℝ), (5457890781/10000000000 : ℝ)] ![(10260179259349/100000000000000 : ℝ), (21690023792879/50000000000000 : ℝ), (9271954627277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1663805519/10000000000 : ℝ)|^4823 ≤ (10260179259349/100000000000000 : ℝ)^3799
        have hw : |(-1663805519/10000000000 : ℝ)|=(1663805519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179634921/10000000000 : ℝ)|^4823 ≤ (21690023792879/50000000000000 : ℝ)^3799
        have hw : |(5179634921/10000000000 : ℝ)|=(5179634921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457890781/10000000000 : ℝ)|^4823 ≤ (9271954627277/20000000000000 : ℝ)^3799
        have hw : |(5457890781/10000000000 : ℝ)|=(5457890781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_5 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277468569/10000000000 : ℝ)*x 0 + (-382274693/2500000000 : ℝ)*x 1 + (5457890939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277468569/10000000000 : ℝ)^4823 ≤ (173526984481/390625000000 : ℝ)^3799 := by
    have hnat : (5277468569 : ℕ)^4823*390625000000^3799 ≤ 173526984481^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277468569 10000000000 173526984481 390625000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382274693/2500000000 : ℝ)^4823 ≤ (9217317116367/100000000000000 : ℝ)^3799 := by
    have hnat : (382274693 : ℕ)^4823*100000000000000^3799 ≤ 9217317116367^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382274693 2500000000 9217317116367 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457890939/10000000000 : ℝ)^4823 ≤ (11589943710049/25000000000000 : ℝ)^3799 := by
    have hnat : (5457890939 : ℕ)^4823*25000000000000^3799 ≤ 11589943710049^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457890939 10000000000 11589943710049 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277468569/10000000000 : ℝ), (-382274693/2500000000 : ℝ), (5457890939/10000000000 : ℝ)] ![(173526984481/390625000000 : ℝ), (9217317116367/100000000000000 : ℝ), (11589943710049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277468569/10000000000 : ℝ)|^4823 ≤ (173526984481/390625000000 : ℝ)^3799
        have hw : |(5277468569/10000000000 : ℝ)|=(5277468569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-382274693/2500000000 : ℝ)|^4823 ≤ (9217317116367/100000000000000 : ℝ)^3799
        have hw : |(-382274693/2500000000 : ℝ)|=(382274693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457890939/10000000000 : ℝ)|^4823 ≤ (11589943710049/25000000000000 : ℝ)^3799
        have hw : |(5457890939/10000000000 : ℝ)|=(5457890939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_6 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277469651/10000000000 : ℝ)*x 0 + (2728944799/5000000000 : ℝ)*x 1 + (-30581983/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277469651/10000000000 : ℝ)^4823 ≤ (8884583917953/20000000000000 : ℝ)^3799 := by
    have hnat : (5277469651 : ℕ)^4823*20000000000000^3799 ≤ 8884583917953^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277469651 10000000000 8884583917953 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728944799/5000000000 : ℝ)^4823 ≤ (46359760379367/100000000000000 : ℝ)^3799 := by
    have hnat : (2728944799 : ℕ)^4823*100000000000000^3799 ≤ 46359760379367^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728944799 5000000000 46359760379367 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30581983/200000000 : ℝ)^4823 ≤ (9217320009103/100000000000000 : ℝ)^3799 := by
    have hnat : (30581983 : ℕ)^4823*100000000000000^3799 ≤ 9217320009103^3799*200000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30581983 200000000 9217320009103 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277469651/10000000000 : ℝ), (2728944799/5000000000 : ℝ), (-30581983/200000000 : ℝ)] ![(8884583917953/20000000000000 : ℝ), (46359760379367/100000000000000 : ℝ), (9217320009103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277469651/10000000000 : ℝ)|^4823 ≤ (8884583917953/20000000000000 : ℝ)^3799
        have hw : |(5277469651/10000000000 : ℝ)|=(5277469651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728944799/5000000000 : ℝ)|^4823 ≤ (46359760379367/100000000000000 : ℝ)^3799
        have hw : |(2728944799/5000000000 : ℝ)|=(2728944799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30581983/200000000 : ℝ)|^4823 ≤ (9217320009103/100000000000000 : ℝ)^3799
        have hw : |(-30581983/200000000 : ℝ)|=(30581983/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s2_7 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839800603/2000000000 : ℝ)*x 0 + (4559196589/10000000000 : ℝ)*x 1 + (386099673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839800603/2000000000 : ℝ)^4823 ≤ (16616412845043/50000000000000 : ℝ)^3799 := by
    have hnat : (839800603 : ℕ)^4823*50000000000000^3799 ≤ 16616412845043^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839800603 2000000000 16616412845043 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4559196589/10000000000 : ℝ)^4823 ≤ (4611620006999/12500000000000 : ℝ)^3799 := by
    have hnat : (4559196589 : ℕ)^4823*12500000000000^3799 ≤ 4611620006999^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559196589 10000000000 4611620006999 12500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386099673/1000000000 : ℝ)^4823 ≤ (1194968569087/4000000000000 : ℝ)^3799 := by
    have hnat : (386099673 : ℕ)^4823*4000000000000^3799 ≤ 1194968569087^3799*1000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386099673 1000000000 1194968569087 4000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839800603/2000000000 : ℝ), (4559196589/10000000000 : ℝ), (386099673/1000000000 : ℝ)] ![(16616412845043/50000000000000 : ℝ), (4611620006999/12500000000000 : ℝ), (1194968569087/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839800603/2000000000 : ℝ)|^4823 ≤ (16616412845043/50000000000000 : ℝ)^3799
        have hw : |(839800603/2000000000 : ℝ)|=(839800603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4559196589/10000000000 : ℝ)|^4823 ≤ (4611620006999/12500000000000 : ℝ)^3799
        have hw : |(4559196589/10000000000 : ℝ)|=(4559196589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(386099673/1000000000 : ℝ)|^4823 ≤ (1194968569087/4000000000000 : ℝ)^3799
        have hw : |(386099673/1000000000 : ℝ)|=(386099673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1626_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10431/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1643/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4701/50000 : ℝ) ^ (4819/1024 : ℝ) ≤ (1472035655847759/100000000000000000000 : ℝ) := by
    have hpowers : (4701/50000 : ℝ)^4819 ≤ (1472035655847759/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4701 : ℕ)^4819*100000000000000000000^1024 ≤ 1472035655847759^1024*50000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4701 50000 1472035655847759 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4701/50000 : ℝ)) (X := (1472035655847759/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/20000 : ℝ) ^ (4819/1024 : ℝ) ≤ (28028426953708769/100000000000000000000 : ℝ) := by
    have hpowers : (3517/20000 : ℝ)^4819 ≤ (28028426953708769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3517 : ℕ)^4819*100000000000000000000^1024 ≤ 28028426953708769^1024*20000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 20000 28028426953708769 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/20000 : ℝ)) (X := (28028426953708769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001472035655847759/50000000000000000000 : ℝ) ≤ (2500015639624797/2500000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50001472035655847759/50000000000000000000 : ℝ)^1024 ≤ (2500015639624797/2500000000000000 : ℝ)^4819 := by
      have hnat : (50001472035655847759 : ℕ)^1024*2500000000000000^4819 ≤ 2500015639624797^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001472035655847759 50000000000000000000 2500015639624797 2500000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500015639624797/2500000000000000 : ℝ)) (X := (50001472035655847759/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251843778913097283/6250000000000000000 : ℝ) ≤ (10000626789071097/10000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (6251843778913097283/6250000000000000000 : ℝ)^1024 ≤ (10000626789071097/10000000000000000 : ℝ)^4819 := by
      have hnat : (6251843778913097283 : ℕ)^1024*10000000000000000^4819 ≤ 10000626789071097^4819*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251843778913097283 6250000000000000000 10000626789071097 10000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000626789071097/10000000000000000 : ℝ)) (X := (6251843778913097283/6250000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028028426953708769/50000000000000000000 : ℝ) ≤ (5000595509821503/5000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50028028426953708769/50000000000000000000 : ℝ)^1024 ≤ (5000595509821503/5000000000000000 : ℝ)^4819 := by
      have hnat : (50028028426953708769 : ℕ)^1024*5000000000000000^4819 ≤ 5000595509821503^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028028426953708769 50000000000000000000 5000595509821503 5000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000595509821503/5000000000000000 : ℝ)) (X := (50028028426953708769/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1472035655847759/100000000000000000000 : ℝ) ≤ ((10227487765565584821/10228750000000000000 : ℝ)+2*(564230571909/818300000000000 : ℝ)*(4701/50000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (10227487765565584821/10228750000000000000 : ℝ)+2*(564230571909/818300000000000 : ℝ)*(4701/50000 : ℝ)=(2500015639624797/2500000000000000 : ℝ) by norm_num, show 1+2*(1472035655847759/100000000000000000000 : ℝ)=(50001472035655847759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28028426953708769/100000000000000000000 : ℝ)+(1472035655847759/100000000000000000000 : ℝ) ≤ ((10227487765565584821/10228750000000000000 : ℝ)+(564230571909/818300000000000 : ℝ)*((3517/20000 : ℝ)+(4701/50000 : ℝ)))^(4819/1024 : ℝ) := by
    rw [show (10227487765565584821/10228750000000000000 : ℝ)+(564230571909/818300000000000 : ℝ)*((3517/20000 : ℝ)+(4701/50000 : ℝ))=(10000626789071097/10000000000000000 : ℝ) by norm_num, show 1+(28028426953708769/100000000000000000000 : ℝ)+(1472035655847759/100000000000000000000 : ℝ)=(6251843778913097283/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28028426953708769/100000000000000000000 : ℝ) ≤ ((10227487765565584821/10228750000000000000 : ℝ)+2*(564230571909/818300000000000 : ℝ)*(3517/20000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (10227487765565584821/10228750000000000000 : ℝ)+2*(564230571909/818300000000000 : ℝ)*(3517/20000 : ℝ)=(5000595509821503/5000000000000000 : ℝ) by norm_num, show 1+2*(28028426953708769/100000000000000000000 : ℝ)=(50028028426953708769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10227487765565584821/10228750000000000000 : ℝ)*(X 1 0+X 2 0)+(564230571909/818300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (4701/50000 : ℝ)) (hi := (3517/20000 : ℝ)) (c := (10227487765565584821/10228750000000000000 : ℝ)) (alpha := (564230571909/818300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10227487765565584821/10228750000000000000 : ℝ)*(X 0 1+X 2 1)+(564230571909/818300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (4701/50000 : ℝ)) (hi := (3517/20000 : ℝ)) (c := (10227487765565584821/10228750000000000000 : ℝ)) (alpha := (564230571909/818300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10227487765565584821/10228750000000000000 : ℝ)*(X 0 2+X 1 2)+(564230571909/818300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (4701/50000 : ℝ)) (hi := (3517/20000 : ℝ)) (c := (10227487765565584821/10228750000000000000 : ℝ)) (alpha := (564230571909/818300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1663730227/10000000000 : ℝ)*X 0 0+(5460109887/10000000000 : ℝ)*X 0 1+(1294359871/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167273347/312500000 : ℝ)*X 1 0+(-452387537/2500000000 : ℝ)*X 1 1+(1294359883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535274713/1000000000 : ℝ)*X 2 0+(1035487889/2000000000 : ℝ)*X 2 1+(-1809550229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099406689/5000000000 : ℝ)*X 0 0+(3855429477/10000000000 : ℝ)*X 0 1+(4564703457/10000000000 : ℝ)*X 0 2+(2099406689/5000000000 : ℝ)*X 1 0+(3855429477/10000000000 : ℝ)*X 1 1+(4564703457/10000000000 : ℝ)*X 1 2+(2099406689/5000000000 : ℝ)*X 2 0+(3855429477/10000000000 : ℝ)*X 2 1+(4564703457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1663805519/10000000000 : ℝ)*X 0 0+(5179634921/10000000000 : ℝ)*X 0 1+(5457890781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277468569/10000000000 : ℝ)*X 1 0+(-382274693/2500000000 : ℝ)*X 1 1+(5457890939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277469651/10000000000 : ℝ)*X 2 0+(2728944799/5000000000 : ℝ)*X 2 1+(-30581983/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839800603/2000000000 : ℝ)*X 0 0+(4559196589/10000000000 : ℝ)*X 0 1+(386099673/1000000000 : ℝ)*X 0 2+(839800603/2000000000 : ℝ)*X 1 0+(4559196589/10000000000 : ℝ)*X 1 1+(386099673/1000000000 : ℝ)*X 1 2+(839800603/2000000000 : ℝ)*X 2 0+(4559196589/10000000000 : ℝ)*X 2 1+(386099673/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11867279124853036884465831/1304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (714014711/50000000000000 : ℝ)*(base19) + (1355771697/100000000000000 : ℝ)*(base23) + (4787581/10000000000000 : ℝ)*(lower2) + (251046899/100000000000000 : ℝ)*(upper3) + (3945191/3125000000000 : ℝ)*(upper5) + (618453713723817/25000000000000 : ℝ)*(major0) + (618453713723817/25000000000000 : ℝ)*(major1) + (618453713723817/25000000000000 : ℝ)*(major2) + (3537707137562837/100000000000000 : ℝ)*(sp0) + (884430479869487/25000000000000 : ℝ)*(sp1) + (1768860995867837/50000000000000 : ℝ)*(sp2) + (1409898589922937/100000000000000 : ℝ)*(sp3) + (16209944533/100000000000000 : ℝ)*(sp4) + (7469164269/100000000000000 : ℝ)*(sp7) + (1409906059087207/100000000000000 : ℝ)*(f.failure) + (353772334750737/10000000000000 : ℝ)*(f.sum) + (186211912432187/40915000000000000000000000000 : ℝ)*base65 + (145788977712518243/255718750000000000000000000000000 : ℝ)*base68 + (233434343781705743/255718750000000000000000000000000 : ℝ)*base70 + (463720547909799493/255718750000000000000000000000000 : ℝ)*base72 + (35360709716039/20457500000000000000000000000 : ℝ)*base74 + (177312761086861993/255718750000000000000000000000000 : ℝ)*base76 + (1837762095663674493/255718750000000000000000000000000 : ℝ)*base78 + (1831986810184205743/255718750000000000000000000000000 : ℝ)*base80 + (64486306766583/40915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2160977/312500000000000000000 : ℝ)*base89 + (2160977/312500000000000000000 : ℝ)*base91 + (2160977/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24220967093235903926157/2557187500000000000000000000 : ℝ) := by norm_num
    linear_combination (535688573/50000000000000 : ℝ)*(base19) + (1072776369/50000000000000 : ℝ)*(base23) + (208520827/100000000000000 : ℝ)*(upper3) + (19035933/12500000000000 : ℝ)*(lower4) + (1256517369737411/50000000000000 : ℝ)*(major0) + (1256517369737411/50000000000000 : ℝ)*(major1) + (1256517369737411/50000000000000 : ℝ)*(major2) + (1194119741/10000000000000 : ℝ)*(sp1) + (3840685717/25000000000000 : ℝ)*(sp2) + (1015293707/100000000000000 : ℝ)*(sp3) + (89845260996833/2500000000000 : ℝ)*(sp4) + (898449356824691/25000000000000 : ℝ)*(sp5) + (1796896465788857/50000000000000 : ℝ)*(sp6) + (1432257708058569/100000000000000 : ℝ)*(sp7) + (57290348934091/4000000000000 : ℝ)*(f.failure) + (89845260996833/2500000000000 : ℝ)*(f.sum) + (210714335466217/40915000000000000000000000000 : ℝ)*base66 + (1561449863743675931/511437500000000000000000000000000 : ℝ)*base67 + (1933133339000738431/511437500000000000000000000000000 : ℝ)*base69 + (2859731462117011569/511437500000000000000000000000000 : ℝ)*base72 + (72699698312991/20457500000000000000000000000 : ℝ)*base74 + (1746991189816011569/511437500000000000000000000000000 : ℝ)*base76 + (1093010151462886569/511437500000000000000000000000000 : ℝ)*base78 + (1532482293325175931/511437500000000000000000000000000 : ℝ)*base79 + (13312549011057/40915000000000000000000000000 : ℝ)*base82 + (112899/12500000000000000000 : ℝ)*base90 + (112899/12500000000000000000 : ℝ)*base92 + (112899/12500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1626_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1626_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1626_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1626_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1626_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1626_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1626_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
