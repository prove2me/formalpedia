-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1534_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:36.89115+00:00
-- url     : https://prove2.me/submissions/093a21de-2d12-444f-820b-c29970da1cd2

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
theorem support_rectangle_w1534_s3_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835616271/10000000000 : ℝ)*x 0 + (217317163/400000000 : ℝ)*x 1 + (5216382771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835616271/10000000000 : ℝ)^4565 ≤ (5621465124727/50000000000000 : ℝ)^3541 := by
    have hnat : (1835616271 : ℕ)^4565*50000000000000^3541 ≤ 5621465124727^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835616271 10000000000 5621465124727 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217317163/400000000 : ℝ)^4565 ≤ (11385449135087/25000000000000 : ℝ)^3541 := by
    have hnat : (217317163 : ℕ)^4565*25000000000000^3541 ≤ 11385449135087^3541*400000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217317163 400000000 11385449135087 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216382771/10000000000 : ℝ)^4565 ≤ (21607636595911/50000000000000 : ℝ)^3541 := by
    have hnat : (5216382771 : ℕ)^4565*50000000000000^3541 ≤ 21607636595911^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216382771 10000000000 21607636595911 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835616271/10000000000 : ℝ), (217317163/400000000 : ℝ), (5216382771/10000000000 : ℝ)] ![(5621465124727/50000000000000 : ℝ), (11385449135087/25000000000000 : ℝ), (21607636595911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835616271/10000000000 : ℝ)|^4565 ≤ (5621465124727/50000000000000 : ℝ)^3541
        have hw : |(-1835616271/10000000000 : ℝ)|=(1835616271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217317163/400000000 : ℝ)|^4565 ≤ (11385449135087/25000000000000 : ℝ)^3541
        have hw : |(217317163/400000000 : ℝ)|=(217317163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216382771/10000000000 : ℝ)|^4565 ≤ (21607636595911/50000000000000 : ℝ)^3541
        have hw : |(5216382771/10000000000 : ℝ)|=(5216382771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337752259/2500000000 : ℝ)*x 0 + (-389306381/2000000000 : ℝ)*x 1 + (5216382621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337752259/2500000000 : ℝ)^4565 ≤ (44658452617317/100000000000000 : ℝ)^3541 := by
    have hnat : (1337752259 : ℕ)^4565*100000000000000^3541 ≤ 44658452617317^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337752259 2500000000 44658452617317 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389306381/2000000000 : ℝ)^4565 ≤ (1515784472777/12500000000000 : ℝ)^3541 := by
    have hnat : (389306381 : ℕ)^4565*12500000000000^3541 ≤ 1515784472777^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389306381 2000000000 1515784472777 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216382621/10000000000 : ℝ)^4565 ≤ (2160763579489/5000000000000 : ℝ)^3541 := by
    have hnat : (5216382621 : ℕ)^4565*5000000000000^3541 ≤ 2160763579489^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216382621 10000000000 2160763579489 5000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337752259/2500000000 : ℝ), (-389306381/2000000000 : ℝ), (5216382621/10000000000 : ℝ)] ![(44658452617317/100000000000000 : ℝ), (1515784472777/12500000000000 : ℝ), (2160763579489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337752259/2500000000 : ℝ)|^4565 ≤ (44658452617317/100000000000000 : ℝ)^3541
        have hw : |(1337752259/2500000000 : ℝ)|=(1337752259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389306381/2000000000 : ℝ)|^4565 ≤ (1515784472777/12500000000000 : ℝ)^3541
        have hw : |(-389306381/2000000000 : ℝ)|=(389306381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216382621/10000000000 : ℝ)|^4565 ≤ (2160763579489/5000000000000 : ℝ)^3541
        have hw : |(5216382621/10000000000 : ℝ)|=(5216382621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675504611/5000000000 : ℝ)*x 0 + (5216382281/10000000000 : ℝ)*x 1 + (-1946532107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675504611/5000000000 : ℝ)^4565 ≤ (44658454618541/100000000000000 : ℝ)^3541 := by
    have hnat : (2675504611 : ℕ)^4565*100000000000000^3541 ≤ 44658454618541^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675504611 5000000000 44658454618541 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216382281/10000000000 : ℝ)^4565 ≤ (10803816989621/25000000000000 : ℝ)^3541 := by
    have hnat : (5216382281 : ℕ)^4565*25000000000000^3541 ≤ 10803816989621^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216382281 10000000000 10803816989621 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1946532107/10000000000 : ℝ)^4565 ≤ (303156935113/2500000000000 : ℝ)^3541 := by
    have hnat : (1946532107 : ℕ)^4565*2500000000000^3541 ≤ 303156935113^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946532107 10000000000 303156935113 2500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675504611/5000000000 : ℝ), (5216382281/10000000000 : ℝ), (-1946532107/10000000000 : ℝ)] ![(44658454618541/100000000000000 : ℝ), (10803816989621/25000000000000 : ℝ), (303156935113/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675504611/5000000000 : ℝ)|^4565 ≤ (44658454618541/100000000000000 : ℝ)^3541
        have hw : |(2675504611/5000000000 : ℝ)|=(2675504611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216382281/10000000000 : ℝ)|^4565 ≤ (10803816989621/25000000000000 : ℝ)^3541
        have hw : |(5216382281/10000000000 : ℝ)|=(5216382281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1946532107/10000000000 : ℝ)|^4565 ≤ (303156935113/2500000000000 : ℝ)^3541
        have hw : |(-1946532107/10000000000 : ℝ)|=(1946532107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259394509/10000000000 : ℝ)*x 0 + (2008074437/5000000000 : ℝ)*x 1 + (2257404253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259394509/10000000000 : ℝ)^4565 ≤ (3327830954547/10000000000000 : ℝ)^3541 := by
    have hnat : (4259394509 : ℕ)^4565*10000000000000^3541 ≤ 3327830954547^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259394509 10000000000 3327830954547 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008074437/5000000000 : ℝ)^4565 ≤ (15424390173913/50000000000000 : ℝ)^3541 := by
    have hnat : (2008074437 : ℕ)^4565*50000000000000^3541 ≤ 15424390173913^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008074437 5000000000 15424390173913 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257404253/5000000000 : ℝ)^4565 ≤ (7174582017177/20000000000000 : ℝ)^3541 := by
    have hnat : (2257404253 : ℕ)^4565*20000000000000^3541 ≤ 7174582017177^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257404253 5000000000 7174582017177 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259394509/10000000000 : ℝ), (2008074437/5000000000 : ℝ), (2257404253/5000000000 : ℝ)] ![(3327830954547/10000000000000 : ℝ), (15424390173913/50000000000000 : ℝ), (7174582017177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259394509/10000000000 : ℝ)|^4565 ≤ (3327830954547/10000000000000 : ℝ)^3541
        have hw : |(4259394509/10000000000 : ℝ)|=(4259394509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008074437/5000000000 : ℝ)|^4565 ≤ (15424390173913/50000000000000 : ℝ)^3541
        have hw : |(2008074437/5000000000 : ℝ)|=(2008074437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257404253/5000000000 : ℝ)|^4565 ≤ (7174582017177/20000000000000 : ℝ)^3541
        have hw : |(2257404253/5000000000 : ℝ)|=(2257404253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835646891/10000000000 : ℝ)*x 0 + (652190939/1250000000 : ℝ)*x 1 + (1357943819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835646891/10000000000 : ℝ)^4565 ≤ (5621586014263/50000000000000 : ℝ)^3541 := by
    have hnat : (1835646891 : ℕ)^4565*50000000000000^3541 ≤ 5621586014263^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835646891 10000000000 5621586014263 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652190939/1250000000 : ℝ)^4565 ≤ (43227499734931/100000000000000 : ℝ)^3541 := by
    have hnat : (652190939 : ℕ)^4565*100000000000000^3541 ≤ 43227499734931^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652190939 1250000000 43227499734931 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357943819/2500000000 : ℝ)^4565 ≤ (22764664112187/50000000000000 : ℝ)^3541 := by
    have hnat : (1357943819 : ℕ)^4565*50000000000000^3541 ≤ 22764664112187^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357943819 2500000000 22764664112187 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835646891/10000000000 : ℝ), (652190939/1250000000 : ℝ), (1357943819/2500000000 : ℝ)] ![(5621586014263/50000000000000 : ℝ), (43227499734931/100000000000000 : ℝ), (22764664112187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835646891/10000000000 : ℝ)|^4565 ≤ (5621586014263/50000000000000 : ℝ)^3541
        have hw : |(-1835646891/10000000000 : ℝ)|=(1835646891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652190939/1250000000 : ℝ)|^4565 ≤ (43227499734931/100000000000000 : ℝ)^3541
        have hw : |(652190939/1250000000 : ℝ)|=(652190939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357943819/2500000000 : ℝ)|^4565 ≤ (22764664112187/50000000000000 : ℝ)^3541
        have hw : |(1357943819/2500000000 : ℝ)|=(1357943819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058796041/2000000000 : ℝ)*x 0 + (-216392447/1250000000 : ℝ)*x 1 + (5431775713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058796041/2000000000 : ℝ)^4565 ≤ (4404581191553/10000000000000 : ℝ)^3541 := by
    have hnat : (1058796041 : ℕ)^4565*10000000000000^3541 ≤ 4404581191553^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058796041 2000000000 4404581191553 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216392447/1250000000 : ℝ)^4565 ≤ (5212427555521/50000000000000 : ℝ)^3541 := by
    have hnat : (216392447 : ℕ)^4565*50000000000000^3541 ≤ 5212427555521^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216392447 1250000000 5212427555521 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431775713/10000000000 : ℝ)^4565 ≤ (45529332946589/100000000000000 : ℝ)^3541 := by
    have hnat : (5431775713 : ℕ)^4565*100000000000000^3541 ≤ 45529332946589^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431775713 10000000000 45529332946589 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058796041/2000000000 : ℝ), (-216392447/1250000000 : ℝ), (5431775713/10000000000 : ℝ)] ![(4404581191553/10000000000000 : ℝ), (5212427555521/50000000000000 : ℝ), (45529332946589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058796041/2000000000 : ℝ)|^4565 ≤ (4404581191553/10000000000000 : ℝ)^3541
        have hw : |(1058796041/2000000000 : ℝ)|=(1058796041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216392447/1250000000 : ℝ)|^4565 ≤ (5212427555521/50000000000000 : ℝ)^3541
        have hw : |(-216392447/1250000000 : ℝ)|=(216392447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431775713/10000000000 : ℝ)|^4565 ≤ (45529332946589/100000000000000 : ℝ)^3541
        have hw : |(5431775713/10000000000 : ℝ)|=(5431775713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661747673/1250000000 : ℝ)*x 0 + (2715887509/5000000000 : ℝ)*x 1 + (-432784729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661747673/1250000000 : ℝ)^4565 ≤ (22022912280733/50000000000000 : ℝ)^3541 := by
    have hnat : (661747673 : ℕ)^4565*50000000000000^3541 ≤ 22022912280733^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661747673 1250000000 22022912280733 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715887509/5000000000 : ℝ)^4565 ≤ (4552932543643/10000000000000 : ℝ)^3541 := by
    have hnat : (2715887509 : ℕ)^4565*10000000000000^3541 ≤ 4552932543643^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715887509 5000000000 4552932543643 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432784729/2500000000 : ℝ)^4565 ≤ (10424849987189/100000000000000 : ℝ)^3541 := by
    have hnat : (432784729 : ℕ)^4565*100000000000000^3541 ≤ 10424849987189^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432784729 2500000000 10424849987189 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661747673/1250000000 : ℝ), (2715887509/5000000000 : ℝ), (-432784729/2500000000 : ℝ)] ![(22022912280733/50000000000000 : ℝ), (4552932543643/10000000000000 : ℝ), (10424849987189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661747673/1250000000 : ℝ)|^4565 ≤ (22022912280733/50000000000000 : ℝ)^3541
        have hw : |(661747673/1250000000 : ℝ)|=(661747673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715887509/5000000000 : ℝ)|^4565 ≤ (4552932543643/10000000000000 : ℝ)^3541
        have hw : |(2715887509/5000000000 : ℝ)|=(2715887509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432784729/2500000000 : ℝ)|^4565 ≤ (10424849987189/100000000000000 : ℝ)^3541
        have hw : |(-432784729/2500000000 : ℝ)|=(432784729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s3_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212973181/500000000 : ℝ)*x 0 + (2256086189/5000000000 : ℝ)*x 1 + (4018804971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212973181/500000000 : ℝ)^4565 ≤ (4159875706647/12500000000000 : ℝ)^3541 := by
    have hnat : (212973181 : ℕ)^4565*12500000000000^3541 ≤ 4159875706647^3541*500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212973181 500000000 4159875706647 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256086189/5000000000 : ℝ)^4565 ≤ (8961477394217/25000000000000 : ℝ)^3541 := by
    have hnat : (2256086189 : ℕ)^4565*25000000000000^3541 ≤ 8961477394217^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256086189 5000000000 8961477394217 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018804971/10000000000 : ℝ)^4565 ≤ (30875084754061/100000000000000 : ℝ)^3541 := by
    have hnat : (4018804971 : ℕ)^4565*100000000000000^3541 ≤ 30875084754061^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018804971 10000000000 30875084754061 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212973181/500000000 : ℝ), (2256086189/5000000000 : ℝ), (4018804971/10000000000 : ℝ)] ![(4159875706647/12500000000000 : ℝ), (8961477394217/25000000000000 : ℝ), (30875084754061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212973181/500000000 : ℝ)|^4565 ≤ (4159875706647/12500000000000 : ℝ)^3541
        have hw : |(212973181/500000000 : ℝ)|=(212973181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256086189/5000000000 : ℝ)|^4565 ≤ (8961477394217/25000000000000 : ℝ)^3541
        have hw : |(2256086189/5000000000 : ℝ)|=(2256086189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018804971/10000000000 : ℝ)|^4565 ≤ (30875084754061/100000000000000 : ℝ)^3541
        have hw : |(4018804971/10000000000 : ℝ)|=(4018804971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10949/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15537/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7959/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5299/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7959/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5299/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7959/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5299/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7959/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5299/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7959/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5299/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7959/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5299/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5299/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (56657116911741/1250000000000000000 : ℝ) := by
    have hpowers : (5299/50000 : ℝ)^4563 ≤ (56657116911741/1250000000000000000 : ℝ)^1024 := by
      have hnat : (5299 : ℕ)^4563*1250000000000000000^1024 ≤ 56657116911741^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5299 50000 56657116911741 1250000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5299/50000 : ℝ)) (X := (56657116911741/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7959/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (13884860322729771/50000000000000000000 : ℝ) := by
    have hpowers : (7959/50000 : ℝ)^4563 ≤ (13884860322729771/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7959 : ℕ)^4563*50000000000000000000^1024 ≤ 13884860322729771^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7959 50000 13884860322729771 50000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7959/50000 : ℝ)) (X := (13884860322729771/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (625056657116911741/625000000000000000 : ℝ) ≤ (10000203427037659/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (625056657116911741/625000000000000000 : ℝ)^1024 ≤ (10000203427037659/10000000000000000 : ℝ)^4563 := by
      have hnat : (625056657116911741 : ℕ)^1024*10000000000000000^4563 ≤ 10000203427037659^4563*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625056657116911741 625000000000000000 10000203427037659 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000203427037659/10000000000000000 : ℝ)) (X := (625056657116911741/625000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016151144999199411/50000000000000000000 : ℝ) ≤ (2500181204263953/2500000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50016151144999199411/50000000000000000000 : ℝ)^1024 ≤ (2500181204263953/2500000000000000 : ℝ)^4563 := by
      have hnat : (50016151144999199411 : ℕ)^1024*2500000000000000^4563 ≤ 2500181204263953^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016151144999199411 50000000000000000000 2500181204263953 2500000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500181204263953/2500000000000000 : ℝ)) (X := (50016151144999199411/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013884860322729771/25000000000000000000 : ℝ) ≤ (2000249241414793/2000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (25013884860322729771/25000000000000000000 : ℝ)^1024 ≤ (2000249241414793/2000000000000000 : ℝ)^4563 := by
      have hnat : (25013884860322729771 : ℕ)^1024*2000000000000000^4563 ≤ 2000249241414793^4563*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013884860322729771 25000000000000000000 2000249241414793 2000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000249241414793/2000000000000000 : ℝ)) (X := (25013884860322729771/25000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(56657116911741/1250000000000000000 : ℝ) ≤ ((1899643958893413389/1900000000000000000 : ℝ)+2*(521390018153/532000000000000 : ℝ)*(5299/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (1899643958893413389/1900000000000000000 : ℝ)+2*(521390018153/532000000000000 : ℝ)*(5299/50000 : ℝ)=(10000203427037659/10000000000000000 : ℝ) by norm_num, show 1+2*(56657116911741/1250000000000000000 : ℝ)=(625056657116911741/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13884860322729771/50000000000000000000 : ℝ)+(56657116911741/1250000000000000000 : ℝ) ≤ ((1899643958893413389/1900000000000000000 : ℝ)+(521390018153/532000000000000 : ℝ)*((7959/50000 : ℝ)+(5299/50000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (1899643958893413389/1900000000000000000 : ℝ)+(521390018153/532000000000000 : ℝ)*((7959/50000 : ℝ)+(5299/50000 : ℝ))=(2500181204263953/2500000000000000 : ℝ) by norm_num, show 1+(13884860322729771/50000000000000000000 : ℝ)+(56657116911741/1250000000000000000 : ℝ)=(50016151144999199411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13884860322729771/50000000000000000000 : ℝ) ≤ ((1899643958893413389/1900000000000000000 : ℝ)+2*(521390018153/532000000000000 : ℝ)*(7959/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (1899643958893413389/1900000000000000000 : ℝ)+2*(521390018153/532000000000000 : ℝ)*(7959/50000 : ℝ)=(2000249241414793/2000000000000000 : ℝ) by norm_num, show 1+2*(13884860322729771/50000000000000000000 : ℝ)=(25013884860322729771/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1899643958893413389/1900000000000000000 : ℝ)*(X 1 0+X 2 0)+(521390018153/532000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5299/50000 : ℝ)) (hi := (7959/50000 : ℝ)) (c := (1899643958893413389/1900000000000000000 : ℝ)) (alpha := (521390018153/532000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1899643958893413389/1900000000000000000 : ℝ)*(X 0 1+X 2 1)+(521390018153/532000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5299/50000 : ℝ)) (hi := (7959/50000 : ℝ)) (c := (1899643958893413389/1900000000000000000 : ℝ)) (alpha := (521390018153/532000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1899643958893413389/1900000000000000000 : ℝ)*(X 0 2+X 1 2)+(521390018153/532000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5299/50000 : ℝ)) (hi := (7959/50000 : ℝ)) (c := (1899643958893413389/1900000000000000000 : ℝ)) (alpha := (521390018153/532000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1835616271/10000000000 : ℝ)*X 0 0+(217317163/400000000 : ℝ)*X 0 1+(5216382771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337752259/2500000000 : ℝ)*X 1 0+(-389306381/2000000000 : ℝ)*X 1 1+(5216382621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675504611/5000000000 : ℝ)*X 2 0+(5216382281/10000000000 : ℝ)*X 2 1+(-1946532107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259394509/10000000000 : ℝ)*X 0 0+(2008074437/5000000000 : ℝ)*X 0 1+(2257404253/5000000000 : ℝ)*X 0 2+(4259394509/10000000000 : ℝ)*X 1 0+(2008074437/5000000000 : ℝ)*X 1 1+(2257404253/5000000000 : ℝ)*X 1 2+(4259394509/10000000000 : ℝ)*X 2 0+(2008074437/5000000000 : ℝ)*X 2 1+(2257404253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1835646891/10000000000 : ℝ)*X 0 0+(652190939/1250000000 : ℝ)*X 0 1+(1357943819/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058796041/2000000000 : ℝ)*X 1 0+(-216392447/1250000000 : ℝ)*X 1 1+(5431775713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661747673/1250000000 : ℝ)*X 2 0+(2715887509/5000000000 : ℝ)*X 2 1+(-432784729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((212973181/500000000 : ℝ)*X 0 0+(2256086189/5000000000 : ℝ)*X 0 1+(4018804971/10000000000 : ℝ)*X 0 2+(212973181/500000000 : ℝ)*X 1 0+(2256086189/5000000000 : ℝ)*X 1 1+(4018804971/10000000000 : ℝ)*X 1 2+(212973181/500000000 : ℝ)*X 2 0+(2256086189/5000000000 : ℝ)*X 2 1+(4018804971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (457460256571187054246277849/47500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (903666501/100000000000000 : ℝ)*(base19) + (1135866863/100000000000000 : ℝ)*(base23) + (10473507/10000000000000 : ℝ)*(lower2) + (116653893/100000000000000 : ℝ)*(upper3) + (143091361/100000000000000 : ℝ)*(lower4) + (1655841575879953/50000000000000 : ℝ)*(major0) + (1655841575879953/50000000000000 : ℝ)*(major1) + (1655841575879953/50000000000000 : ℝ)*(major2) + (4617964560834061/100000000000000 : ℝ)*(sp0) + (577246886837897/12500000000000 : ℝ)*(sp1) + (2308987431251407/50000000000000 : ℝ)*(sp2) + (1002691102454061/50000000000000 : ℝ)*(sp3) + (89355747/781250000000 : ℝ)*(sp4) + (1555843453/20000000000000 : ℝ)*(sp7) + (2005389984125387/100000000000000 : ℝ)*(f.failure) + (4617975998369677/100000000000000 : ℝ)*(f.sum) + (9994302305787/1900000000000000000000000000 : ℝ)*base65 + (671020061459065717/95000000000000000000000000000000 : ℝ)*base67 + (145823314795934283/95000000000000000000000000000000 : ℝ)*base70 + (576927504404065717/95000000000000000000000000000000 : ℝ)*base71 + (1779261842487/1900000000000000000000000000 : ℝ)*base73 + (325497883450934283/95000000000000000000000000000000 : ℝ)*base76 + (652827529064065717/95000000000000000000000000000000 : ℝ)*base77 + (856731023594065717/95000000000000000000000000000000 : ℝ)*base79 + (3821235976413/1900000000000000000000000000 : ℝ)*base82 + (46539817/10000000000000000000000 : ℝ)*base90 + (46539817/10000000000000000000000 : ℝ)*base92 + (46539817/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3495047931203920384887207057/665000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1206653707/100000000000000 : ℝ)*(base23) + (3672653/25000000000000 : ℝ)*(upper2) + (186368889/100000000000000 : ℝ)*(upper3) + (719617/1562500000000 : ℝ)*(upper4) + (3347194636287349/100000000000000 : ℝ)*(major0) + (3347194636287349/100000000000000 : ℝ)*(major1) + (3347194636287349/100000000000000 : ℝ)*(major2) + (817140517/100000000000000 : ℝ)*(sp1) + (21836261549/100000000000000 : ℝ)*(sp2) + (461006707/50000000000000 : ℝ)*(sp3) + (2333747565552821/50000000000000 : ℝ)*(sp4) + (37339954511721/800000000000 : ℝ)*(sp5) + (2333736044095193/50000000000000 : ℝ)*(sp6) + (2026893044265251/100000000000000 : ℝ)*(sp7) + (1013446983139333/50000000000000 : ℝ)*(f.failure) + (2333747565552821/50000000000000 : ℝ)*(f.sum) + (43562404172003/26600000000000000000000000000 : ℝ)*base66 + (9399925264155335327/1330000000000000000000000000000000 : ℝ)*base67 + (95639899672085335327/1330000000000000000000000000000000 : ℝ)*base69 + (3678771774705335327/1330000000000000000000000000000000 : ℝ)*base71 + (41938042194997/26600000000000000000000000000 : ℝ)*base73 + (16188283875385335327/1330000000000000000000000000000000 : ℝ)*base75 + (62896068344255335327/1330000000000000000000000000000000 : ℝ)*base77 + (16217016471865335327/1330000000000000000000000000000000 : ℝ)*base79 + (95178047078797/26600000000000000000000000000 : ℝ)*base81 + (24474297/5000000000000000000000 : ℝ)*base89 + (24474297/5000000000000000000000 : ℝ)*base91 + (24474297/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1534_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10949/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15537/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1534_s4_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91797849/500000000 : ℝ)*x 0 + (2715335579/5000000000 : ℝ)*x 1 + (5218415253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91797849/500000000 : ℝ)^4565 ≤ (1405702574119/12500000000000 : ℝ)^3541 := by
    have hnat : (91797849 : ℕ)^4565*12500000000000^3541 ≤ 1405702574119^3541*500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91797849 500000000 1405702574119 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715335579/5000000000 : ℝ)^4565 ≤ (45517397494073/100000000000000 : ℝ)^3541 := by
    have hnat : (2715335579 : ℕ)^4565*100000000000000^3541 ≤ 45517397494073^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715335579 5000000000 45517397494073 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218415253/10000000000 : ℝ)^4565 ≤ (1351155684153/3125000000000 : ℝ)^3541 := by
    have hnat : (5218415253 : ℕ)^4565*3125000000000^3541 ≤ 1351155684153^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218415253 10000000000 1351155684153 3125000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91797849/500000000 : ℝ), (2715335579/5000000000 : ℝ), (5218415253/10000000000 : ℝ)] ![(1405702574119/12500000000000 : ℝ), (45517397494073/100000000000000 : ℝ), (1351155684153/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91797849/500000000 : ℝ)|^4565 ≤ (1405702574119/12500000000000 : ℝ)^3541
        have hw : |(-91797849/500000000 : ℝ)|=(91797849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715335579/5000000000 : ℝ)|^4565 ≤ (45517397494073/100000000000000 : ℝ)^3541
        have hw : |(2715335579/5000000000 : ℝ)|=(2715335579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218415253/10000000000 : ℝ)|^4565 ≤ (1351155684153/3125000000000 : ℝ)^3541
        have hw : |(5218415253/10000000000 : ℝ)|=(5218415253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675207903/5000000000 : ℝ)*x 0 + (-1944623319/10000000000 : ℝ)*x 1 + (2609207551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675207903/5000000000 : ℝ)^4565 ≤ (5581508749671/12500000000000 : ℝ)^3541 := by
    have hnat : (2675207903 : ℕ)^4565*12500000000000^3541 ≤ 5581508749671^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675207903 5000000000 5581508749671 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944623319/10000000000 : ℝ)^4565 ≤ (378467178387/3125000000000 : ℝ)^3541 := by
    have hnat : (1944623319 : ℕ)^4565*3125000000000^3541 ≤ 378467178387^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944623319 10000000000 378467178387 3125000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609207551/5000000000 : ℝ)^4565 ≤ (5404622534999/12500000000000 : ℝ)^3541 := by
    have hnat : (2609207551 : ℕ)^4565*12500000000000^3541 ≤ 5404622534999^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609207551 5000000000 5404622534999 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675207903/5000000000 : ℝ), (-1944623319/10000000000 : ℝ), (2609207551/5000000000 : ℝ)] ![(5581508749671/12500000000000 : ℝ), (378467178387/3125000000000 : ℝ), (5404622534999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675207903/5000000000 : ℝ)|^4565 ≤ (5581508749671/12500000000000 : ℝ)^3541
        have hw : |(2675207903/5000000000 : ℝ)|=(2675207903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944623319/10000000000 : ℝ)|^4565 ≤ (378467178387/3125000000000 : ℝ)^3541
        have hw : |(-1944623319/10000000000 : ℝ)|=(1944623319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609207551/5000000000 : ℝ)|^4565 ≤ (5404622534999/12500000000000 : ℝ)^3541
        have hw : |(2609207551/5000000000 : ℝ)|=(2609207551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337603943/2500000000 : ℝ)*x 0 + (2609207661/5000000000 : ℝ)*x 1 + (-60769471/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337603943/2500000000 : ℝ)^4565 ≤ (8930413926313/20000000000000 : ℝ)^3541 := by
    have hnat : (1337603943 : ℕ)^4565*20000000000000^3541 ≤ 8930413926313^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337603943 2500000000 8930413926313 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609207661/5000000000 : ℝ)^4565 ≤ (43236982629919/100000000000000 : ℝ)^3541 := by
    have hnat : (2609207661 : ℕ)^4565*100000000000000^3541 ≤ 43236982629919^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609207661 5000000000 43236982629919 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60769471/312500000 : ℝ)^4565 ≤ (12110947725239/100000000000000 : ℝ)^3541 := by
    have hnat : (60769471 : ℕ)^4565*100000000000000^3541 ≤ 12110947725239^3541*312500000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60769471 312500000 12110947725239 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337603943/2500000000 : ℝ), (2609207661/5000000000 : ℝ), (-60769471/312500000 : ℝ)] ![(8930413926313/20000000000000 : ℝ), (43236982629919/100000000000000 : ℝ), (12110947725239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337603943/2500000000 : ℝ)|^4565 ≤ (8930413926313/20000000000000 : ℝ)^3541
        have hw : |(1337603943/2500000000 : ℝ)|=(1337603943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609207661/5000000000 : ℝ)|^4565 ≤ (43236982629919/100000000000000 : ℝ)^3541
        have hw : |(2609207661/5000000000 : ℝ)|=(2609207661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60769471/312500000 : ℝ)|^4565 ≤ (12110947725239/100000000000000 : ℝ)^3541
        have hw : |(-60769471/312500000 : ℝ)|=(60769471/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259609037/10000000000 : ℝ)*x 0 + (4021064803/10000000000 : ℝ)*x 1 + (11274609/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259609037/10000000000 : ℝ)^4565 ≤ (6656094069911/20000000000000 : ℝ)^3541 := by
    have hnat : (4259609037 : ℕ)^4565*20000000000000^3541 ≤ 6656094069911^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259609037 10000000000 6656094069911 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021064803/10000000000 : ℝ)^4565 ≤ (30897468746041/100000000000000 : ℝ)^3541 := by
    have hnat : (4021064803 : ℕ)^4565*100000000000000^3541 ≤ 30897468746041^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021064803 10000000000 30897468746041 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11274609/25000000 : ℝ)^4565 ≤ (4477757611379/12500000000000 : ℝ)^3541 := by
    have hnat : (11274609 : ℕ)^4565*12500000000000^3541 ≤ 4477757611379^3541*25000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11274609 25000000 4477757611379 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259609037/10000000000 : ℝ), (4021064803/10000000000 : ℝ), (11274609/25000000 : ℝ)] ![(6656094069911/20000000000000 : ℝ), (30897468746041/100000000000000 : ℝ), (4477757611379/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259609037/10000000000 : ℝ)|^4565 ≤ (6656094069911/20000000000000 : ℝ)^3541
        have hw : |(4259609037/10000000000 : ℝ)|=(4259609037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021064803/10000000000 : ℝ)|^4565 ≤ (30897468746041/100000000000000 : ℝ)^3541
        have hw : |(4021064803/10000000000 : ℝ)|=(4021064803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11274609/25000000 : ℝ)|^4565 ≤ (4477757611379/12500000000000 : ℝ)^3541
        have hw : |(11274609/25000000 : ℝ)|=(11274609/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835985387/10000000000 : ℝ)*x 0 + (1304878869/2500000000 : ℝ)*x 1 + (5429562723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835985387/10000000000 : ℝ)^4565 ≤ (11245844909919/100000000000000 : ℝ)^3541 := by
    have hnat : (1835985387 : ℕ)^4565*100000000000000^3541 ≤ 11245844909919^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835985387 10000000000 11245844909919 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304878869/2500000000 : ℝ)^4565 ≤ (43248734265423/100000000000000 : ℝ)^3541 := by
    have hnat : (1304878869 : ℕ)^4565*100000000000000^3541 ≤ 43248734265423^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304878869 2500000000 43248734265423 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429562723/10000000000 : ℝ)^4565 ≤ (5688177602659/12500000000000 : ℝ)^3541 := by
    have hnat : (5429562723 : ℕ)^4565*12500000000000^3541 ≤ 5688177602659^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429562723 10000000000 5688177602659 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835985387/10000000000 : ℝ), (1304878869/2500000000 : ℝ), (5429562723/10000000000 : ℝ)] ![(11245844909919/100000000000000 : ℝ), (43248734265423/100000000000000 : ℝ), (5688177602659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835985387/10000000000 : ℝ)|^4565 ≤ (11245844909919/100000000000000 : ℝ)^3541
        have hw : |(-1835985387/10000000000 : ℝ)|=(1835985387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304878869/2500000000 : ℝ)|^4565 ≤ (43248734265423/100000000000000 : ℝ)^3541
        have hw : |(1304878869/2500000000 : ℝ)|=(1304878869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429562723/10000000000 : ℝ)|^4565 ≤ (5688177602659/12500000000000 : ℝ)^3541
        have hw : |(5429562723/10000000000 : ℝ)|=(5429562723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294518183/10000000000 : ℝ)*x 0 + (-69339039/400000000 : ℝ)*x 1 + (2714781349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294518183/10000000000 : ℝ)^4565 ≤ (44051582343963/100000000000000 : ℝ)^3541 := by
    have hnat : (5294518183 : ℕ)^4565*100000000000000^3541 ≤ 44051582343963^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294518183 10000000000 44051582343963 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69339039/400000000 : ℝ)^4565 ≤ (26107492711/250000000000 : ℝ)^3541 := by
    have hnat : (69339039 : ℕ)^4565*250000000000^3541 ≤ 26107492711^3541*400000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69339039 400000000 26107492711 250000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714781349/5000000000 : ℝ)^4565 ≤ (22752710275577/50000000000000 : ℝ)^3541 := by
    have hnat : (2714781349 : ℕ)^4565*50000000000000^3541 ≤ 22752710275577^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714781349 5000000000 22752710275577 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294518183/10000000000 : ℝ), (-69339039/400000000 : ℝ), (2714781349/5000000000 : ℝ)] ![(44051582343963/100000000000000 : ℝ), (26107492711/250000000000 : ℝ), (22752710275577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294518183/10000000000 : ℝ)|^4565 ≤ (44051582343963/100000000000000 : ℝ)^3541
        have hw : |(5294518183/10000000000 : ℝ)|=(5294518183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69339039/400000000 : ℝ)|^4565 ≤ (26107492711/250000000000 : ℝ)^3541
        have hw : |(-69339039/400000000 : ℝ)|=(69339039/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714781349/5000000000 : ℝ)|^4565 ≤ (22752710275577/50000000000000 : ℝ)^3541
        have hw : |(2714781349/5000000000 : ℝ)|=(2714781349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294518159/10000000000 : ℝ)*x 0 + (1085912539/2000000000 : ℝ)*x 1 + (-433369003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294518159/10000000000 : ℝ)^4565 ≤ (11012895521633/25000000000000 : ℝ)^3541 := by
    have hnat : (5294518159 : ℕ)^4565*25000000000000^3541 ≤ 11012895521633^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294518159 10000000000 11012895521633 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085912539/2000000000 : ℝ)^4565 ≤ (2275271025937/5000000000000 : ℝ)^3541 := by
    have hnat : (1085912539 : ℕ)^4565*5000000000000^3541 ≤ 2275271025937^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085912539 2000000000 2275271025937 5000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433369003/2500000000 : ℝ)^4565 ≤ (5221498685879/50000000000000 : ℝ)^3541 := by
    have hnat : (433369003 : ℕ)^4565*50000000000000^3541 ≤ 5221498685879^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433369003 2500000000 5221498685879 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294518159/10000000000 : ℝ), (1085912539/2000000000 : ℝ), (-433369003/2500000000 : ℝ)] ![(11012895521633/25000000000000 : ℝ), (2275271025937/5000000000000 : ℝ), (5221498685879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294518159/10000000000 : ℝ)|^4565 ≤ (11012895521633/25000000000000 : ℝ)^3541
        have hw : |(5294518159/10000000000 : ℝ)|=(5294518159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085912539/2000000000 : ℝ)|^4565 ≤ (2275271025937/5000000000000 : ℝ)^3541
        have hw : |(1085912539/2000000000 : ℝ)|=(1085912539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433369003/2500000000 : ℝ)|^4565 ≤ (5221498685879/50000000000000 : ℝ)^3541
        have hw : |(-433369003/2500000000 : ℝ)|=(433369003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s4_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129837053/5000000000 : ℝ)*x 0 + (2253655073/5000000000 : ℝ)*x 1 + (4023617101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129837053/5000000000 : ℝ)^4565 ≤ (33281125754423/100000000000000 : ℝ)^3541 := by
    have hnat : (2129837053 : ℕ)^4565*100000000000000^3541 ≤ 33281125754423^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129837053 5000000000 33281125754423 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253655073/5000000000 : ℝ)^4565 ≤ (17898060095761/50000000000000 : ℝ)^3541 := by
    have hnat : (2253655073 : ℕ)^4565*50000000000000^3541 ≤ 17898060095761^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253655073 5000000000 17898060095761 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023617101/10000000000 : ℝ)^4565 ≤ (30922754034653/100000000000000 : ℝ)^3541 := by
    have hnat : (4023617101 : ℕ)^4565*100000000000000^3541 ≤ 30922754034653^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023617101 10000000000 30922754034653 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129837053/5000000000 : ℝ), (2253655073/5000000000 : ℝ), (4023617101/10000000000 : ℝ)] ![(33281125754423/100000000000000 : ℝ), (17898060095761/50000000000000 : ℝ), (30922754034653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129837053/5000000000 : ℝ)|^4565 ≤ (33281125754423/100000000000000 : ℝ)^3541
        have hw : |(2129837053/5000000000 : ℝ)|=(2129837053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253655073/5000000000 : ℝ)|^4565 ≤ (17898060095761/50000000000000 : ℝ)^3541
        have hw : |(2253655073/5000000000 : ℝ)|=(2253655073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023617101/10000000000 : ℝ)|^4565 ≤ (30922754034653/100000000000000 : ℝ)^3541
        have hw : |(4023617101/10000000000 : ℝ)|=(4023617101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10993/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10949/100000 : ℝ) ^ (4563/1024 : ℝ) ≤ (8188796276131/156250000000000000 : ℝ) := by
    have hpowers : (10949/100000 : ℝ)^4563 ≤ (8188796276131/156250000000000000 : ℝ)^1024 := by
      have hnat : (10949 : ℕ)^4563*156250000000000000^1024 ≤ 8188796276131^1024*100000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10949 100000 8188796276131 156250000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10949/100000 : ℝ)) (X := (8188796276131/156250000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15537/100000 : ℝ) ^ (4563/1024 : ℝ) ≤ (1246401241038061/5000000000000000000 : ℝ) := by
    have hpowers : (15537/100000 : ℝ)^4563 ≤ (1246401241038061/5000000000000000000 : ℝ)^1024 := by
      have hnat : (15537 : ℕ)^4563*5000000000000000000^1024 ≤ 1246401241038061^1024*100000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15537 100000 1246401241038061 5000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15537/100000 : ℝ)) (X := (1246401241038061/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (78133188796276131/78125000000000000 : ℝ) ≤ (10000235213298429/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (78133188796276131/78125000000000000 : ℝ)^1024 ≤ (10000235213298429/10000000000000000 : ℝ)^4563 := by
      have hnat : (78133188796276131 : ℕ)^1024*10000000000000000^4563 ≤ 10000235213298429^4563*78125000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78133188796276131 78125000000000000 10000235213298429 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000235213298429/10000000000000000 : ℝ)) (X := (78133188796276131/78125000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001508442721874253/5000000000000000000 : ℝ) ≤ (2500169237855267/2500000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (5001508442721874253/5000000000000000000 : ℝ)^1024 ≤ (2500169237855267/2500000000000000 : ℝ)^4563 := by
      have hnat : (5001508442721874253 : ℕ)^1024*2500000000000000^4563 ≤ 2500169237855267^4563*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001508442721874253 5000000000000000000 2500169237855267 2500000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500169237855267/2500000000000000 : ℝ)) (X := (5001508442721874253/5000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501246401241038061/2500000000000000000 : ℝ) ≤ (10001118689543707/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (2501246401241038061/2500000000000000000 : ℝ)^1024 ≤ (10001118689543707/10000000000000000 : ℝ)^4563 := by
      have hnat : (2501246401241038061 : ℕ)^1024*10000000000000000^4563 ≤ 10001118689543707^4563*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501246401241038061 2500000000000000000 10001118689543707 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001118689543707/10000000000000000 : ℝ)) (X := (2501246401241038061/2500000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8188796276131/156250000000000000 : ℝ) ≤ ((4587140597720364343/4588000000000000000 : ℝ)+2*(441738122639/458800000000000 : ℝ)*(10949/100000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (4587140597720364343/4588000000000000000 : ℝ)+2*(441738122639/458800000000000 : ℝ)*(10949/100000 : ℝ)=(10000235213298429/10000000000000000 : ℝ) by norm_num, show 1+2*(8188796276131/156250000000000000 : ℝ)=(78133188796276131/78125000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1246401241038061/5000000000000000000 : ℝ)+(8188796276131/156250000000000000 : ℝ) ≤ ((4587140597720364343/4588000000000000000 : ℝ)+(441738122639/458800000000000 : ℝ)*((15537/100000 : ℝ)+(10949/100000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (4587140597720364343/4588000000000000000 : ℝ)+(441738122639/458800000000000 : ℝ)*((15537/100000 : ℝ)+(10949/100000 : ℝ))=(2500169237855267/2500000000000000 : ℝ) by norm_num, show 1+(1246401241038061/5000000000000000000 : ℝ)+(8188796276131/156250000000000000 : ℝ)=(5001508442721874253/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1246401241038061/5000000000000000000 : ℝ) ≤ ((4587140597720364343/4588000000000000000 : ℝ)+2*(441738122639/458800000000000 : ℝ)*(15537/100000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (4587140597720364343/4588000000000000000 : ℝ)+2*(441738122639/458800000000000 : ℝ)*(15537/100000 : ℝ)=(10001118689543707/10000000000000000 : ℝ) by norm_num, show 1+2*(1246401241038061/5000000000000000000 : ℝ)=(2501246401241038061/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4587140597720364343/4588000000000000000 : ℝ)*(X 1 0+X 2 0)+(441738122639/458800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (10949/100000 : ℝ)) (hi := (15537/100000 : ℝ)) (c := (4587140597720364343/4588000000000000000 : ℝ)) (alpha := (441738122639/458800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4587140597720364343/4588000000000000000 : ℝ)*(X 0 1+X 2 1)+(441738122639/458800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (10949/100000 : ℝ)) (hi := (15537/100000 : ℝ)) (c := (4587140597720364343/4588000000000000000 : ℝ)) (alpha := (441738122639/458800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4587140597720364343/4588000000000000000 : ℝ)*(X 0 2+X 1 2)+(441738122639/458800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (10949/100000 : ℝ)) (hi := (15537/100000 : ℝ)) (c := (4587140597720364343/4588000000000000000 : ℝ)) (alpha := (441738122639/458800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-91797849/500000000 : ℝ)*X 0 0+(2715335579/5000000000 : ℝ)*X 0 1+(5218415253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675207903/5000000000 : ℝ)*X 1 0+(-1944623319/10000000000 : ℝ)*X 1 1+(2609207551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337603943/2500000000 : ℝ)*X 2 0+(2609207661/5000000000 : ℝ)*X 2 1+(-60769471/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259609037/10000000000 : ℝ)*X 0 0+(4021064803/10000000000 : ℝ)*X 0 1+(11274609/25000000 : ℝ)*X 0 2+(4259609037/10000000000 : ℝ)*X 1 0+(4021064803/10000000000 : ℝ)*X 1 1+(11274609/25000000 : ℝ)*X 1 2+(4259609037/10000000000 : ℝ)*X 2 0+(4021064803/10000000000 : ℝ)*X 2 1+(11274609/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1835985387/10000000000 : ℝ)*X 0 0+(1304878869/2500000000 : ℝ)*X 0 1+(5429562723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294518183/10000000000 : ℝ)*X 1 0+(-69339039/400000000 : ℝ)*X 1 1+(2714781349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294518159/10000000000 : ℝ)*X 2 0+(1085912539/2000000000 : ℝ)*X 2 1+(-433369003/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2129837053/5000000000 : ℝ)*X 0 0+(2253655073/5000000000 : ℝ)*X 0 1+(4023617101/10000000000 : ℝ)*X 0 2+(2129837053/5000000000 : ℝ)*X 1 0+(2253655073/5000000000 : ℝ)*X 1 1+(4023617101/10000000000 : ℝ)*X 1 2+(2129837053/5000000000 : ℝ)*X 2 0+(2253655073/5000000000 : ℝ)*X 2 1+(4023617101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78763537668486813938465907/28675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469326491/50000000000000 : ℝ)*(base19) + (142105159/20000000000000 : ℝ)*(base23) + (106552447/100000000000000 : ℝ)*(lower2) + (88042589/100000000000000 : ℝ)*(upper5) + (422328315590583/12500000000000 : ℝ)*(major0) + (422328315590583/12500000000000 : ℝ)*(major1) + (422328315590583/12500000000000 : ℝ)*(major2) + (1177826857530579/25000000000000 : ℝ)*(sp0) + (588915547334713/12500000000000 : ℝ)*(sp1) + (2355662349327489/50000000000000 : ℝ)*(sp2) + (409184311503963/20000000000000 : ℝ)*(sp3) + (2247382307/12500000000000 : ℝ)*(sp4) + (91850087/100000000000000 : ℝ)*(sp5) + (74889873/1250000000000 : ℝ)*(sp7) + (1022963774354827/50000000000000 : ℝ)*(f.failure) + (4711325409180773/100000000000000 : ℝ)*(f.sum) + (26795505934531/5735000000000000000000000000 : ℝ)*base66 + (677650068858001969/57350000000000000000000000000000 : ℝ)*base67 + (348535944616551969/57350000000000000000000000000000 : ℝ)*base69 + (228586457103848031/57350000000000000000000000000000 : ℝ)*base72 + (8092308157167/2867500000000000000000000000 : ℝ)*base73 + (266366104183748031/57350000000000000000000000000000 : ℝ)*base76 + (164612054435698031/57350000000000000000000000000000 : ℝ)*base78 + (72071910342198031/57350000000000000000000000000000 : ℝ)*base80 + (8281652319783/2867500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19370857/5000000000000000000000 : ℝ)*base90 + (19370857/5000000000000000000000 : ℝ)*base92 + (19370857/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90639494662953162753110343/14337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (969236981/100000000000000 : ℝ)*(base19) + (1064774571/100000000000000 : ℝ)*(base23) + (32108269/25000000000000 : ℝ)*(upper3) + (57826741/100000000000000 : ℝ)*(lower4) + (66145947/50000000000000 : ℝ)*(upper5) + (213383100745667/6250000000000 : ℝ)*(major0) + (213383100745667/6250000000000 : ℝ)*(major1) + (213383100745667/6250000000000 : ℝ)*(major2) + (3583376423/25000000000000 : ℝ)*(sp1) + (15081627007/100000000000000 : ℝ)*(sp2) + (4760832567268773/100000000000000 : ℝ)*(sp4) + (4760817264526101/100000000000000 : ℝ)*(sp5) + (952163284173439/20000000000000 : ℝ)*(sp6) + (20674264458643/1000000000000 : ℝ)*(sp7) + (20674264458643/1000000000000 : ℝ)*(f.failure) + (4760832567268773/100000000000000 : ℝ)*(f.sum) + (51046843626163/5735000000000000000000000000 : ℝ)*base66 + (65163719828218219/28675000000000000000000000000000 : ℝ)*base68 + (211600944612856781/28675000000000000000000000000000 : ℝ)*base69 + (389683262382943219/28675000000000000000000000000000 : ℝ)*base72 + (15675869408243/5735000000000000000000000000 : ℝ)*base74 + (206193581808168219/28675000000000000000000000000000 : ℝ)*base76 + (207266853422393219/28675000000000000000000000000000 : ℝ)*base78 + (112218085842856781/28675000000000000000000000000000 : ℝ)*base79 + (781109058923/1433750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (369087/100000000000000000000 : ℝ)*base89 + (369087/100000000000000000000 : ℝ)*base91 + (369087/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1534_s5_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835995033/10000000000 : ℝ)*x 0 + (1086082539/2000000000 : ℝ)*x 1 + (5218648579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835995033/10000000000 : ℝ)^4565 ≤ (11245921080157/100000000000000 : ℝ)^3541 := by
    have hnat : (1835995033 : ℕ)^4565*100000000000000^3541 ≤ 11245921080157^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835995033 10000000000 11245921080157 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086082539/2000000000 : ℝ)^4565 ≤ (9102920946109/20000000000000 : ℝ)^3541 := by
    have hnat : (1086082539 : ℕ)^4565*20000000000000^3541 ≤ 9102920946109^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086082539 2000000000 9102920946109 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218648579/10000000000 : ℝ)^4565 ≤ (21619737088463/50000000000000 : ℝ)^3541 := by
    have hnat : (5218648579 : ℕ)^4565*50000000000000^3541 ≤ 21619737088463^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218648579 10000000000 21619737088463 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835995033/10000000000 : ℝ), (1086082539/2000000000 : ℝ), (5218648579/10000000000 : ℝ)] ![(11245921080157/100000000000000 : ℝ), (9102920946109/20000000000000 : ℝ), (21619737088463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835995033/10000000000 : ℝ)|^4565 ≤ (11245921080157/100000000000000 : ℝ)^3541
        have hw : |(-1835995033/10000000000 : ℝ)|=(1835995033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086082539/2000000000 : ℝ)|^4565 ≤ (9102920946109/20000000000000 : ℝ)^3541
        have hw : |(1086082539/2000000000 : ℝ)|=(1086082539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218648579/10000000000 : ℝ)|^4565 ≤ (21619737088463/50000000000000 : ℝ)^3541
        have hw : |(5218648579/10000000000 : ℝ)|=(5218648579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675173953/5000000000 : ℝ)*x 0 + (-388880759/2000000000 : ℝ)*x 1 + (10437297/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675173953/5000000000 : ℝ)^4565 ≤ (22325669733819/50000000000000 : ℝ)^3541 := by
    have hnat : (2675173953 : ℕ)^4565*50000000000000^3541 ≤ 22325669733819^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675173953 5000000000 22325669733819 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388880759/2000000000 : ℝ)^4565 ≤ (12109187194751/100000000000000 : ℝ)^3541 := by
    have hnat : (388880759 : ℕ)^4565*100000000000000^3541 ≤ 12109187194751^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388880759 2000000000 12109187194751 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10437297/20000000 : ℝ)^4565 ≤ (21619736666539/50000000000000 : ℝ)^3541 := by
    have hnat : (10437297 : ℕ)^4565*50000000000000^3541 ≤ 21619736666539^3541*20000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10437297 20000000 21619736666539 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675173953/5000000000 : ℝ), (-388880759/2000000000 : ℝ), (10437297/20000000 : ℝ)] ![(22325669733819/50000000000000 : ℝ), (12109187194751/100000000000000 : ℝ), (21619736666539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675173953/5000000000 : ℝ)|^4565 ≤ (22325669733819/50000000000000 : ℝ)^3541
        have hw : |(2675173953/5000000000 : ℝ)|=(2675173953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-388880759/2000000000 : ℝ)|^4565 ≤ (12109187194751/100000000000000 : ℝ)^3541
        have hw : |(-388880759/2000000000 : ℝ)|=(388880759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10437297/20000000 : ℝ)|^4565 ≤ (21619736666539/50000000000000 : ℝ)^3541
        have hw : |(10437297/20000000 : ℝ)|=(10437297/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337586967/2500000000 : ℝ)*x 0 + (260932427/500000000 : ℝ)*x 1 + (-1944403791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337586967/2500000000 : ℝ)^4565 ≤ (111628347647/250000000000 : ℝ)^3541 := by
    have hnat : (1337586967 : ℕ)^4565*250000000000^3541 ≤ 111628347647^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337586967 2500000000 111628347647 250000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260932427/500000000 : ℝ)^4565 ≤ (43239473760343/100000000000000 : ℝ)^3541 := by
    have hnat : (260932427 : ℕ)^4565*100000000000000^3541 ≤ 43239473760343^3541*500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260932427 500000000 43239473760343 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944403791/10000000000 : ℝ)^4565 ≤ (3027296790659/25000000000000 : ℝ)^3541 := by
    have hnat : (1944403791 : ℕ)^4565*25000000000000^3541 ≤ 3027296790659^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944403791 10000000000 3027296790659 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337586967/2500000000 : ℝ), (260932427/500000000 : ℝ), (-1944403791/10000000000 : ℝ)] ![(111628347647/250000000000 : ℝ), (43239473760343/100000000000000 : ℝ), (3027296790659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337586967/2500000000 : ℝ)|^4565 ≤ (111628347647/250000000000 : ℝ)^3541
        have hw : |(1337586967/2500000000 : ℝ)|=(1337586967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260932427/500000000 : ℝ)|^4565 ≤ (43239473760343/100000000000000 : ℝ)^3541
        have hw : |(260932427/500000000 : ℝ)|=(260932427/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944403791/10000000000 : ℝ)|^4565 ≤ (3027296790659/25000000000000 : ℝ)^3541
        have hw : |(-1944403791/10000000000 : ℝ)|=(1944403791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266227071/625000000 : ℝ)*x 0 + (2010814101/5000000000 : ℝ)*x 1 + (4509274859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266227071/625000000 : ℝ)^4565 ≤ (33280713085419/100000000000000 : ℝ)^3541 := by
    have hnat : (266227071 : ℕ)^4565*100000000000000^3541 ≤ 33280713085419^3541*625000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266227071 625000000 33280713085419 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010814101/5000000000 : ℝ)^4565 ≤ (30903049868533/100000000000000 : ℝ)^3541 := by
    have hnat : (2010814101 : ℕ)^4565*100000000000000^3541 ≤ 30903049868533^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010814101 5000000000 30903049868533 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509274859/10000000000 : ℝ)^4565 ≤ (716324740719/2000000000000 : ℝ)^3541 := by
    have hnat : (4509274859 : ℕ)^4565*2000000000000^3541 ≤ 716324740719^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509274859 10000000000 716324740719 2000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266227071/625000000 : ℝ), (2010814101/5000000000 : ℝ), (4509274859/10000000000 : ℝ)] ![(33280713085419/100000000000000 : ℝ), (30903049868533/100000000000000 : ℝ), (716324740719/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266227071/625000000 : ℝ)|^4565 ≤ (33280713085419/100000000000000 : ℝ)^3541
        have hw : |(266227071/625000000 : ℝ)|=(266227071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010814101/5000000000 : ℝ)|^4565 ≤ (30903049868533/100000000000000 : ℝ)^3541
        have hw : |(2010814101/5000000000 : ℝ)|=(2010814101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509274859/10000000000 : ℝ)|^4565 ≤ (716324740719/2000000000000 : ℝ)^3541
        have hw : |(4509274859/10000000000 : ℝ)|=(4509274859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367204629/2000000000 : ℝ)*x 0 + (521974373/1000000000 : ℝ)*x 1 + (5429309459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367204629/2000000000 : ℝ)^4565 ≤ (11246143068971/100000000000000 : ℝ)^3541 := by
    have hnat : (367204629 : ℕ)^4565*100000000000000^3541 ≤ 11246143068971^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367204629 2000000000 11246143068971 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521974373/1000000000 : ℝ)^4565 ≤ (43251172520911/100000000000000 : ℝ)^3541 := by
    have hnat : (521974373 : ℕ)^4565*100000000000000^3541 ≤ 43251172520911^3541*1000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521974373 1000000000 43251172520911 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429309459/10000000000 : ℝ)^4565 ≤ (11375671098881/25000000000000 : ℝ)^3541 := by
    have hnat : (5429309459 : ℕ)^4565*25000000000000^3541 ≤ 11375671098881^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429309459 10000000000 11375671098881 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367204629/2000000000 : ℝ), (521974373/1000000000 : ℝ), (5429309459/10000000000 : ℝ)] ![(11246143068971/100000000000000 : ℝ), (43251172520911/100000000000000 : ℝ), (11375671098881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367204629/2000000000 : ℝ)|^4565 ≤ (11246143068971/100000000000000 : ℝ)^3541
        have hw : |(-367204629/2000000000 : ℝ)|=(367204629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521974373/1000000000 : ℝ)|^4565 ≤ (43251172520911/100000000000000 : ℝ)^3541
        have hw : |(521974373/1000000000 : ℝ)|=(521974373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429309459/10000000000 : ℝ)|^4565 ≤ (11375671098881/25000000000000 : ℝ)^3541
        have hw : |(5429309459/10000000000 : ℝ)|=(5429309459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294580019/10000000000 : ℝ)*x 0 + (-108358929/625000000 : ℝ)*x 1 + (678663683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294580019/10000000000 : ℝ)^4565 ≤ (44052245616547/100000000000000 : ℝ)^3541 := by
    have hnat : (5294580019 : ℕ)^4565*100000000000000^3541 ≤ 44052245616547^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294580019 10000000000 44052245616547 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108358929/625000000 : ℝ)^4565 ≤ (1044506990887/10000000000000 : ℝ)^3541 := by
    have hnat : (108358929 : ℕ)^4565*10000000000000^3541 ≤ 1044506990887^3541*625000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108358929 625000000 1044506990887 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678663683/1250000000 : ℝ)^4565 ≤ (45502684449547/100000000000000 : ℝ)^3541 := by
    have hnat : (678663683 : ℕ)^4565*100000000000000^3541 ≤ 45502684449547^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678663683 1250000000 45502684449547 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294580019/10000000000 : ℝ), (-108358929/625000000 : ℝ), (678663683/1250000000 : ℝ)] ![(44052245616547/100000000000000 : ℝ), (1044506990887/10000000000000 : ℝ), (45502684449547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294580019/10000000000 : ℝ)|^4565 ≤ (44052245616547/100000000000000 : ℝ)^3541
        have hw : |(5294580019/10000000000 : ℝ)|=(5294580019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108358929/625000000 : ℝ)|^4565 ≤ (1044506990887/10000000000000 : ℝ)^3541
        have hw : |(-108358929/625000000 : ℝ)|=(108358929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678663683/1250000000 : ℝ)|^4565 ≤ (45502684449547/100000000000000 : ℝ)^3541
        have hw : |(678663683/1250000000 : ℝ)|=(678663683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647290011/5000000000 : ℝ)*x 0 + (2714654727/5000000000 : ℝ)*x 1 + (-433435719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647290011/5000000000 : ℝ)^4565 ≤ (22026122824363/50000000000000 : ℝ)^3541 := by
    have hnat : (2647290011 : ℕ)^4565*50000000000000^3541 ≤ 22026122824363^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647290011 5000000000 22026122824363 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714654727/5000000000 : ℝ)^4565 ≤ (45502684341501/100000000000000 : ℝ)^3541 := by
    have hnat : (2714654727 : ℕ)^4565*100000000000000^3541 ≤ 45502684341501^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714654727 5000000000 45502684341501 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433435719/2500000000 : ℝ)^4565 ≤ (1305633750259/12500000000000 : ℝ)^3541 := by
    have hnat : (433435719 : ℕ)^4565*12500000000000^3541 ≤ 1305633750259^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433435719 2500000000 1305633750259 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647290011/5000000000 : ℝ), (2714654727/5000000000 : ℝ), (-433435719/2500000000 : ℝ)] ![(22026122824363/50000000000000 : ℝ), (45502684341501/100000000000000 : ℝ), (1305633750259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647290011/5000000000 : ℝ)|^4565 ≤ (22026122824363/50000000000000 : ℝ)^3541
        have hw : |(2647290011/5000000000 : ℝ)|=(2647290011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714654727/5000000000 : ℝ)|^4565 ≤ (45502684341501/100000000000000 : ℝ)^3541
        have hw : |(2714654727/5000000000 : ℝ)|=(2714654727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433435719/2500000000 : ℝ)|^4565 ≤ (1305633750259/12500000000000 : ℝ)^3541
        have hw : |(-433435719/2500000000 : ℝ)|=(433435719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s5_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259697873/10000000000 : ℝ)*x 0 + (281672059/625000000 : ℝ)*x 1 + (2012084357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259697873/10000000000 : ℝ)^4565 ≤ (3328136514729/10000000000000 : ℝ)^3541 := by
    have hnat : (4259697873 : ℕ)^4565*10000000000000^3541 ≤ 3328136514729^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259697873 10000000000 3328136514729 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281672059/625000000 : ℝ)^4565 ≤ (8947603854941/25000000000000 : ℝ)^3541 := by
    have hnat : (281672059 : ℕ)^4565*25000000000000^3541 ≤ 8947603854941^3541*625000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281672059 625000000 8947603854941 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012084357/5000000000 : ℝ)^4565 ≤ (15464109701751/50000000000000 : ℝ)^3541 := by
    have hnat : (2012084357 : ℕ)^4565*50000000000000^3541 ≤ 15464109701751^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012084357 5000000000 15464109701751 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259697873/10000000000 : ℝ), (281672059/625000000 : ℝ), (2012084357/5000000000 : ℝ)] ![(3328136514729/10000000000000 : ℝ), (8947603854941/25000000000000 : ℝ), (15464109701751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259697873/10000000000 : ℝ)|^4565 ≤ (3328136514729/10000000000000 : ℝ)^3541
        have hw : |(4259697873/10000000000 : ℝ)|=(4259697873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281672059/625000000 : ℝ)|^4565 ≤ (8947603854941/25000000000000 : ℝ)^3541
        have hw : |(281672059/625000000 : ℝ)|=(281672059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012084357/5000000000 : ℝ)|^4565 ≤ (15464109701751/50000000000000 : ℝ)^3541
        have hw : |(2012084357/5000000000 : ℝ)|=(2012084357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5499/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10993/100000 : ℝ) ^ (4563/1024 : ℝ) ≤ (2667666144781841/50000000000000000000 : ℝ) := by
    have hpowers : (10993/100000 : ℝ)^4563 ≤ (2667666144781841/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10993 : ℕ)^4563*50000000000000000000^1024 ≤ 2667666144781841^1024*100000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10993 100000 2667666144781841 50000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10993/100000 : ℝ)) (X := (2667666144781841/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4563/1024 : ℝ) ≤ (24593753931922799/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4563 ≤ (24593753931922799/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4563*100000000000000000000^1024 ≤ 24593753931922799^1024*10000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 24593753931922799 100000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (24593753931922799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002667666144781841/25000000000000000000 : ℝ) ≤ (10000239454490623/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (25002667666144781841/25000000000000000000 : ℝ)^1024 ≤ (10000239454490623/10000000000000000 : ℝ)^4563 := by
      have hnat : (25002667666144781841 : ℕ)^1024*10000000000000000^4563 ≤ 10000239454490623^4563*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002667666144781841 25000000000000000000 10000239454490623 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000239454490623/10000000000000000 : ℝ)) (X := (25002667666144781841/25000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029929086221486481/100000000000000000000 : ℝ) ≤ (5000335785972993/5000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (100029929086221486481/100000000000000000000 : ℝ)^1024 ≤ (5000335785972993/5000000000000000 : ℝ)^4563 := by
      have hnat : (100029929086221486481 : ℕ)^1024*5000000000000000^4563 ≤ 5000335785972993^4563*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029929086221486481 100000000000000000000 5000335785972993 5000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000335785972993/5000000000000000 : ℝ)) (X := (100029929086221486481/100000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024593753931922799/50000000000000000000 : ℝ) ≤ (10001103689401349/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50024593753931922799/50000000000000000000 : ℝ)^1024 ≤ (10001103689401349/10000000000000000 : ℝ)^4563 := by
      have hnat : (50024593753931922799 : ℕ)^1024*10000000000000000^4563 ≤ 10001103689401349^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024593753931922799 50000000000000000000 10001103689401349 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001103689401349/10000000000000000 : ℝ)) (X := (50024593753931922799/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2667666144781841/50000000000000000000 : ℝ) ≤ ((44961576292470720713/44970000000000000000 : ℝ)+2*(432117455363/449700000000000 : ℝ)*(10993/100000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (44961576292470720713/44970000000000000000 : ℝ)+2*(432117455363/449700000000000 : ℝ)*(10993/100000 : ℝ)=(10000239454490623/10000000000000000 : ℝ) by norm_num, show 1+2*(2667666144781841/50000000000000000000 : ℝ)=(25002667666144781841/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24593753931922799/100000000000000000000 : ℝ)+(2667666144781841/50000000000000000000 : ℝ) ≤ ((44961576292470720713/44970000000000000000 : ℝ)+(432117455363/449700000000000 : ℝ)*((1549/10000 : ℝ)+(10993/100000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (44961576292470720713/44970000000000000000 : ℝ)+(432117455363/449700000000000 : ℝ)*((1549/10000 : ℝ)+(10993/100000 : ℝ))=(5000335785972993/5000000000000000 : ℝ) by norm_num, show 1+(24593753931922799/100000000000000000000 : ℝ)+(2667666144781841/50000000000000000000 : ℝ)=(100029929086221486481/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24593753931922799/100000000000000000000 : ℝ) ≤ ((44961576292470720713/44970000000000000000 : ℝ)+2*(432117455363/449700000000000 : ℝ)*(1549/10000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (44961576292470720713/44970000000000000000 : ℝ)+2*(432117455363/449700000000000 : ℝ)*(1549/10000 : ℝ)=(10001103689401349/10000000000000000 : ℝ) by norm_num, show 1+2*(24593753931922799/100000000000000000000 : ℝ)=(50024593753931922799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44961576292470720713/44970000000000000000 : ℝ)*(X 1 0+X 2 0)+(432117455363/449700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44961576292470720713/44970000000000000000 : ℝ)) (alpha := (432117455363/449700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44961576292470720713/44970000000000000000 : ℝ)*(X 0 1+X 2 1)+(432117455363/449700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44961576292470720713/44970000000000000000 : ℝ)) (alpha := (432117455363/449700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44961576292470720713/44970000000000000000 : ℝ)*(X 0 2+X 1 2)+(432117455363/449700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44961576292470720713/44970000000000000000 : ℝ)) (alpha := (432117455363/449700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1835995033/10000000000 : ℝ)*X 0 0+(1086082539/2000000000 : ℝ)*X 0 1+(5218648579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675173953/5000000000 : ℝ)*X 1 0+(-388880759/2000000000 : ℝ)*X 1 1+(10437297/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337586967/2500000000 : ℝ)*X 2 0+(260932427/500000000 : ℝ)*X 2 1+(-1944403791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((266227071/625000000 : ℝ)*X 0 0+(2010814101/5000000000 : ℝ)*X 0 1+(4509274859/10000000000 : ℝ)*X 0 2+(266227071/625000000 : ℝ)*X 1 0+(2010814101/5000000000 : ℝ)*X 1 1+(4509274859/10000000000 : ℝ)*X 1 2+(266227071/625000000 : ℝ)*X 2 0+(2010814101/5000000000 : ℝ)*X 2 1+(4509274859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-367204629/2000000000 : ℝ)*X 0 0+(521974373/1000000000 : ℝ)*X 0 1+(5429309459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294580019/10000000000 : ℝ)*X 1 0+(-108358929/625000000 : ℝ)*X 1 1+(678663683/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647290011/5000000000 : ℝ)*X 2 0+(2714654727/5000000000 : ℝ)*X 2 1+(-433435719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259697873/10000000000 : ℝ)*X 0 0+(281672059/625000000 : ℝ)*X 0 1+(2012084357/5000000000 : ℝ)*X 0 2+(4259697873/10000000000 : ℝ)*X 1 0+(281672059/625000000 : ℝ)*X 1 1+(2012084357/5000000000 : ℝ)*X 1 2+(4259697873/10000000000 : ℝ)*X 2 0+(281672059/625000000 : ℝ)*X 2 1+(2012084357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (645439834350471519547994011/187375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (653484009/100000000000000 : ℝ)*(base19) + (578929333/100000000000000 : ℝ)*(base23) + (21944783/100000000000000 : ℝ)*(lower2) + (83548047/100000000000000 : ℝ)*(upper3) + (12913593/25000000000000 : ℝ)*(upper5) + (846615970278547/25000000000000 : ℝ)*(major0) + (846615970278547/25000000000000 : ℝ)*(major1) + (846615970278547/25000000000000 : ℝ)*(major2) + (59028063647029/1250000000000 : ℝ)*(sp0) + (944450706691249/20000000000000 : ℝ)*(sp1) + (2361126804005461/50000000000000 : ℝ)*(sp2) + (51266726989887/2500000000000 : ℝ)*(sp3) + (4547588967/50000000000000 : ℝ)*(sp4) + (4380871227/100000000000000 : ℝ)*(sp7) + (512668365116677/25000000000000 : ℝ)*(f.failure) + (2361127093470127/50000000000000 : ℝ)*(f.sum) + (184606632414659/22485000000000000000000000000 : ℝ)*base65 + (108177616690455989/1124250000000000000000000000000000 : ℝ)*base68 + (5408545333996544011/1124250000000000000000000000000000 : ℝ)*base69 + (652003146600705989/1124250000000000000000000000000000 : ℝ)*base72 + (178453994139839/22485000000000000000000000000 : ℝ)*base73 + (4211506223117955989/1124250000000000000000000000000000 : ℝ)*base76 + (7369474142643794011/1124250000000000000000000000000000 : ℝ)*base77 + (4287967848445455989/1124250000000000000000000000000000 : ℝ)*base80 + (30776203547921/5621250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (20820793/2500000000000000000000 : ℝ)*base89 + (20820793/2500000000000000000000 : ℝ)*base91 + (20820793/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3889052605652754380665643091/374750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842681023/50000000000000 : ℝ)*(base19) + (914225001/50000000000000 : ℝ)*(base23) + (279673041/50000000000000 : ℝ)*(lower1) + (213366617/100000000000000 : ℝ)*(upper3) + (64628381/100000000000000 : ℝ)*(lower4) + (13285861/6250000000000 : ℝ)*(upper5) + (1710977559476293/50000000000000 : ℝ)*(major0) + (1710977559476293/50000000000000 : ℝ)*(major1) + (1710977559476293/50000000000000 : ℝ)*(major2) + (1739203877/100000000000000 : ℝ)*(sp2) + (1192936177436269/25000000000000 : ℝ)*(sp4) + (477174302438303/10000000000000 : ℝ)*(sp5) + (2385870571045599/50000000000000 : ℝ)*(sp6) + (2072165182235897/100000000000000 : ℝ)*(sp7) + (2072165182235897/100000000000000 : ℝ)*(f.failure) + (1192936177436269/25000000000000 : ℝ)*(f.sum) + (2205760007867/22485000000000000000000000000 : ℝ)*base66 + (5694153505855456909/2248500000000000000000000000000000 : ℝ)*base67 + (5320236738496456909/2248500000000000000000000000000000 : ℝ)*base69 + (139941249829709956909/2248500000000000000000000000000000 : ℝ)*base71 + (23713029915719/11242500000000000000000000000 : ℝ)*base73 + (190152036059449543091/2248500000000000000000000000000000 : ℝ)*base76 + (6473094790257043091/2248500000000000000000000000000000 : ℝ)*base78 + (1757924926843456909/2248500000000000000000000000000000 : ℝ)*base79 + (132923238450763/22485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (58395773/10000000000000000000000 : ℝ)*base89 + (58395773/10000000000000000000000 : ℝ)*base91 + (58395773/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1534_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1534_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1534_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1534_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1534_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
