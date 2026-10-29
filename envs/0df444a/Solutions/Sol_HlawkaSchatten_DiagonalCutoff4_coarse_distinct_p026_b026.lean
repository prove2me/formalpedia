-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:09:26.736749+00:00
-- url     : https://prove2.me/submissions/cb00f23d-0197-408d-9482-f00461f6f345

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c326051_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3233058463/10000000000 : ℝ)*x 0 + (3233058457/10000000000 : ℝ)*x 1 + (702305741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3233058463/10000000000 : ℝ)^89 ≤ (6310613857091/25000000000000 : ℝ)^73 := by
    have hnat : (3233058463 : ℕ)^89*25000000000000^73 ≤ 6310613857091^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233058463 10000000000 6310613857091 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3233058457/10000000000 : ℝ)^89 ≤ (25242455371251/100000000000000 : ℝ)^73 := by
    have hnat : (3233058457 : ℕ)^89*100000000000000^73 ≤ 25242455371251^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233058457 10000000000 25242455371251 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702305741/1250000000 : ℝ)^89 ≤ (12378772298063/25000000000000 : ℝ)^73 := by
    have hnat : (702305741 : ℕ)^89*25000000000000^73 ≤ 12378772298063^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702305741 1250000000 12378772298063 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3233058463/10000000000 : ℝ), (3233058457/10000000000 : ℝ), (702305741/1250000000 : ℝ)] ![(6310613857091/25000000000000 : ℝ), (25242455371251/100000000000000 : ℝ), (12378772298063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3233058463/10000000000 : ℝ)|^89 ≤ (6310613857091/25000000000000 : ℝ)^73
        have hw : |(-3233058463/10000000000 : ℝ)|=(3233058463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3233058457/10000000000 : ℝ)|^89 ≤ (25242455371251/100000000000000 : ℝ)^73
        have hw : |(3233058457/10000000000 : ℝ)|=(3233058457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(702305741/1250000000 : ℝ)|^89 ≤ (12378772298063/25000000000000 : ℝ)^73
        have hw : |(702305741/1250000000 : ℝ)|=(702305741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (118807681/500000000 : ℝ)*x 0 + (-475230723/2000000000 : ℝ)*x 1 + (440720151/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118807681/500000000 : ℝ)^89 ≤ (8670614787027/50000000000000 : ℝ)^73 := by
    have hnat : (118807681 : ℕ)^89*50000000000000^73 ≤ 8670614787027^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118807681 500000000 8670614787027 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475230723/2000000000 : ℝ)^89 ≤ (8670614764783/50000000000000 : ℝ)^73 := by
    have hnat : (475230723 : ℕ)^89*50000000000000^73 ≤ 8670614764783^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475230723 2000000000 8670614764783 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440720151/625000000 : ℝ)^89 ≤ (32658770443063/50000000000000 : ℝ)^73 := by
    have hnat : (440720151 : ℕ)^89*50000000000000^73 ≤ 32658770443063^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440720151 625000000 32658770443063 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(118807681/500000000 : ℝ), (-475230723/2000000000 : ℝ), (440720151/625000000 : ℝ)] ![(8670614787027/50000000000000 : ℝ), (8670614764783/50000000000000 : ℝ), (32658770443063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(118807681/500000000 : ℝ)|^89 ≤ (8670614787027/50000000000000 : ℝ)^73
        have hw : |(118807681/500000000 : ℝ)|=(118807681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475230723/2000000000 : ℝ)|^89 ≤ (8670614764783/50000000000000 : ℝ)^73
        have hw : |(-475230723/2000000000 : ℝ)|=(475230723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440720151/625000000 : ℝ)|^89 ≤ (32658770443063/50000000000000 : ℝ)^73
        have hw : |(440720151/625000000 : ℝ)|=(440720151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5911006623/10000000000 : ℝ)*x 0 + (5314383841/10000000000 : ℝ)*x 1 + (-239317687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5911006623/10000000000 : ℝ)^89 ≤ (26338112230431/50000000000000 : ℝ)^73 := by
    have hnat : (5911006623 : ℕ)^89*50000000000000^73 ≤ 26338112230431^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911006623 10000000000 26338112230431 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5314383841/10000000000 : ℝ)^89 ≤ (11566933130173/25000000000000 : ℝ)^73 := by
    have hnat : (5314383841 : ℕ)^89*25000000000000^73 ≤ 11566933130173^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5314383841 10000000000 11566933130173 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239317687/10000000000 : ℝ)^89 ≤ (1056042998377/100000000000000 : ℝ)^73 := by
    have hnat : (239317687 : ℕ)^89*100000000000000^73 ≤ 1056042998377^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239317687 10000000000 1056042998377 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5911006623/10000000000 : ℝ), (5314383841/10000000000 : ℝ), (-239317687/10000000000 : ℝ)] ![(26338112230431/50000000000000 : ℝ), (11566933130173/25000000000000 : ℝ), (1056042998377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5911006623/10000000000 : ℝ)|^89 ≤ (26338112230431/50000000000000 : ℝ)^73
        have hw : |(5911006623/10000000000 : ℝ)|=(5911006623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5314383841/10000000000 : ℝ)|^89 ≤ (11566933130173/25000000000000 : ℝ)^73
        have hw : |(5314383841/10000000000 : ℝ)|=(5314383841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239317687/10000000000 : ℝ)|^89 ≤ (1056042998377/100000000000000 : ℝ)^73
        have hw : |(-239317687/10000000000 : ℝ)|=(239317687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1371458089/5000000000 : ℝ)*x 0 + (410190429/2500000000 : ℝ)*x 1 + (7314687917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371458089/5000000000 : ℝ)^89 ≤ (20657655807721/100000000000000 : ℝ)^73 := by
    have hnat : (1371458089 : ℕ)^89*100000000000000^73 ≤ 20657655807721^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371458089 5000000000 20657655807721 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410190429/2500000000 : ℝ)^89 ≤ (11040803873169/100000000000000 : ℝ)^73 := by
    have hnat : (410190429 : ℕ)^89*100000000000000^73 ≤ 11040803873169^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410190429 2500000000 11040803873169 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7314687917/10000000000 : ℝ)^89 ≤ (34150770153023/50000000000000 : ℝ)^73 := by
    have hnat : (7314687917 : ℕ)^89*50000000000000^73 ≤ 34150770153023^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7314687917 10000000000 34150770153023 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1371458089/5000000000 : ℝ), (410190429/2500000000 : ℝ), (7314687917/10000000000 : ℝ)] ![(20657655807721/100000000000000 : ℝ), (11040803873169/100000000000000 : ℝ), (34150770153023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1371458089/5000000000 : ℝ)|^89 ≤ (20657655807721/100000000000000 : ℝ)^73
        have hw : |(-1371458089/5000000000 : ℝ)|=(1371458089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(410190429/2500000000 : ℝ)|^89 ≤ (11040803873169/100000000000000 : ℝ)^73
        have hw : |(410190429/2500000000 : ℝ)|=(410190429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7314687917/10000000000 : ℝ)|^89 ≤ (34150770153023/50000000000000 : ℝ)^73
        have hw : |(7314687917/10000000000 : ℝ)|=(7314687917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (373068513/2500000000 : ℝ)*x 0 + (-404351507/5000000000 : ℝ)*x 1 + (8794620751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373068513/2500000000 : ℝ)^89 ≤ (307343708233/3125000000000 : ℝ)^73 := by
    have hnat : (373068513 : ℕ)^89*3125000000000^73 ≤ 307343708233^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373068513 2500000000 307343708233 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404351507/5000000000 : ℝ)^89 ≤ (4660155011153/100000000000000 : ℝ)^73 := by
    have hnat : (404351507 : ℕ)^89*100000000000000^73 ≤ 4660155011153^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404351507 5000000000 4660155011153 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8794620751/10000000000 : ℝ)^89 ≤ (42752423153861/50000000000000 : ℝ)^73 := by
    have hnat : (8794620751 : ℕ)^89*50000000000000^73 ≤ 42752423153861^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8794620751 10000000000 42752423153861 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(373068513/2500000000 : ℝ), (-404351507/5000000000 : ℝ), (8794620751/10000000000 : ℝ)] ![(307343708233/3125000000000 : ℝ), (4660155011153/100000000000000 : ℝ), (42752423153861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(373068513/2500000000 : ℝ)|^89 ≤ (307343708233/3125000000000 : ℝ)^73
        have hw : |(373068513/2500000000 : ℝ)|=(373068513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404351507/5000000000 : ℝ)|^89 ≤ (4660155011153/100000000000000 : ℝ)^73
        have hw : |(-404351507/5000000000 : ℝ)|=(404351507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8794620751/10000000000 : ℝ)|^89 ≤ (42752423153861/50000000000000 : ℝ)^73
        have hw : |(8794620751/10000000000 : ℝ)|=(8794620751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4108627641/10000000000 : ℝ)*x 0 + (3532402091/5000000000 : ℝ)*x 1 + (-175553089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4108627641/10000000000 : ℝ)^89 ≤ (1056519718843/3125000000000 : ℝ)^73 := by
    have hnat : (4108627641 : ℕ)^89*3125000000000^73 ≤ 1056519718843^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108627641 10000000000 1056519718843 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3532402091/5000000000 : ℝ)^89 ≤ (255732673659/390625000000 : ℝ)^73 := by
    have hnat : (3532402091 : ℕ)^89*390625000000^73 ≤ 255732673659^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3532402091 5000000000 255732673659 390625000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175553089/10000000000 : ℝ)^89 ≤ (90475565283/12500000000000 : ℝ)^73 := by
    have hnat : (175553089 : ℕ)^89*12500000000000^73 ≤ 90475565283^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175553089 10000000000 90475565283 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4108627641/10000000000 : ℝ), (3532402091/5000000000 : ℝ), (-175553089/10000000000 : ℝ)] ![(1056519718843/3125000000000 : ℝ), (255732673659/390625000000 : ℝ), (90475565283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4108627641/10000000000 : ℝ)|^89 ≤ (1056519718843/3125000000000 : ℝ)^73
        have hw : |(4108627641/10000000000 : ℝ)|=(4108627641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3532402091/5000000000 : ℝ)|^89 ≤ (255732673659/390625000000 : ℝ)^73
        have hw : |(3532402091/5000000000 : ℝ)|=(3532402091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175553089/10000000000 : ℝ)|^89 ≤ (90475565283/12500000000000 : ℝ)^73
        have hw : |(-175553089/10000000000 : ℝ)|=(175553089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (55828703/200000000 : ℝ)*x 0 + (8175268317/10000000000 : ℝ)*x 1 + (165743789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55828703/200000000 : ℝ)^89 ≤ (21104014982023/100000000000000 : ℝ)^73 := by
    have hnat : (55828703 : ℕ)^89*100000000000000^73 ≤ 21104014982023^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55828703 200000000 21104014982023 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8175268317/10000000000 : ℝ)^89 ≤ (78221182108697/100000000000000 : ℝ)^73 := by
    have hnat : (8175268317 : ℕ)^89*100000000000000^73 ≤ 78221182108697^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8175268317 10000000000 78221182108697 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165743789/10000000000 : ℝ)^89 ≤ (337401447337/50000000000000 : ℝ)^73 := by
    have hnat : (165743789 : ℕ)^89*50000000000000^73 ≤ 337401447337^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165743789 10000000000 337401447337 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(55828703/200000000 : ℝ), (8175268317/10000000000 : ℝ), (165743789/10000000000 : ℝ)] ![(21104014982023/100000000000000 : ℝ), (78221182108697/100000000000000 : ℝ), (337401447337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(55828703/200000000 : ℝ)|^89 ≤ (21104014982023/100000000000000 : ℝ)^73
        have hw : |(55828703/200000000 : ℝ)|=(55828703/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8175268317/10000000000 : ℝ)|^89 ≤ (78221182108697/100000000000000 : ℝ)^73
        have hw : |(8175268317/10000000000 : ℝ)|=(8175268317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165743789/10000000000 : ℝ)|^89 ≤ (337401447337/50000000000000 : ℝ)^73
        have hw : |(165743789/10000000000 : ℝ)|=(165743789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-443926509/2500000000 : ℝ)*x 0 + (2794034681/10000000000 : ℝ)*x 1 + (1434995039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443926509/2500000000 : ℝ)^89 ≤ (3039412676969/25000000000000 : ℝ)^73 := by
    have hnat : (443926509 : ℕ)^89*25000000000000^73 ≤ 3039412676969^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443926509 2500000000 3039412676969 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794034681/10000000000 : ℝ)^89 ≤ (10563989068597/50000000000000 : ℝ)^73 := by
    have hnat : (2794034681 : ℕ)^89*50000000000000^73 ≤ 10563989068597^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794034681 10000000000 10563989068597 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1434995039/2000000000 : ℝ)^89 ≤ (2084824098061/3125000000000 : ℝ)^73 := by
    have hnat : (1434995039 : ℕ)^89*3125000000000^73 ≤ 2084824098061^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434995039 2000000000 2084824098061 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443926509/2500000000 : ℝ), (2794034681/10000000000 : ℝ), (1434995039/2000000000 : ℝ)] ![(3039412676969/25000000000000 : ℝ), (10563989068597/50000000000000 : ℝ), (2084824098061/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443926509/2500000000 : ℝ)|^89 ≤ (3039412676969/25000000000000 : ℝ)^73
        have hw : |(-443926509/2500000000 : ℝ)|=(443926509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794034681/10000000000 : ℝ)|^89 ≤ (10563989068597/50000000000000 : ℝ)^73
        have hw : |(2794034681/10000000000 : ℝ)|=(2794034681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1434995039/2000000000 : ℝ)|^89 ≤ (2084824098061/3125000000000 : ℝ)^73
        have hw : |(1434995039/2000000000 : ℝ)|=(1434995039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1021914551/10000000000 : ℝ)*x 0 + (-1612172481/10000000000 : ℝ)*x 1 + (214556997/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021914551/10000000000 : ℝ)^89 ≤ (3099345382461/50000000000000 : ℝ)^73 := by
    have hnat : (1021914551 : ℕ)^89*50000000000000^73 ≤ 3099345382461^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021914551 10000000000 3099345382461 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1612172481/10000000000 : ℝ)^89 ≤ (5403354749187/50000000000000 : ℝ)^73 := by
    have hnat : (1612172481 : ℕ)^89*50000000000000^73 ≤ 5403354749187^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612172481 10000000000 5403354749187 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214556997/250000000 : ℝ)^89 ≤ (82994599714091/100000000000000 : ℝ)^73 := by
    have hnat : (214556997 : ℕ)^89*100000000000000^73 ≤ 82994599714091^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214556997 250000000 82994599714091 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1021914551/10000000000 : ℝ), (-1612172481/10000000000 : ℝ), (214556997/250000000 : ℝ)] ![(3099345382461/50000000000000 : ℝ), (5403354749187/50000000000000 : ℝ), (82994599714091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1021914551/10000000000 : ℝ)|^89 ≤ (3099345382461/50000000000000 : ℝ)^73
        have hw : |(1021914551/10000000000 : ℝ)|=(1021914551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1612172481/10000000000 : ℝ)|^89 ≤ (5403354749187/50000000000000 : ℝ)^73
        have hw : |(-1612172481/10000000000 : ℝ)|=(1612172481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(214556997/250000000 : ℝ)|^89 ≤ (82994599714091/100000000000000 : ℝ)^73
        have hw : |(214556997/250000000 : ℝ)|=(214556997/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (93192289/125000000 : ℝ)*x 0 + (3692078907/10000000000 : ℝ)*x 1 + (-22290923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93192289/125000000 : ℝ)^89 ≤ (69906599618463/100000000000000 : ℝ)^73 := by
    have hnat : (93192289 : ℕ)^89*100000000000000^73 ≤ 69906599618463^73*125000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93192289 125000000 69906599618463 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3692078907/10000000000 : ℝ)^89 ≤ (29677427738349/100000000000000 : ℝ)^73 := by
    have hnat : (3692078907 : ℕ)^89*100000000000000^73 ≤ 29677427738349^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692078907 10000000000 29677427738349 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22290923/2000000000 : ℝ)^89 ≤ (41597262731/10000000000000 : ℝ)^73 := by
    have hnat : (22290923 : ℕ)^89*10000000000000^73 ≤ 41597262731^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22290923 2000000000 41597262731 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(93192289/125000000 : ℝ), (3692078907/10000000000 : ℝ), (-22290923/2000000000 : ℝ)] ![(69906599618463/100000000000000 : ℝ), (29677427738349/100000000000000 : ℝ), (41597262731/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(93192289/125000000 : ℝ)|^89 ≤ (69906599618463/100000000000000 : ℝ)^73
        have hw : |(93192289/125000000 : ℝ)|=(93192289/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3692078907/10000000000 : ℝ)|^89 ≤ (29677427738349/100000000000000 : ℝ)^73
        have hw : |(3692078907/10000000000 : ℝ)|=(3692078907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22290923/2000000000 : ℝ)|^89 ≤ (41597262731/10000000000000 : ℝ)^73
        have hw : |(-22290923/2000000000 : ℝ)|=(22290923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1849248293/2500000000 : ℝ)*x 0 + (58219297/156250000 : ℝ)*x 1 + (903541/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849248293/2500000000 : ℝ)^89 ≤ (69239670357873/100000000000000 : ℝ)^73 := by
    have hnat : (1849248293 : ℕ)^89*100000000000000^73 ≤ 69239670357873^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849248293 2500000000 69239670357873 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58219297/156250000 : ℝ)^89 ≤ (15005264663597/50000000000000 : ℝ)^73 := by
    have hnat : (58219297 : ℕ)^89*50000000000000^73 ≤ 15005264663597^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58219297 156250000 15005264663597 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903541/50000000 : ℝ)^89 ≤ (749800300493/100000000000000 : ℝ)^73 := by
    have hnat : (903541 : ℕ)^89*100000000000000^73 ≤ 749800300493^73*50000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903541 50000000 749800300493 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1849248293/2500000000 : ℝ), (58219297/156250000 : ℝ), (903541/50000000 : ℝ)] ![(69239670357873/100000000000000 : ℝ), (15005264663597/50000000000000 : ℝ), (749800300493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1849248293/2500000000 : ℝ)|^89 ≤ (69239670357873/100000000000000 : ℝ)^73
        have hw : |(1849248293/2500000000 : ℝ)|=(1849248293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58219297/156250000 : ℝ)|^89 ≤ (15005264663597/50000000000000 : ℝ)^73
        have hw : |(58219297/156250000 : ℝ)|=(58219297/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903541/50000000 : ℝ)|^89 ≤ (749800300493/100000000000000 : ℝ)^73
        have hw : |(903541/50000000 : ℝ)|=(903541/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4821887177/10000000000 : ℝ)*x 0 + (4174674933/10000000000 : ℝ)*x 1 + (1573884809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4821887177/10000000000 : ℝ)^89 ≤ (41094638445421/100000000000000 : ℝ)^73 := by
    have hnat : (4821887177 : ℕ)^89*100000000000000^73 ≤ 41094638445421^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821887177 10000000000 41094638445421 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4174674933/10000000000 : ℝ)^89 ≤ (17236197890477/50000000000000 : ℝ)^73 := by
    have hnat : (4174674933 : ℕ)^89*50000000000000^73 ≤ 17236197890477^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174674933 10000000000 17236197890477 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1573884809/5000000000 : ℝ)^89 ≤ (4886593150611/20000000000000 : ℝ)^73 := by
    have hnat : (1573884809 : ℕ)^89*20000000000000^73 ≤ 4886593150611^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573884809 5000000000 4886593150611 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4821887177/10000000000 : ℝ), (4174674933/10000000000 : ℝ), (1573884809/5000000000 : ℝ)] ![(41094638445421/100000000000000 : ℝ), (17236197890477/50000000000000 : ℝ), (4886593150611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4821887177/10000000000 : ℝ)|^89 ≤ (41094638445421/100000000000000 : ℝ)^73
        have hw : |(-4821887177/10000000000 : ℝ)|=(4821887177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4174674933/10000000000 : ℝ)|^89 ≤ (17236197890477/50000000000000 : ℝ)^73
        have hw : |(4174674933/10000000000 : ℝ)|=(4174674933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1573884809/5000000000 : ℝ)|^89 ≤ (4886593150611/20000000000000 : ℝ)^73
        have hw : |(1573884809/5000000000 : ℝ)|=(1573884809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1047696339/10000000000 : ℝ)*x 0 + (-847455507/5000000000 : ℝ)*x 1 + (531770273/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047696339/10000000000 : ℝ)^89 ≤ (3194938556437/50000000000000 : ℝ)^73 := by
    have hnat : (1047696339 : ℕ)^89*50000000000000^73 ≤ 3194938556437^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047696339 10000000000 3194938556437 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847455507/5000000000 : ℝ)^89 ≤ (2871658598213/25000000000000 : ℝ)^73 := by
    have hnat : (847455507 : ℕ)^89*25000000000000^73 ≤ 2871658598213^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847455507 5000000000 2871658598213 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531770273/625000000 : ℝ)^89 ≤ (10265436061159/12500000000000 : ℝ)^73 := by
    have hnat : (531770273 : ℕ)^89*12500000000000^73 ≤ 10265436061159^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531770273 625000000 10265436061159 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047696339/10000000000 : ℝ), (-847455507/5000000000 : ℝ), (531770273/625000000 : ℝ)] ![(3194938556437/50000000000000 : ℝ), (2871658598213/25000000000000 : ℝ), (10265436061159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047696339/10000000000 : ℝ)|^89 ≤ (3194938556437/50000000000000 : ℝ)^73
        have hw : |(1047696339/10000000000 : ℝ)|=(1047696339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-847455507/5000000000 : ℝ)|^89 ≤ (2871658598213/25000000000000 : ℝ)^73
        have hw : |(-847455507/5000000000 : ℝ)|=(847455507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531770273/625000000 : ℝ)|^89 ≤ (10265436061159/12500000000000 : ℝ)^73
        have hw : |(531770273/625000000 : ℝ)|=(531770273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6743235349/10000000000 : ℝ)*x 0 + (4500829117/10000000000 : ℝ)*x 1 + (-99816243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6743235349/10000000000 : ℝ)^89 ≤ (30926445510963/50000000000000 : ℝ)^73 := by
    have hnat : (6743235349 : ℕ)^89*50000000000000^73 ≤ 30926445510963^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6743235349 10000000000 30926445510963 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500829117/10000000000 : ℝ)^89 ≤ (1511338814519/4000000000000 : ℝ)^73 := by
    have hnat : (4500829117 : ℕ)^89*4000000000000^73 ≤ 1511338814519^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500829117 10000000000 1511338814519 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99816243/10000000000 : ℝ)^89 ≤ (363638602253/100000000000000 : ℝ)^73 := by
    have hnat : (99816243 : ℕ)^89*100000000000000^73 ≤ 363638602253^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99816243 10000000000 363638602253 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6743235349/10000000000 : ℝ), (4500829117/10000000000 : ℝ), (-99816243/10000000000 : ℝ)] ![(30926445510963/50000000000000 : ℝ), (1511338814519/4000000000000 : ℝ), (363638602253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6743235349/10000000000 : ℝ)|^89 ≤ (30926445510963/50000000000000 : ℝ)^73
        have hw : |(6743235349/10000000000 : ℝ)|=(6743235349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500829117/10000000000 : ℝ)|^89 ≤ (1511338814519/4000000000000 : ℝ)^73
        have hw : |(4500829117/10000000000 : ℝ)|=(4500829117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99816243/10000000000 : ℝ)|^89 ≤ (363638602253/100000000000000 : ℝ)^73
        have hw : |(-99816243/10000000000 : ℝ)|=(99816243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (635536537/2500000000 : ℝ)*x 0 + (8397825861/10000000000 : ℝ)*x 1 + (95757733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (635536537/2500000000 : ℝ)^89 ≤ (1882927091131/10000000000000 : ℝ)^73 := by
    have hnat : (635536537 : ℕ)^89*10000000000000^73 ≤ 1882927091131^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635536537 2500000000 1882927091131 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8397825861/10000000000 : ℝ)^89 ≤ (20206258856329/25000000000000 : ℝ)^73 := by
    have hnat : (8397825861 : ℕ)^89*25000000000000^73 ≤ 20206258856329^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8397825861 10000000000 20206258856329 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95757733/10000000000 : ℝ)^89 ≤ (345693658937/100000000000000 : ℝ)^73 := by
    have hnat : (95757733 : ℕ)^89*100000000000000^73 ≤ 345693658937^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95757733 10000000000 345693658937 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(635536537/2500000000 : ℝ), (8397825861/10000000000 : ℝ), (95757733/10000000000 : ℝ)] ![(1882927091131/10000000000000 : ℝ), (20206258856329/25000000000000 : ℝ), (345693658937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(635536537/2500000000 : ℝ)|^89 ≤ (1882927091131/10000000000000 : ℝ)^73
        have hw : |(635536537/2500000000 : ℝ)|=(635536537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8397825861/10000000000 : ℝ)|^89 ≤ (20206258856329/25000000000000 : ℝ)^73
        have hw : |(8397825861/10000000000 : ℝ)|=(8397825861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95757733/10000000000 : ℝ)|^89 ≤ (345693658937/100000000000000 : ℝ)^73
        have hw : |(95757733/10000000000 : ℝ)|=(95757733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-713830377/2000000000 : ℝ)*x 0 + (891442027/2500000000 : ℝ)*x 1 + (5012008419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (713830377/2000000000 : ℝ)^89 ≤ (1779824203527/6250000000000 : ℝ)^73 := by
    have hnat : (713830377 : ℕ)^89*6250000000000^73 ≤ 1779824203527^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713830377 2000000000 1779824203527 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891442027/2500000000 : ℝ)^89 ≤ (28444275140321/100000000000000 : ℝ)^73 := by
    have hnat : (891442027 : ℕ)^89*100000000000000^73 ≤ 28444275140321^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891442027 2500000000 28444275140321 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5012008419/10000000000 : ℝ)^89 ≤ (4307853759391/10000000000000 : ℝ)^73 := by
    have hnat : (5012008419 : ℕ)^89*10000000000000^73 ≤ 4307853759391^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012008419 10000000000 4307853759391 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-713830377/2000000000 : ℝ), (891442027/2500000000 : ℝ), (5012008419/10000000000 : ℝ)] ![(1779824203527/6250000000000 : ℝ), (28444275140321/100000000000000 : ℝ), (4307853759391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-713830377/2000000000 : ℝ)|^89 ≤ (1779824203527/6250000000000 : ℝ)^73
        have hw : |(-713830377/2000000000 : ℝ)|=(713830377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(891442027/2500000000 : ℝ)|^89 ≤ (28444275140321/100000000000000 : ℝ)^73
        have hw : |(891442027/2500000000 : ℝ)|=(891442027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5012008419/10000000000 : ℝ)|^89 ≤ (4307853759391/10000000000000 : ℝ)^73
        have hw : |(5012008419/10000000000 : ℝ)|=(5012008419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2955737169/10000000000 : ℝ)*x 0 + (-2952934947/10000000000 : ℝ)*x 1 + (3051521817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2955737169/10000000000 : ℝ)^89 ≤ (11314031025939/50000000000000 : ℝ)^73 := by
    have hnat : (2955737169 : ℕ)^89*50000000000000^73 ≤ 11314031025939^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955737169 10000000000 11314031025939 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2952934947/10000000000 : ℝ)^89 ≤ (11300954990113/50000000000000 : ℝ)^73 := by
    have hnat : (2952934947 : ℕ)^89*50000000000000^73 ≤ 11300954990113^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2952934947 10000000000 11300954990113 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3051521817/5000000000 : ℝ)^89 ≤ (27385013980469/50000000000000 : ℝ)^73 := by
    have hnat : (3051521817 : ℕ)^89*50000000000000^73 ≤ 27385013980469^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051521817 5000000000 27385013980469 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2955737169/10000000000 : ℝ), (-2952934947/10000000000 : ℝ), (3051521817/5000000000 : ℝ)] ![(11314031025939/50000000000000 : ℝ), (11300954990113/50000000000000 : ℝ), (27385013980469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2955737169/10000000000 : ℝ)|^89 ≤ (11314031025939/50000000000000 : ℝ)^73
        have hw : |(2955737169/10000000000 : ℝ)|=(2955737169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2952934947/10000000000 : ℝ)|^89 ≤ (11300954990113/50000000000000 : ℝ)^73
        have hw : |(-2952934947/10000000000 : ℝ)|=(2952934947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3051521817/5000000000 : ℝ)|^89 ≤ (27385013980469/50000000000000 : ℝ)^73
        have hw : |(3051521817/5000000000 : ℝ)|=(3051521817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2595902241/5000000000 : ℝ)*x 0 + (5196534937/10000000000 : ℝ)*x 1 + (-757018963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595902241/5000000000 : ℝ)^89 ≤ (22484971978541/50000000000000 : ℝ)^73 := by
    have hnat : (2595902241 : ℕ)^89*50000000000000^73 ≤ 22484971978541^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595902241 5000000000 22484971978541 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196534937/10000000000 : ℝ)^89 ≤ (45019903382111/100000000000000 : ℝ)^73 := by
    have hnat : (5196534937 : ℕ)^89*100000000000000^73 ≤ 45019903382111^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196534937 10000000000 45019903382111 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757018963/5000000000 : ℝ)^89 ≤ (10010152650079/100000000000000 : ℝ)^73 := by
    have hnat : (757018963 : ℕ)^89*100000000000000^73 ≤ 10010152650079^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757018963 5000000000 10010152650079 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595902241/5000000000 : ℝ), (5196534937/10000000000 : ℝ), (-757018963/5000000000 : ℝ)] ![(22484971978541/50000000000000 : ℝ), (45019903382111/100000000000000 : ℝ), (10010152650079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595902241/5000000000 : ℝ)|^89 ≤ (22484971978541/50000000000000 : ℝ)^73
        have hw : |(2595902241/5000000000 : ℝ)|=(2595902241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196534937/10000000000 : ℝ)|^89 ≤ (45019903382111/100000000000000 : ℝ)^73
        have hw : |(5196534937/10000000000 : ℝ)|=(5196534937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-757018963/5000000000 : ℝ)|^89 ≤ (10010152650079/100000000000000 : ℝ)^73
        have hw : |(-757018963/5000000000 : ℝ)|=(757018963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326051_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4949255849/10000000000 : ℝ)*x 0 + (4953765309/10000000000 : ℝ)*x 1 + (33159827/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4949255849/10000000000 : ℝ)^89 ≤ (21210931993371/50000000000000 : ℝ)^73 := by
    have hnat : (4949255849 : ℕ)^89*50000000000000^73 ≤ 21210931993371^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949255849 10000000000 21210931993371 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4953765309/10000000000 : ℝ)^89 ≤ (21234496311879/50000000000000 : ℝ)^73 := by
    have hnat : (4953765309 : ℕ)^89*50000000000000^73 ≤ 21234496311879^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4953765309 10000000000 21234496311879 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33159827/156250000 : ℝ)^89 ≤ (3777285841979/25000000000000 : ℝ)^73 := by
    have hnat : (33159827 : ℕ)^89*25000000000000^73 ≤ 3777285841979^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33159827 156250000 3777285841979 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4949255849/10000000000 : ℝ), (4953765309/10000000000 : ℝ), (33159827/156250000 : ℝ)] ![(21210931993371/50000000000000 : ℝ), (21234496311879/50000000000000 : ℝ), (3777285841979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4949255849/10000000000 : ℝ)|^89 ≤ (21210931993371/50000000000000 : ℝ)^73
        have hw : |(4949255849/10000000000 : ℝ)|=(4949255849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4953765309/10000000000 : ℝ)|^89 ≤ (21234496311879/50000000000000 : ℝ)^73
        have hw : |(4953765309/10000000000 : ℝ)|=(4953765309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33159827/156250000 : ℝ)|^89 ≤ (3777285841979/25000000000000 : ℝ)^73
        have hw : |(33159827/156250000 : ℝ)|=(33159827/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326051 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3233058463/10000000000 : ℝ)*X 0 0+(3233058457/10000000000 : ℝ)*X 0 1+(702305741/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((118807681/500000000 : ℝ)*X 1 0+(-475230723/2000000000 : ℝ)*X 1 1+(440720151/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5911006623/10000000000 : ℝ)*X 2 0+(5314383841/10000000000 : ℝ)*X 2 1+(-239317687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1371458089/5000000000 : ℝ)*X 0 0+(410190429/2500000000 : ℝ)*X 0 1+(7314687917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((373068513/2500000000 : ℝ)*X 1 0+(-404351507/5000000000 : ℝ)*X 1 1+(8794620751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4108627641/10000000000 : ℝ)*X 2 0+(3532402091/5000000000 : ℝ)*X 2 1+(-175553089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((55828703/200000000 : ℝ)*X 0 0+(8175268317/10000000000 : ℝ)*X 0 1+(165743789/10000000000 : ℝ)*X 0 2+(55828703/200000000 : ℝ)*X 1 0+(8175268317/10000000000 : ℝ)*X 1 1+(165743789/10000000000 : ℝ)*X 1 2+(55828703/200000000 : ℝ)*X 2 0+(8175268317/10000000000 : ℝ)*X 2 1+(165743789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-443926509/2500000000 : ℝ)*X 0 0+(2794034681/10000000000 : ℝ)*X 0 1+(1434995039/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1021914551/10000000000 : ℝ)*X 1 0+(-1612172481/10000000000 : ℝ)*X 1 1+(214556997/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((93192289/125000000 : ℝ)*X 2 0+(3692078907/10000000000 : ℝ)*X 2 1+(-22290923/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1849248293/2500000000 : ℝ)*X 0 0+(58219297/156250000 : ℝ)*X 0 1+(903541/50000000 : ℝ)*X 0 2+(1849248293/2500000000 : ℝ)*X 1 0+(58219297/156250000 : ℝ)*X 1 1+(903541/50000000 : ℝ)*X 1 2+(1849248293/2500000000 : ℝ)*X 2 0+(58219297/156250000 : ℝ)*X 2 1+(903541/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4821887177/10000000000 : ℝ)*X 0 0+(4174674933/10000000000 : ℝ)*X 0 1+(1573884809/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1047696339/10000000000 : ℝ)*X 1 0+(-847455507/5000000000 : ℝ)*X 1 1+(531770273/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6743235349/10000000000 : ℝ)*X 2 0+(4500829117/10000000000 : ℝ)*X 2 1+(-99816243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((635536537/2500000000 : ℝ)*X 0 0+(8397825861/10000000000 : ℝ)*X 0 1+(95757733/10000000000 : ℝ)*X 0 2+(635536537/2500000000 : ℝ)*X 1 0+(8397825861/10000000000 : ℝ)*X 1 1+(95757733/10000000000 : ℝ)*X 1 2+(635536537/2500000000 : ℝ)*X 2 0+(8397825861/10000000000 : ℝ)*X 2 1+(95757733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((61569/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(61569/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3564098285685284352273/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240592832639/250000000000 : ℝ)*(base7) + (25257/25000000000 : ℝ)*(base19) + (7629630491/1000000000000 : ℝ)*(base49) + (20621596681/250000000000 : ℝ)*(base60) + (88373779553/50000000000 : ℝ)*(major_s0_0) + (88373779553/50000000000 : ℝ)*(major_s0_1) + (88373779553/50000000000 : ℝ)*(major_s0_2) + (141773/250000000000 : ℝ)*(sp_s0_2) + (538033064163/250000000000 : ℝ)*(sp_s0_7) + (269022663861/125000000000 : ℝ)*(sp_s0_8) + (2152181754077/1000000000000 : ℝ)*(sp_s0_9) + (363835659839/200000000000 : ℝ)*(sp_s0_13) + (50064517/1000000000000 : ℝ)*(sp_s0_14) + (88574017/1000000000000 : ℝ)*(sp_s0_27) + (6694496427/7812500000 : ℝ)*(f.failure) + (2152182321169/1000000000000 : ℝ)*(f.sum) + (2588049951/5000000000000000000000 : ℝ)*base63 + (396153918584859/500000000000000000000000000 : ℝ)*base65 + (21030562615141/500000000000000000000000000 : ℝ)*base67 + (7269765098379/10000000000000000000000000 : ℝ)*base69 + (327337983615909/500000000000000000000000000 : ℝ)*base71 + (459463776434859/500000000000000000000000000 : ℝ)*base73 + (1489982520621/10000000000000000000000000 : ℝ)*base75 + (3701947121621/10000000000000000000000000 : ℝ)*base77 + (575876741/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (47/78125000000000 : ℝ)*base86 + (47/78125000000000 : ℝ)*base88 + (47/78125000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15229/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15229/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (168181773565655333283/20000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239981123797/1000000000000 : ℝ)*(base5) + (472034811859/500000000000 : ℝ)*(base7) + (8961/250000000000 : ℝ)*(base49) + (26683671529/125000000000 : ℝ)*(base60) + (388812950573/200000000000 : ℝ)*(major_s0_0) + (388812950573/200000000000 : ℝ)*(major_s0_1) + (388812950573/200000000000 : ℝ)*(major_s0_2) + (5602217/1000000000000 : ℝ)*(sp_s0_0) + (29321311/1000000000000 : ℝ)*(sp_s0_7) + (1214857755431/500000000000 : ℝ)*(sp_s0_14) + (607420267009/250000000000 : ℝ)*(sp_s0_15) + (667432889547/250000000000 : ℝ)*(sp_s0_16) + (205824600467/125000000000 : ℝ)*(sp_s0_20) + (13873271/200000000000 : ℝ)*(sp_s0_22) + (117813537977/125000000000 : ℝ)*(f.failure) + (2429750434391/1000000000000 : ℝ)*(f.sum) + (1646354269/10000000000000000000000 : ℝ)*base63 + (107444928055919/2000000000000000000000000000 : ℝ)*base65 + (699445350344081/2000000000000000000000000000 : ℝ)*base67 + (371801566239/40000000000000000000000000 : ℝ)*base69 + (383140525743969/2000000000000000000000000000 : ℝ)*base71 + (1257088224944081/2000000000000000000000000000 : ℝ)*base72 + (8123137266239/40000000000000000000000000 : ℝ)*base74 + (12403350274239/40000000000000000000000000 : ℝ)*base76 + (115390121/500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (2681/2500000000000000 : ℝ)*base87 + (2681/2500000000000000 : ℝ)*base89 + (2681/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11653/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11653/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1961799368706854304453/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9013/7812500000 : ℝ)*(base5) + (139297323937/1000000000000 : ℝ)*(base7) + (266511783801/500000000000 : ℝ)*(base39) + (1548093/1000000000000 : ℝ)*(base44) + (549431513529/1000000000000 : ℝ)*(base49) + (1765211101659/1000000000000 : ℝ)*(major_s0_0) + (882604776783/500000000000 : ℝ)*(major_s0_1) + (1765211101659/1000000000000 : ℝ)*(major_s0_2) + (707669/20000000000 : ℝ)*(sp_s0_1) + (103462817/1000000000000 : ℝ)*(sp_s0_13) + (2598505008681/1000000000000 : ℝ)*(sp_s0_21) + (1299234038569/500000000000 : ℝ)*(sp_s0_22) + (1299253081173/500000000000 : ℝ)*(sp_s0_23) + (124373605951/125000000000 : ℝ)*(sp_s0_27) + (171159537649/200000000000 : ℝ)*(f.failure) + (2598505008681/1000000000000 : ℝ)*(f.sum) + (63225321524401/200000000000000000000000000 : ℝ)*base62 + (5546824590606423/10000000000000000000000000000 : ℝ)*base64 + (651359591731451/5000000000000000000000000000 : ℝ)*base67 + (81157662789863/200000000000000000000000000 : ℝ)*base68 + (7130196712113273/10000000000000000000000000000 : ℝ)*base70 + (1884932001606423/10000000000000000000000000000 : ℝ)*base72 + (65567535437269/100000000000000000000000000 : ℝ)*base74 + (159836462710137/200000000000000000000000000 : ℝ)*base76 + (4735887378856479/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1803/4000000000000000 : ℝ)*base86 + (1803/4000000000000000 : ℝ)*base88 + (1803/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (61569/100000 : ℝ) ^ (87/16 : ℝ) ≤ (7155770740421626897/100000000000000000000 : ℝ) := by
    have hpowers : (61569/100000 : ℝ)^87 ≤ (7155770740421626897/100000000000000000000 : ℝ)^16 := by
      have hnat : (61569 : ℕ)^87*100000000000000000000^16 ≤ 7155770740421626897^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61569 100000 7155770740421626897 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61569/100000 : ℝ)) (X := (7155770740421626897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (107155770740421626897/100000000000000000000 : ℝ) ≤ (5063958152829861/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (107155770740421626897/100000000000000000000 : ℝ)^16 ≤ (5063958152829861/5000000000000000 : ℝ)^87 := by
      have hnat : (107155770740421626897 : ℕ)^16*5000000000000000^87 ≤ 5063958152829861^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107155770740421626897 100000000000000000000 5063958152829861 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5063958152829861/5000000000000000 : ℝ)) (X := (107155770740421626897/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (57155770740421626897/50000000000000000000 : ℝ) ≤ (10249041067282131/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (57155770740421626897/50000000000000000000 : ℝ)^16 ≤ (10249041067282131/10000000000000000 : ℝ)^87 := by
      have hnat : (57155770740421626897 : ℕ)^16*10000000000000000^87 ≤ 10249041067282131^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57155770740421626897 50000000000000000000 10249041067282131 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10249041067282131/10000000000000000 : ℝ)) (X := (57155770740421626897/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(63958152829861/3078450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(40374920540803/2052300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (61569/100000 : ℝ)) (alpha := (63958152829861/3078450000000000 : ℝ)) (beta := (40374920540803/2052300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (61569/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(63958152829861/3078450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(40374920540803/2052300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (15229/25000 : ℝ) ^ (87/16 : ℝ) ≤ (6752690857455993787/100000000000000000000 : ℝ) := by
    have hpowers : (15229/25000 : ℝ)^87 ≤ (6752690857455993787/100000000000000000000 : ℝ)^16 := by
      have hnat : (15229 : ℕ)^87*100000000000000000000^16 ≤ 6752690857455993787^16*25000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15229 25000 6752690857455993787 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15229/25000 : ℝ)) (X := (6752690857455993787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (106752690857455993787/100000000000000000000 : ℝ) ≤ (1265112387898981/1250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (106752690857455993787/100000000000000000000 : ℝ)^16 ≤ (1265112387898981/1250000000000000 : ℝ)^87 := by
      have hnat : (106752690857455993787 : ℕ)^16*1250000000000000^87 ≤ 1265112387898981^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106752690857455993787 100000000000000000000 1265112387898981 1250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265112387898981/1250000000000000 : ℝ)) (X := (106752690857455993787/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (56752690857455993787/50000000000000000000 : ℝ) ≤ (10235709896033309/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (56752690857455993787/50000000000000000000 : ℝ)^16 ≤ (10235709896033309/10000000000000000 : ℝ)^87 := by
      have hnat : (56752690857455993787 : ℕ)^16*10000000000000000^87 ≤ 10235709896033309^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56752690857455993787 50000000000000000000 10235709896033309 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10235709896033309/10000000000000000 : ℝ)) (X := (56752690857455993787/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(15112387898981/761450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(114810792841461/6091600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (15229/25000 : ℝ)) (alpha := (15112387898981/761450000000000 : ℝ)) (beta := (114810792841461/6091600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15229/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(15112387898981/761450000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(114810792841461/6091600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11653/50000 : ℝ) ^ (87/16 : ℝ) ≤ (4544811349133377/12500000000000000000 : ℝ) := by
    have hpowers : (11653/50000 : ℝ)^87 ≤ (4544811349133377/12500000000000000000 : ℝ)^16 := by
      have hnat : (11653 : ℕ)^87*12500000000000000000^16 ≤ 4544811349133377^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11653 50000 4544811349133377 12500000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11653/50000 : ℝ)) (X := (4544811349133377/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (12504544811349133377/12500000000000000000 : ℝ) ≤ (10000668562719221/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (12504544811349133377/12500000000000000000 : ℝ)^16 ≤ (10000668562719221/10000000000000000 : ℝ)^87 := by
      have hnat : (12504544811349133377 : ℕ)^16*10000000000000000^87 ≤ 10000668562719221^87*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504544811349133377 12500000000000000000 10000668562719221 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668562719221/10000000000000000 : ℝ)) (X := (12504544811349133377/12500000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6254544811349133377/6250000000000000000 : ℝ) ≤ (10001336927164869/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (6254544811349133377/6250000000000000000 : ℝ)^16 ≤ (10001336927164869/10000000000000000 : ℝ)^87 := by
      have hnat : (6254544811349133377 : ℕ)^16*10000000000000000^87 ≤ 10001336927164869^87*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254544811349133377 6250000000000000000 10001336927164869 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001336927164869/10000000000000000 : ℝ)) (X := (6254544811349133377/6250000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(668562719221/2330600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(41772777853/145662500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (11653/50000 : ℝ)) (alpha := (668562719221/2330600000000000 : ℝ)) (beta := (41772777853/145662500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (11653/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(668562719221/2330600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(41772777853/145662500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-713830377/2000000000 : ℝ)*X 0 0+(891442027/2500000000 : ℝ)*X 0 1+(5012008419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2955737169/10000000000 : ℝ)*X 1 0+(-2952934947/10000000000 : ℝ)*X 1 1+(3051521817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2595902241/5000000000 : ℝ)*X 2 0+(5196534937/10000000000 : ℝ)*X 2 1+(-757018963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4949255849/10000000000 : ℝ)*X 0 0+(4953765309/10000000000 : ℝ)*X 0 1+(33159827/156250000 : ℝ)*X 0 2+(4949255849/10000000000 : ℝ)*X 1 0+(4953765309/10000000000 : ℝ)*X 1 1+(33159827/156250000 : ℝ)*X 1 2+(4949255849/10000000000 : ℝ)*X 2 0+(4953765309/10000000000 : ℝ)*X 2 1+(33159827/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326051_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-22569727947046798901762002633072779/2428056113234000000000000000000000 : ℝ) := by norm_num
    linear_combination (13653/1000000000000 : ℝ)*(base5) + (8423/1000000000000 : ℝ)*(base7) + (27/3906250000 : ℝ)*(base19) + (1079/500000000000 : ℝ)*(base23) + (117/5000000000 : ℝ)*(base43) + (64649787693/250000000000 : ℝ)*(base49) + (188283587611/1000000000000 : ℝ)*(base59) + (651308422203/1000000000000 : ℝ)*(base60) + (41253/20000 : ℝ)*(major_s1_0) + (10313249883/5000000000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (3098463227439/1000000000000 : ℝ)*(sp_s1_0) + (3098463243927/1000000000000 : ℝ)*(sp_s1_1) + (619692647787/200000000000 : ℝ)*(sp_s1_2) + (999999994769/1000000000000 : ℝ)*(sp_s1_6) + (3098463250839/1000000000000 : ℝ)*(f.sum) + (247092221365786609/887317685000000000000000000000 : ℝ)*base63 + (12905614863451/116530000000000000000000000 : ℝ)*base65 + (14569510803883/38072500000000000000000000 : ℝ)*base66 + (1343701735399/3641562500000000000000000 : ℝ)*base69 + (5244710814891589/298943148750000000000000000000 : ℝ)*base71 + (62060446047/1368200000000000000000000 : ℝ)*base72 + (18948678137741/152290000000000000000000000 : ℝ)*base75 + (17713525253617/51307500000000000000000000 : ℝ)*base76 + (356689268267108073/1041815890000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b026 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=51 := by omega
  rcases hc with rfl
  · exact collision_c326051 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 51 ≤ c.val) (hhi : c.val < 52)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
