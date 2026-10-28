-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b011
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:14:26.534803+00:00
-- url     : https://prove2.me/submissions/cc45cdf4-3f1e-4d86-be29-0dafa93ad15e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10023
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
theorem collision_support_c302022_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2553156969/10000000000 : ℝ)*x 0 + (702878579/1250000000 : ℝ)*x 1 + (144873639/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2553156969/10000000000 : ℝ)^67 ≤ (8318262545137/50000000000000 : ℝ)^51 := by
    have hnat : (2553156969 : ℕ)^67*50000000000000^51 ≤ 8318262545137^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553156969 10000000000 8318262545137 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702878579/1250000000 : ℝ)^67 ≤ (46938542826799/100000000000000 : ℝ)^51 := by
    have hnat : (702878579 : ℕ)^67*100000000000000^51 ≤ 46938542826799^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702878579 1250000000 46938542826799 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144873639/312500000 : ℝ)^67 ≤ (36424932066881/100000000000000 : ℝ)^51 := by
    have hnat : (144873639 : ℕ)^67*100000000000000^51 ≤ 36424932066881^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144873639 312500000 36424932066881 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2553156969/10000000000 : ℝ), (702878579/1250000000 : ℝ), (144873639/312500000 : ℝ)] ![(8318262545137/50000000000000 : ℝ), (46938542826799/100000000000000 : ℝ), (36424932066881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2553156969/10000000000 : ℝ)|^67 ≤ (8318262545137/50000000000000 : ℝ)^51
        have hw : |(2553156969/10000000000 : ℝ)|=(2553156969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702878579/1250000000 : ℝ)|^67 ≤ (46938542826799/100000000000000 : ℝ)^51
        have hw : |(702878579/1250000000 : ℝ)|=(702878579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(144873639/312500000 : ℝ)|^67 ≤ (36424932066881/100000000000000 : ℝ)^51
        have hw : |(144873639/312500000 : ℝ)|=(144873639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-529768683/2000000000 : ℝ)*x 0 + (174328121/500000000 : ℝ)*x 1 + (-6561323281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529768683/2000000000 : ℝ)^67 ≤ (1091275371219/6250000000000 : ℝ)^51 := by
    have hnat : (529768683 : ℕ)^67*6250000000000^51 ≤ 1091275371219^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529768683 2000000000 1091275371219 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174328121/500000000 : ℝ)^67 ≤ (25051622505849/100000000000000 : ℝ)^51 := by
    have hnat : (174328121 : ℕ)^67*100000000000000^51 ≤ 25051622505849^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174328121 500000000 25051622505849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6561323281/10000000000 : ℝ)^67 ≤ (3592998221711/6250000000000 : ℝ)^51 := by
    have hnat : (6561323281 : ℕ)^67*6250000000000^51 ≤ 3592998221711^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6561323281 10000000000 3592998221711 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529768683/2000000000 : ℝ), (174328121/500000000 : ℝ), (-6561323281/10000000000 : ℝ)] ![(1091275371219/6250000000000 : ℝ), (25051622505849/100000000000000 : ℝ), (3592998221711/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529768683/2000000000 : ℝ)|^67 ≤ (1091275371219/6250000000000 : ℝ)^51
        have hw : |(-529768683/2000000000 : ℝ)|=(529768683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174328121/500000000 : ℝ)|^67 ≤ (25051622505849/100000000000000 : ℝ)^51
        have hw : |(174328121/500000000 : ℝ)|=(174328121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6561323281/10000000000 : ℝ)|^67 ≤ (3592998221711/6250000000000 : ℝ)^51
        have hw : |(-6561323281/10000000000 : ℝ)|=(6561323281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7425731453/10000000000 : ℝ)*x 0 + (-45999721/2500000000 : ℝ)*x 1 + (-836888629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7425731453/10000000000 : ℝ)^67 ≤ (676373904659/1000000000000 : ℝ)^51 := by
    have hnat : (7425731453 : ℕ)^67*1000000000000^51 ≤ 676373904659^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7425731453 10000000000 676373904659 1000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45999721/2500000000 : ℝ)^67 ≤ (525343645531/100000000000000 : ℝ)^51 := by
    have hnat : (45999721 : ℕ)^67*100000000000000^51 ≤ 525343645531^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45999721 2500000000 525343645531 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (836888629/2000000000 : ℝ)^67 ≤ (636745317629/2000000000000 : ℝ)^51 := by
    have hnat : (836888629 : ℕ)^67*2000000000000^51 ≤ 636745317629^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836888629 2000000000 636745317629 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7425731453/10000000000 : ℝ), (-45999721/2500000000 : ℝ), (-836888629/2000000000 : ℝ)] ![(676373904659/1000000000000 : ℝ), (525343645531/100000000000000 : ℝ), (636745317629/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7425731453/10000000000 : ℝ)|^67 ≤ (676373904659/1000000000000 : ℝ)^51
        have hw : |(7425731453/10000000000 : ℝ)|=(7425731453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45999721/2500000000 : ℝ)|^67 ≤ (525343645531/100000000000000 : ℝ)^51
        have hw : |(-45999721/2500000000 : ℝ)|=(45999721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-836888629/2000000000 : ℝ)|^67 ≤ (636745317629/2000000000000 : ℝ)^51
        have hw : |(-836888629/2000000000 : ℝ)|=(836888629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1434028843/10000000000 : ℝ)*x 0 + (366650009/500000000 : ℝ)*x 1 + (3552164231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1434028843/10000000000 : ℝ)^67 ≤ (1559475627297/20000000000000 : ℝ)^51 := by
    have hnat : (1434028843 : ℕ)^67*20000000000000^51 ≤ 1559475627297^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434028843 10000000000 1559475627297 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366650009/500000000 : ℝ)^67 ≤ (66529939664427/100000000000000 : ℝ)^51 := by
    have hnat : (366650009 : ℕ)^67*100000000000000^51 ≤ 66529939664427^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366650009 500000000 66529939664427 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3552164231/10000000000 : ℝ)^67 ≤ (401135659043/1562500000000 : ℝ)^51 := by
    have hnat : (3552164231 : ℕ)^67*1562500000000^51 ≤ 401135659043^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552164231 10000000000 401135659043 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1434028843/10000000000 : ℝ), (366650009/500000000 : ℝ), (3552164231/10000000000 : ℝ)] ![(1559475627297/20000000000000 : ℝ), (66529939664427/100000000000000 : ℝ), (401135659043/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1434028843/10000000000 : ℝ)|^67 ≤ (1559475627297/20000000000000 : ℝ)^51
        have hw : |(1434028843/10000000000 : ℝ)|=(1434028843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(366650009/500000000 : ℝ)|^67 ≤ (66529939664427/100000000000000 : ℝ)^51
        have hw : |(366650009/500000000 : ℝ)|=(366650009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3552164231/10000000000 : ℝ)|^67 ≤ (401135659043/1562500000000 : ℝ)^51
        have hw : |(3552164231/10000000000 : ℝ)|=(3552164231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_11 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^67 ≤ (0 : ℝ)^51 := by
    have hnat : (0 : ℕ)^67*1^51 ≤ 0^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^67 ≤ (1 : ℝ)^51 := by
    have hnat : (1 : ℕ)^67*1^51 ≤ 1^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^67 ≤ (0 : ℝ)^51 := by
    have hnat : (0 : ℕ)^67*1^51 ≤ 0^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^67 ≤ (0 : ℝ)^51
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^67 ≤ (1 : ℝ)^51
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^67 ≤ (0 : ℝ)^51
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2618400999/10000000000 : ℝ)*x 0 + (1601907219/2000000000 : ℝ)*x 1 + (-1475484291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618400999/10000000000 : ℝ)^67 ≤ (1719726036083/10000000000000 : ℝ)^51 := by
    have hnat : (2618400999 : ℕ)^67*10000000000000^51 ≤ 1719726036083^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618400999 10000000000 1719726036083 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1601907219/2000000000 : ℝ)^67 ≤ (74707901161157/100000000000000 : ℝ)^51 := by
    have hnat : (1601907219 : ℕ)^67*100000000000000^51 ≤ 74707901161157^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601907219 2000000000 74707901161157 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1475484291/10000000000 : ℝ)^67 ≤ (4047419234903/50000000000000 : ℝ)^51 := by
    have hnat : (1475484291 : ℕ)^67*50000000000000^51 ≤ 4047419234903^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475484291 10000000000 4047419234903 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618400999/10000000000 : ℝ), (1601907219/2000000000 : ℝ), (-1475484291/10000000000 : ℝ)] ![(1719726036083/10000000000000 : ℝ), (74707901161157/100000000000000 : ℝ), (4047419234903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618400999/10000000000 : ℝ)|^67 ≤ (1719726036083/10000000000000 : ℝ)^51
        have hw : |(2618400999/10000000000 : ℝ)|=(2618400999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1601907219/2000000000 : ℝ)|^67 ≤ (74707901161157/100000000000000 : ℝ)^51
        have hw : |(1601907219/2000000000 : ℝ)|=(1601907219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1475484291/10000000000 : ℝ)|^67 ≤ (4047419234903/50000000000000 : ℝ)^51
        have hw : |(-1475484291/10000000000 : ℝ)|=(1475484291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-50403773/156250000 : ℝ)*x 0 + (4044734539/10000000000 : ℝ)*x 1 + (-5622418911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50403773/156250000 : ℝ)^67 ≤ (22619958920297/100000000000000 : ℝ)^51 := by
    have hnat : (50403773 : ℕ)^67*100000000000000^51 ≤ 22619958920297^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50403773 156250000 22619958920297 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4044734539/10000000000 : ℝ)^67 ≤ (15224092284891/50000000000000 : ℝ)^51 := by
    have hnat : (4044734539 : ℕ)^67*50000000000000^51 ≤ 15224092284891^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044734539 10000000000 15224092284891 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5622418911/10000000000 : ℝ)^67 ≤ (9386371299687/20000000000000 : ℝ)^51 := by
    have hnat : (5622418911 : ℕ)^67*20000000000000^51 ≤ 9386371299687^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622418911 10000000000 9386371299687 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50403773/156250000 : ℝ), (4044734539/10000000000 : ℝ), (-5622418911/10000000000 : ℝ)] ![(22619958920297/100000000000000 : ℝ), (15224092284891/50000000000000 : ℝ), (9386371299687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50403773/156250000 : ℝ)|^67 ≤ (22619958920297/100000000000000 : ℝ)^51
        have hw : |(-50403773/156250000 : ℝ)|=(50403773/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4044734539/10000000000 : ℝ)|^67 ≤ (15224092284891/50000000000000 : ℝ)^51
        have hw : |(4044734539/10000000000 : ℝ)|=(4044734539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5622418911/10000000000 : ℝ)|^67 ≤ (9386371299687/20000000000000 : ℝ)^51
        have hw : |(-5622418911/10000000000 : ℝ)|=(5622418911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (358467089/400000000 : ℝ)*x 0 + (-1160297159/10000000000 : ℝ)*x 1 + (-1393566993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358467089/400000000 : ℝ)^67 ≤ (21646745716703/25000000000000 : ℝ)^51 := by
    have hnat : (358467089 : ℕ)^67*25000000000000^51 ≤ 21646745716703^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358467089 400000000 21646745716703 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1160297159/10000000000 : ℝ)^67 ≤ (1475845040911/25000000000000 : ℝ)^51 := by
    have hnat : (1160297159 : ℕ)^67*25000000000000^51 ≤ 1475845040911^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160297159 10000000000 1475845040911 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1393566993/10000000000 : ℝ)^67 ≤ (7509636955231/100000000000000 : ℝ)^51 := by
    have hnat : (1393566993 : ℕ)^67*100000000000000^51 ≤ 7509636955231^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393566993 10000000000 7509636955231 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(358467089/400000000 : ℝ), (-1160297159/10000000000 : ℝ), (-1393566993/10000000000 : ℝ)] ![(21646745716703/25000000000000 : ℝ), (1475845040911/25000000000000 : ℝ), (7509636955231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(358467089/400000000 : ℝ)|^67 ≤ (21646745716703/25000000000000 : ℝ)^51
        have hw : |(358467089/400000000 : ℝ)|=(358467089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1160297159/10000000000 : ℝ)|^67 ≤ (1475845040911/25000000000000 : ℝ)^51
        have hw : |(-1160297159/10000000000 : ℝ)|=(1160297159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1393566993/10000000000 : ℝ)|^67 ≤ (7509636955231/100000000000000 : ℝ)^51
        have hw : |(-1393566993/10000000000 : ℝ)|=(1393566993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (851792523/5000000000 : ℝ)*x 0 + (5716148831/10000000000 : ℝ)*x 1 + (5191125783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851792523/5000000000 : ℝ)^67 ≤ (9777392655443/100000000000000 : ℝ)^51 := by
    have hnat : (851792523 : ℕ)^67*100000000000000^51 ≤ 9777392655443^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851792523 5000000000 9777392655443 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5716148831/10000000000 : ℝ)^67 ≤ (4796237862917/10000000000000 : ℝ)^51 := by
    have hnat : (5716148831 : ℕ)^67*10000000000000^51 ≤ 4796237862917^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716148831 10000000000 4796237862917 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191125783/10000000000 : ℝ)^67 ≤ (21130114349903/50000000000000 : ℝ)^51 := by
    have hnat : (5191125783 : ℕ)^67*50000000000000^51 ≤ 21130114349903^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191125783 10000000000 21130114349903 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851792523/5000000000 : ℝ), (5716148831/10000000000 : ℝ), (5191125783/10000000000 : ℝ)] ![(9777392655443/100000000000000 : ℝ), (4796237862917/10000000000000 : ℝ), (21130114349903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851792523/5000000000 : ℝ)|^67 ≤ (9777392655443/100000000000000 : ℝ)^51
        have hw : |(851792523/5000000000 : ℝ)|=(851792523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5716148831/10000000000 : ℝ)|^67 ≤ (4796237862917/10000000000000 : ℝ)^51
        have hw : |(5716148831/10000000000 : ℝ)|=(5716148831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191125783/10000000000 : ℝ)|^67 ≤ (21130114349903/50000000000000 : ℝ)^51
        have hw : |(5191125783/10000000000 : ℝ)|=(5191125783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2243981413/10000000000 : ℝ)*x 0 + (1221477617/2500000000 : ℝ)*x 1 + (-5622418911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243981413/10000000000 : ℝ)^67 ≤ (2808325534221/20000000000000 : ℝ)^51 := by
    have hnat : (2243981413 : ℕ)^67*20000000000000^51 ≤ 2808325534221^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243981413 10000000000 2808325534221 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221477617/2500000000 : ℝ)^67 ≤ (39026515818757/100000000000000 : ℝ)^51 := by
    have hnat : (1221477617 : ℕ)^67*100000000000000^51 ≤ 39026515818757^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221477617 2500000000 39026515818757 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5622418911/10000000000 : ℝ)^67 ≤ (9386371299687/20000000000000 : ℝ)^51 := by
    have hnat : (5622418911 : ℕ)^67*20000000000000^51 ≤ 9386371299687^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622418911 10000000000 9386371299687 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243981413/10000000000 : ℝ), (1221477617/2500000000 : ℝ), (-5622418911/10000000000 : ℝ)] ![(2808325534221/20000000000000 : ℝ), (39026515818757/100000000000000 : ℝ), (9386371299687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243981413/10000000000 : ℝ)|^67 ≤ (2808325534221/20000000000000 : ℝ)^51
        have hw : |(2243981413/10000000000 : ℝ)|=(2243981413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1221477617/2500000000 : ℝ)|^67 ≤ (39026515818757/100000000000000 : ℝ)^51
        have hw : |(1221477617/2500000000 : ℝ)|=(1221477617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5622418911/10000000000 : ℝ)|^67 ≤ (9386371299687/20000000000000 : ℝ)^51
        have hw : |(-5622418911/10000000000 : ℝ)|=(5622418911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821612983/10000000000 : ℝ)*x 0 + (1134795987/2000000000 : ℝ)*x 1 + (-5150388069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821612983/10000000000 : ℝ)^67 ≤ (533841520439/5000000000000 : ℝ)^51 := by
    have hnat : (1821612983 : ℕ)^67*5000000000000^51 ≤ 533841520439^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821612983 10000000000 533841520439 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134795987/2000000000 : ℝ)^67 ≤ (11874521888761/25000000000000 : ℝ)^51 := by
    have hnat : (1134795987 : ℕ)^67*25000000000000^51 ≤ 11874521888761^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134795987 2000000000 11874521888761 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150388069/10000000000 : ℝ)^67 ≤ (10456270506981/25000000000000 : ℝ)^51 := by
    have hnat : (5150388069 : ℕ)^67*25000000000000^51 ≤ 10456270506981^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150388069 10000000000 10456270506981 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821612983/10000000000 : ℝ), (1134795987/2000000000 : ℝ), (-5150388069/10000000000 : ℝ)] ![(533841520439/5000000000000 : ℝ), (11874521888761/25000000000000 : ℝ), (10456270506981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821612983/10000000000 : ℝ)|^67 ≤ (533841520439/5000000000000 : ℝ)^51
        have hw : |(-1821612983/10000000000 : ℝ)|=(1821612983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134795987/2000000000 : ℝ)|^67 ≤ (11874521888761/25000000000000 : ℝ)^51
        have hw : |(1134795987/2000000000 : ℝ)|=(1134795987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5150388069/10000000000 : ℝ)|^67 ≤ (10456270506981/25000000000000 : ℝ)^51
        have hw : |(-5150388069/10000000000 : ℝ)|=(5150388069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8737230931/10000000000 : ℝ)*x 0 + (-447743781/10000000000 : ℝ)*x 1 + (-461375469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8737230931/10000000000 : ℝ)^67 ≤ (41874659644919/50000000000000 : ℝ)^51 := by
    have hnat : (8737230931 : ℕ)^67*50000000000000^51 ≤ 41874659644919^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8737230931 10000000000 41874659644919 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447743781/10000000000 : ℝ)^67 ≤ (337950541169/20000000000000 : ℝ)^51 := by
    have hnat : (447743781 : ℕ)^67*20000000000000^51 ≤ 337950541169^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447743781 10000000000 337950541169 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461375469/2000000000 : ℝ)^67 ≤ (14560927996211/100000000000000 : ℝ)^51 := by
    have hnat : (461375469 : ℕ)^67*100000000000000^51 ≤ 14560927996211^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461375469 2000000000 14560927996211 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8737230931/10000000000 : ℝ), (-447743781/10000000000 : ℝ), (-461375469/2000000000 : ℝ)] ![(41874659644919/50000000000000 : ℝ), (337950541169/20000000000000 : ℝ), (14560927996211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8737230931/10000000000 : ℝ)|^67 ≤ (41874659644919/50000000000000 : ℝ)^51
        have hw : |(8737230931/10000000000 : ℝ)|=(8737230931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447743781/10000000000 : ℝ)|^67 ≤ (337950541169/20000000000000 : ℝ)^51
        have hw : |(-447743781/10000000000 : ℝ)|=(447743781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-461375469/2000000000 : ℝ)|^67 ≤ (14560927996211/100000000000000 : ℝ)^51
        have hw : |(-461375469/2000000000 : ℝ)|=(461375469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1683789837/10000000000 : ℝ)*x 0 + (1534236763/2500000000 : ℝ)*x 1 + (476070997/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1683789837/10000000000 : ℝ)^67 ≤ (2407103030533/25000000000000 : ℝ)^51 := by
    have hnat : (1683789837 : ℕ)^67*25000000000000^51 ≤ 2407103030533^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683789837 10000000000 2407103030533 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534236763/2500000000 : ℝ)^67 ≤ (26326773435209/50000000000000 : ℝ)^51 := by
    have hnat : (1534236763 : ℕ)^67*50000000000000^51 ≤ 26326773435209^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534236763 2500000000 26326773435209 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476070997/1000000000 : ℝ)^67 ≤ (18859020492909/50000000000000 : ℝ)^51 := by
    have hnat : (476070997 : ℕ)^67*50000000000000^51 ≤ 18859020492909^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476070997 1000000000 18859020492909 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1683789837/10000000000 : ℝ), (1534236763/2500000000 : ℝ), (476070997/1000000000 : ℝ)] ![(2407103030533/25000000000000 : ℝ), (26326773435209/50000000000000 : ℝ), (18859020492909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1683789837/10000000000 : ℝ)|^67 ≤ (2407103030533/25000000000000 : ℝ)^51
        have hw : |(1683789837/10000000000 : ℝ)|=(1683789837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1534236763/2500000000 : ℝ)|^67 ≤ (26326773435209/50000000000000 : ℝ)^51
        have hw : |(1534236763/2500000000 : ℝ)|=(1534236763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(476070997/1000000000 : ℝ)|^67 ≤ (18859020492909/50000000000000 : ℝ)^51
        have hw : |(476070997/1000000000 : ℝ)|=(476070997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s0_26 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5551960143/10000000000 : ℝ)*x 0 + (5520152991/10000000000 : ℝ)*x 1 + (-1465875307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5551960143/10000000000 : ℝ)^67 ≤ (23080363622529/50000000000000 : ℝ)^51 := by
    have hnat : (5551960143 : ℕ)^67*50000000000000^51 ≤ 23080363622529^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5551960143 10000000000 23080363622529 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520152991/10000000000 : ℝ)^67 ≤ (4581361915233/10000000000000 : ℝ)^51 := by
    have hnat : (5520152991 : ℕ)^67*10000000000000^51 ≤ 4581361915233^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520152991 10000000000 4581361915233 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1465875307/10000000000 : ℝ)^67 ≤ (8025653596997/100000000000000 : ℝ)^51 := by
    have hnat : (1465875307 : ℕ)^67*100000000000000^51 ≤ 8025653596997^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465875307 10000000000 8025653596997 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5551960143/10000000000 : ℝ), (5520152991/10000000000 : ℝ), (-1465875307/10000000000 : ℝ)] ![(23080363622529/50000000000000 : ℝ), (4581361915233/10000000000000 : ℝ), (8025653596997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5551960143/10000000000 : ℝ)|^67 ≤ (23080363622529/50000000000000 : ℝ)^51
        have hw : |(5551960143/10000000000 : ℝ)|=(5551960143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520152991/10000000000 : ℝ)|^67 ≤ (4581361915233/10000000000000 : ℝ)^51
        have hw : |(5520152991/10000000000 : ℝ)|=(5520152991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1465875307/10000000000 : ℝ)|^67 ≤ (8025653596997/100000000000000 : ℝ)^51
        have hw : |(-1465875307/10000000000 : ℝ)|=(1465875307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3686159401/10000000000 : ℝ)*x 0 + (939773723/2000000000 : ℝ)*x 1 + (-4592002479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3686159401/10000000000 : ℝ)^67 ≤ (1684524685179/6250000000000 : ℝ)^51 := by
    have hnat : (3686159401 : ℕ)^67*6250000000000^51 ≤ 1684524685179^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686159401 10000000000 1684524685179 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939773723/2000000000 : ℝ)^67 ≤ (18537844892951/50000000000000 : ℝ)^51 := by
    have hnat : (939773723 : ℕ)^67*50000000000000^51 ≤ 18537844892951^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939773723 2000000000 18537844892951 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4592002479/10000000000 : ℝ)^67 ≤ (35971915231977/100000000000000 : ℝ)^51 := by
    have hnat : (4592002479 : ℕ)^67*100000000000000^51 ≤ 35971915231977^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592002479 10000000000 35971915231977 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3686159401/10000000000 : ℝ), (939773723/2000000000 : ℝ), (-4592002479/10000000000 : ℝ)] ![(1684524685179/6250000000000 : ℝ), (18537844892951/50000000000000 : ℝ), (35971915231977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3686159401/10000000000 : ℝ)|^67 ≤ (1684524685179/6250000000000 : ℝ)^51
        have hw : |(-3686159401/10000000000 : ℝ)|=(3686159401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(939773723/2000000000 : ℝ)|^67 ≤ (18537844892951/50000000000000 : ℝ)^51
        have hw : |(939773723/2000000000 : ℝ)|=(939773723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4592002479/10000000000 : ℝ)|^67 ≤ (35971915231977/100000000000000 : ℝ)^51
        have hw : |(-4592002479/10000000000 : ℝ)|=(4592002479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5719827309/10000000000 : ℝ)*x 0 + (-2690973753/10000000000 : ℝ)*x 1 + (-4415930669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5719827309/10000000000 : ℝ)^67 ≤ (1920117230873/4000000000000 : ℝ)^51 := by
    have hnat : (5719827309 : ℕ)^67*4000000000000^51 ≤ 1920117230873^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719827309 10000000000 1920117230873 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2690973753/10000000000 : ℝ)^67 ≤ (8913074417677/50000000000000 : ℝ)^51 := by
    have hnat : (2690973753 : ℕ)^67*50000000000000^51 ≤ 8913074417677^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690973753 10000000000 8913074417677 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415930669/10000000000 : ℝ)^67 ≤ (34170920376919/100000000000000 : ℝ)^51 := by
    have hnat : (4415930669 : ℕ)^67*100000000000000^51 ≤ 34170920376919^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415930669 10000000000 34170920376919 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5719827309/10000000000 : ℝ), (-2690973753/10000000000 : ℝ), (-4415930669/10000000000 : ℝ)] ![(1920117230873/4000000000000 : ℝ), (8913074417677/50000000000000 : ℝ), (34170920376919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5719827309/10000000000 : ℝ)|^67 ≤ (1920117230873/4000000000000 : ℝ)^51
        have hw : |(5719827309/10000000000 : ℝ)|=(5719827309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2690973753/10000000000 : ℝ)|^67 ≤ (8913074417677/50000000000000 : ℝ)^51
        have hw : |(-2690973753/10000000000 : ℝ)|=(2690973753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4415930669/10000000000 : ℝ)|^67 ≤ (34170920376919/100000000000000 : ℝ)^51
        have hw : |(-4415930669/10000000000 : ℝ)|=(4415930669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3580606633/10000000000 : ℝ)*x 0 + (984902723/2000000000 : ℝ)*x 1 + (892102199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3580606633/10000000000 : ℝ)^67 ≤ (5188614762009/20000000000000 : ℝ)^51 := by
    have hnat : (3580606633 : ℕ)^67*20000000000000^51 ≤ 5188614762009^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3580606633 10000000000 5188614762009 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984902723/2000000000 : ℝ)^67 ≤ (39432097711941/100000000000000 : ℝ)^51 := by
    have hnat : (984902723 : ℕ)^67*100000000000000^51 ≤ 39432097711941^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984902723 2000000000 39432097711941 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892102199/2000000000 : ℝ)^67 ≤ (8656207114603/25000000000000 : ℝ)^51 := by
    have hnat : (892102199 : ℕ)^67*25000000000000^51 ≤ 8656207114603^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892102199 2000000000 8656207114603 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3580606633/10000000000 : ℝ), (984902723/2000000000 : ℝ), (892102199/2000000000 : ℝ)] ![(5188614762009/20000000000000 : ℝ), (39432097711941/100000000000000 : ℝ), (8656207114603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3580606633/10000000000 : ℝ)|^67 ≤ (5188614762009/20000000000000 : ℝ)^51
        have hw : |(3580606633/10000000000 : ℝ)|=(3580606633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984902723/2000000000 : ℝ)|^67 ≤ (39432097711941/100000000000000 : ℝ)^51
        have hw : |(984902723/2000000000 : ℝ)|=(984902723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(892102199/2000000000 : ℝ)|^67 ≤ (8656207114603/25000000000000 : ℝ)^51
        have hw : |(892102199/2000000000 : ℝ)|=(892102199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302022_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (417616233/1000000000 : ℝ)*x 0 + (1376078431/2500000000 : ℝ)*x 1 + (-403020107/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417616233/1000000000 : ℝ)^67 ≤ (793863026113/2500000000000 : ℝ)^51 := by
    have hnat : (417616233 : ℕ)^67*2500000000000^51 ≤ 793863026113^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417616233 1000000000 793863026113 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376078431/2500000000 : ℝ)^67 ≤ (45641000569401/100000000000000 : ℝ)^51 := by
    have hnat : (1376078431 : ℕ)^67*100000000000000^51 ≤ 45641000569401^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376078431 2500000000 45641000569401 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403020107/1250000000 : ℝ)^67 ≤ (22604478369323/100000000000000 : ℝ)^51 := by
    have hnat : (403020107 : ℕ)^67*100000000000000^51 ≤ 22604478369323^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403020107 1250000000 22604478369323 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417616233/1000000000 : ℝ), (1376078431/2500000000 : ℝ), (-403020107/1250000000 : ℝ)] ![(793863026113/2500000000000 : ℝ), (45641000569401/100000000000000 : ℝ), (22604478369323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417616233/1000000000 : ℝ)|^67 ≤ (793863026113/2500000000000 : ℝ)^51
        have hw : |(417616233/1000000000 : ℝ)|=(417616233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376078431/2500000000 : ℝ)|^67 ≤ (45641000569401/100000000000000 : ℝ)^51
        have hw : |(1376078431/2500000000 : ℝ)|=(1376078431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403020107/1250000000 : ℝ)|^67 ≤ (22604478369323/100000000000000 : ℝ)^51
        have hw : |(-403020107/1250000000 : ℝ)|=(403020107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302022 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_2 : ((2553156969/10000000000 : ℝ)*X 2 0+(702878579/1250000000 : ℝ)*X 2 1+(144873639/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-529768683/2000000000 : ℝ)*X 0 0+(174328121/500000000 : ℝ)*X 0 1+(-6561323281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7425731453/10000000000 : ℝ)*X 1 0+(-45999721/2500000000 : ℝ)*X 1 1+(-836888629/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1434028843/10000000000 : ℝ)*X 2 0+(366650009/500000000 : ℝ)*X 2 1+(3552164231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_11 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_11 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2618400999/10000000000 : ℝ)*X 0 0+(1601907219/2000000000 : ℝ)*X 0 1+(-1475484291/10000000000 : ℝ)*X 0 2+(2618400999/10000000000 : ℝ)*X 1 0+(1601907219/2000000000 : ℝ)*X 1 1+(-1475484291/10000000000 : ℝ)*X 1 2+(2618400999/10000000000 : ℝ)*X 2 0+(1601907219/2000000000 : ℝ)*X 2 1+(-1475484291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-50403773/156250000 : ℝ)*X 0 0+(4044734539/10000000000 : ℝ)*X 0 1+(-5622418911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((358467089/400000000 : ℝ)*X 1 0+(-1160297159/10000000000 : ℝ)*X 1 1+(-1393566993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((851792523/5000000000 : ℝ)*X 2 0+(5716148831/10000000000 : ℝ)*X 2 1+(5191125783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2243981413/10000000000 : ℝ)*X 0 0+(1221477617/2500000000 : ℝ)*X 0 1+(-5622418911/10000000000 : ℝ)*X 0 2+(2243981413/10000000000 : ℝ)*X 1 0+(1221477617/2500000000 : ℝ)*X 1 1+(-5622418911/10000000000 : ℝ)*X 1 2+(2243981413/10000000000 : ℝ)*X 2 0+(1221477617/2500000000 : ℝ)*X 2 1+(-5622418911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1821612983/10000000000 : ℝ)*X 0 0+(1134795987/2000000000 : ℝ)*X 0 1+(-5150388069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8737230931/10000000000 : ℝ)*X 1 0+(-447743781/10000000000 : ℝ)*X 1 1+(-461375469/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1683789837/10000000000 : ℝ)*X 2 0+(1534236763/2500000000 : ℝ)*X 2 1+(476070997/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((5551960143/10000000000 : ℝ)*X 0 0+(5520152991/10000000000 : ℝ)*X 0 1+(-1465875307/10000000000 : ℝ)*X 0 2+(5551960143/10000000000 : ℝ)*X 1 0+(5520152991/10000000000 : ℝ)*X 1 1+(-1465875307/10000000000 : ℝ)*X 1 2+(5551960143/10000000000 : ℝ)*X 2 0+(5520152991/10000000000 : ℝ)*X 2 1+(-1465875307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5643/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5643/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11431863263818215077373/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414023/100000000000 : ℝ)*(base18) + (675730976401/1000000000000 : ℝ)*(base39) + (651334845401/1000000000000 : ℝ)*(base50) + (266967/200000000000 : ℝ)*(base53) + (380352640703/1000000000000 : ℝ)*(base60) + (3068312433847/1000000000000 : ℝ)*(major_s0_0) + (4525410925111/1000000000000 : ℝ)*(major_s0_1) + (767077774753/250000000000 : ℝ)*(major_s0_2) + (4079688434039/1000000000000 : ℝ)*(sp_s0_7) + (1019923650937/250000000000 : ℝ)*(sp_s0_8) + (4079700078813/1000000000000 : ℝ)*(sp_s0_9) + (11383581963/7812500000 : ℝ)*(sp_s0_11) + (2056923264629/1000000000000 : ℝ)*(sp_s0_13) + (10309939/1000000000000 : ℝ)*(sp_s0_21) + (2056923264629/1000000000000 : ℝ)*(f.failure) + (4079700078813/1000000000000 : ℝ)*(f.sum) + (6669116643144023/10000000000000000000000000000 : ℝ)*base63 + (1167725678621239/2500000000000000000000000000 : ℝ)*base64 + (3316645516131407/10000000000000000000000000000 : ℝ)*base66 + (1595271166117219/2500000000000000000000000000 : ℝ)*base69 + (8005868165719/16000000000000000000000000 : ℝ)*base70 + (5176571092319439/10000000000000000000000000000 : ℝ)*base73 + (1659237182675147/10000000000000000000000000000 : ℝ)*base75 + (214259438910581/10000000000000000000000000000 : ℝ)*base77 + (13779355657719/78125000000000000000000000 : ℝ)*base79 + (793/10000000000000000 : ℝ)*base87 + (793/10000000000000000 : ℝ)*base89 + (793/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12563/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(12563/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24335900254968530079093/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3700098851/62500000000 : ℝ)*(base1) + (5936713/500000000000 : ℝ)*(base3) + (740698090821/1000000000000 : ℝ)*(base39) + (67769123261/200000000000 : ℝ)*(base60) + (2257848819537/1000000000000 : ℝ)*(major_s0_0) + (2257848819537/1000000000000 : ℝ)*(major_s0_1) + (2257848819537/1000000000000 : ℝ)*(major_s0_2) + (24279211/1000000000000 : ℝ)*(sp_s0_2) + (2838271/31250000000 : ℝ)*(sp_s0_7) + (3061197308137/1000000000000 : ℝ)*(sp_s0_14) + (3002085701879/1000000000000 : ℝ)*(sp_s0_15) + (3002062271981/1000000000000 : ℝ)*(sp_s0_16) + (90899649253/62500000000 : ℝ)*(sp_s0_20) + (636137/50000000000 : ℝ)*(sp_s0_22) + (151360784309/100000000000 : ℝ)*(f.failure) + (3002086551193/1000000000000 : ℝ)*(f.sum) + (47211991/125000000000000000000 : ℝ)*base62 + (3326579361806969/10000000000000000000000000000 : ℝ)*base65 + (1264192541806969/10000000000000000000000000000 : ℝ)*base66 + (4047834574451549/10000000000000000000000000000 : ℝ)*base68 + (65989255517771/500000000000000000000000000 : ℝ)*base71 + (1089916783806969/10000000000000000000000000000 : ℝ)*base73 + (2593186626451549/10000000000000000000000000000 : ℝ)*base75 + (5612733937548451/10000000000000000000000000000 : ℝ)*base77 + (6432187077/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (353/1000000000000000 : ℝ)*base87 + (353/1000000000000000 : ℝ)*base89 + (353/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-39843/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-39843/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26210589141397508846529/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38165753957/40000000000 : ℝ)*(base39) + (600371231917/1000000000000 : ℝ)*(base50) + (574926350343/200000000000 : ℝ)*(major_s0_0) + (753561558829/250000000000 : ℝ)*(major_s0_1) + (574926350343/200000000000 : ℝ)*(major_s0_2) + (19539041/250000000000 : ℝ)*(sp_s0_2) + (16988159/500000000000 : ℝ)*(sp_s0_9) + (139614483601/1000000000000 : ℝ)*(sp_s0_11) + (7939563/1000000000000 : ℝ)*(sp_s0_13) + (15060979/500000000000 : ℝ)*(sp_s0_15) + (3822175640697/1000000000000 : ℝ)*(sp_s0_21) + (3822145518739/1000000000000 : ℝ)*(sp_s0_22) + (764412701643/200000000000 : ℝ)*(sp_s0_23) + (15055284597/7812500000 : ℝ)*(sp_s0_26) + (1927084367979/1000000000000 : ℝ)*(f.failure) + (3822175640697/1000000000000 : ℝ)*(f.sum) + (4674130984022877/10000000000000000000000000000 : ℝ)*base63 + (1415359824762591/2000000000000000000000000000 : ℝ)*base65 + (2110329277716373/2500000000000000000000000000 : ℝ)*base66 + (1239158413642789/2000000000000000000000000000 : ℝ)*base69 + (30445048520269/100000000000000000000000000 : ℝ)*base71 + (762427729237409/2000000000000000000000000000 : ℝ)*base72 + (2047935583952233/2500000000000000000000000000 : ℝ)*base75 + (1469057148642789/2000000000000000000000000000 : ℝ)*base77 + (2744759124052537/10000000000000000000000000000 : ℝ)*base78 + (7257/10000000000000000 : ℝ)*base86 + (7257/10000000000000000 : ℝ)*base88 + (7257/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (5643/12500 : ℝ) ^ (65/16 : ℝ) ≤ (79039220233531483/2000000000000000000 : ℝ) := by
    have hpowers : (5643/12500 : ℝ)^65 ≤ (79039220233531483/2000000000000000000 : ℝ)^16 := by
      have hnat : (5643 : ℕ)^65*2000000000000000000^16 ≤ 79039220233531483^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 12500 79039220233531483 2000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/12500 : ℝ)) (X := (79039220233531483/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2079039220233531483/2000000000000000000 : ℝ) ≤ (2523965644986983/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2079039220233531483/2000000000000000000 : ℝ)^16 ≤ (2523965644986983/2500000000000000 : ℝ)^65 := by
      have hnat : (2079039220233531483 : ℕ)^16*2500000000000000^65 ≤ 2523965644986983^65*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2079039220233531483 2000000000000000000 2523965644986983 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523965644986983/2500000000000000 : ℝ)) (X := (2079039220233531483/2000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1079039220233531483/1000000000000000000 : ℝ) ≤ (10189015932311229/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (1079039220233531483/1000000000000000000 : ℝ)^16 ≤ (10189015932311229/10000000000000000 : ℝ)^65 := by
      have hnat : (1079039220233531483 : ℕ)^16*10000000000000000^65 ≤ 10189015932311229^65*1000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079039220233531483 1000000000000000000 10189015932311229 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10189015932311229/10000000000000000 : ℝ)) (X := (1079039220233531483/1000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1261349736157/59400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(93153352363297/4514400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (5643/12500 : ℝ)) (alpha := (1261349736157/59400000000000 : ℝ)) (beta := (93153352363297/4514400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5643/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1261349736157/59400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(93153352363297/4514400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (12563/50000 : ℝ) ^ (65/16 : ℝ) ≤ (365595744094879417/100000000000000000000 : ℝ) := by
    have hpowers : (12563/50000 : ℝ)^65 ≤ (365595744094879417/100000000000000000000 : ℝ)^16 := by
      have hnat : (12563 : ℕ)^65*100000000000000000000^16 ≤ 365595744094879417^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12563 50000 365595744094879417 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12563/50000 : ℝ)) (X := (365595744094879417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100365595744094879417/100000000000000000000 : ℝ) ≤ (40035947620613/40000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100365595744094879417/100000000000000000000 : ℝ)^16 ≤ (40035947620613/40000000000000 : ℝ)^65 := by
      have hnat : (100365595744094879417 : ℕ)^16*40000000000000^65 ≤ 40035947620613^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100365595744094879417 100000000000000000000 40035947620613 40000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40035947620613/40000000000000 : ℝ)) (X := (100365595744094879417/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50365595744094879417/50000000000000000000 : ℝ) ≤ (1001794916612951/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50365595744094879417/50000000000000000000 : ℝ)^16 ≤ (1001794916612951/1000000000000000 : ℝ)^65 := by
      have hnat : (50365595744094879417 : ℕ)^16*1000000000000000^65 ≤ 1001794916612951^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50365595744094879417 50000000000000000000 1001794916612951 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001794916612951/1000000000000000 : ℝ)) (X := (50365595744094879417/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(35947620613/10050400000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(448113048813/125630000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (12563/50000 : ℝ)) (alpha := (35947620613/10050400000000 : ℝ)) (beta := (448113048813/125630000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (12563/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(35947620613/10050400000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(448113048813/125630000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (39843/100000 : ℝ) ^ (65/16 : ℝ) ≤ (2379195488387984837/100000000000000000000 : ℝ) := by
    have hpowers : (39843/100000 : ℝ)^65 ≤ (2379195488387984837/100000000000000000000 : ℝ)^16 := by
      have hnat : (39843 : ℕ)^65*100000000000000000000^16 ≤ 2379195488387984837^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39843 100000 2379195488387984837 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39843/100000 : ℝ)) (X := (2379195488387984837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102379195488387984837/100000000000000000000 : ℝ) ≤ (2011609361127699/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (102379195488387984837/100000000000000000000 : ℝ)^16 ≤ (2011609361127699/2000000000000000 : ℝ)^65 := by
      have hnat : (102379195488387984837 : ℕ)^16*2000000000000000^65 ≤ 2011609361127699^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102379195488387984837 100000000000000000000 2011609361127699 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011609361127699/2000000000000000 : ℝ)) (X := (102379195488387984837/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52379195488387984837/50000000000000000000 : ℝ) ≤ (505754272007921/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (52379195488387984837/50000000000000000000 : ℝ)^16 ≤ (505754272007921/500000000000000 : ℝ)^65 := by
      have hnat : (52379195488387984837 : ℕ)^16*500000000000000^65 ≤ 505754272007921^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52379195488387984837 50000000000000000000 505754272007921 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505754272007921/500000000000000 : ℝ)) (X := (52379195488387984837/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(611019006721/41940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2281545380797/159372000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (39843/100000 : ℝ)) (alpha := (611019006721/41940000000000 : ℝ)) (beta := (2281545380797/159372000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39843/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(611019006721/41940000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2281545380797/159372000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3686159401/10000000000 : ℝ)*X 0 0+(939773723/2000000000 : ℝ)*X 0 1+(-4592002479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5719827309/10000000000 : ℝ)*X 1 0+(-2690973753/10000000000 : ℝ)*X 1 1+(-4415930669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3580606633/10000000000 : ℝ)*X 2 0+(984902723/2000000000 : ℝ)*X 2 1+(892102199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((417616233/1000000000 : ℝ)*X 0 0+(1376078431/2500000000 : ℝ)*X 0 1+(-403020107/1250000000 : ℝ)*X 0 2+(417616233/1000000000 : ℝ)*X 1 0+(1376078431/2500000000 : ℝ)*X 1 1+(-403020107/1250000000 : ℝ)*X 1 2+(417616233/1000000000 : ℝ)*X 2 0+(1376078431/2500000000 : ℝ)*X 2 1+(-403020107/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302022_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-163175198091933188054623686704767/27530118495000000000000000000000 : ℝ) := by norm_num
    linear_combination (95363/1000000000000 : ℝ)*(base3) + (489/31250000000 : ℝ)*(base5) + (7127/1000000000000 : ℝ)*(base12) + (66510002671/250000000000 : ℝ)*(base39) + (2936465733/31250000000 : ℝ)*(base49) + (72264345529/200000000000 : ℝ)*(base50) + (4211/200000000000 : ℝ)*(base53) + (17130014421/500000000000 : ℝ)*(base60) + (14917/10000 : ℝ)*(major_s1_0) + (14917/10000 : ℝ)*(major_s1_1) + (298339995789/200000000000 : ℝ)*(major_s1_2) + (987858659803/500000000000 : ℝ)*(sp_s1_0) + (395143484419/200000000000 : ℝ)*(sp_s1_1) + (395143472687/200000000000 : ℝ)*(sp_s1_2) + (999999888989/1000000000000 : ℝ)*(sp_s1_6) + (1975717347787/1000000000000 : ℝ)*(f.sum) + (4357658956592397/58543580000000000000000000000 : ℝ)*base62 + (46533235360421/88540000000000000000000000 : ℝ)*base65 + (23129681925027/62815000000000000000000000 : ℝ)*base67 + (232268473229/932000000000000000000000 : ℝ)*base68 + (16868112072357587/26296380000000000000000000000 : ℝ)*base71 + (28054326312377/56430000000000000000000000 : ℝ)*base73 + (1423161490713/5025200000000000000000000 : ℝ)*base75 + (577458789383/2970000000000000000000000 : ℝ)*base77 + (58841235101257831/708930090000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c302024_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-984868939/2000000000 : ℝ)*x 0 + (1531912337/5000000000 : ℝ)*x 1 + (-2462172347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984868939/2000000000 : ℝ)^67 ≤ (9857580195913/25000000000000 : ℝ)^51 := by
    have hnat : (984868939 : ℕ)^67*25000000000000^51 ≤ 9857580195913^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984868939 2000000000 9857580195913 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531912337/5000000000 : ℝ)^67 ≤ (21139358428429/100000000000000 : ℝ)^51 := by
    have hnat : (1531912337 : ℕ)^67*100000000000000^51 ≤ 21139358428429^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531912337 5000000000 21139358428429 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462172347/5000000000 : ℝ)^67 ≤ (39430320773133/100000000000000 : ℝ)^51 := by
    have hnat : (2462172347 : ℕ)^67*100000000000000^51 ≤ 39430320773133^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462172347 5000000000 39430320773133 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-984868939/2000000000 : ℝ), (1531912337/5000000000 : ℝ), (-2462172347/5000000000 : ℝ)] ![(9857580195913/25000000000000 : ℝ), (21139358428429/100000000000000 : ℝ), (39430320773133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-984868939/2000000000 : ℝ)|^67 ≤ (9857580195913/25000000000000 : ℝ)^51
        have hw : |(-984868939/2000000000 : ℝ)|=(984868939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1531912337/5000000000 : ℝ)|^67 ≤ (21139358428429/100000000000000 : ℝ)^51
        have hw : |(1531912337/5000000000 : ℝ)|=(1531912337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2462172347/5000000000 : ℝ)|^67 ≤ (39430320773133/100000000000000 : ℝ)^51
        have hw : |(-2462172347/5000000000 : ℝ)|=(2462172347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302024_s0_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (984868939/2000000000 : ℝ)*x 0 + (-1531912337/5000000000 : ℝ)*x 1 + (-2462172347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984868939/2000000000 : ℝ)^67 ≤ (9857580195913/25000000000000 : ℝ)^51 := by
    have hnat : (984868939 : ℕ)^67*25000000000000^51 ≤ 9857580195913^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984868939 2000000000 9857580195913 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531912337/5000000000 : ℝ)^67 ≤ (21139358428429/100000000000000 : ℝ)^51 := by
    have hnat : (1531912337 : ℕ)^67*100000000000000^51 ≤ 21139358428429^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531912337 5000000000 21139358428429 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462172347/5000000000 : ℝ)^67 ≤ (39430320773133/100000000000000 : ℝ)^51 := by
    have hnat : (2462172347 : ℕ)^67*100000000000000^51 ≤ 39430320773133^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462172347 5000000000 39430320773133 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(984868939/2000000000 : ℝ), (-1531912337/5000000000 : ℝ), (-2462172347/5000000000 : ℝ)] ![(9857580195913/25000000000000 : ℝ), (21139358428429/100000000000000 : ℝ), (39430320773133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(984868939/2000000000 : ℝ)|^67 ≤ (9857580195913/25000000000000 : ℝ)^51
        have hw : |(984868939/2000000000 : ℝ)|=(984868939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1531912337/5000000000 : ℝ)|^67 ≤ (21139358428429/100000000000000 : ℝ)^51
        have hw : |(-1531912337/5000000000 : ℝ)|=(1531912337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2462172347/5000000000 : ℝ)|^67 ≤ (39430320773133/100000000000000 : ℝ)^51
        have hw : |(-2462172347/5000000000 : ℝ)|=(2462172347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302024_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (108157193/312500000 : ℝ)*x 0 + (1483504951/2500000000 : ℝ)*x 1 + (138441207/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108157193/312500000 : ℝ)^67 ≤ (4962178301021/20000000000000 : ℝ)^51 := by
    have hnat : (108157193 : ℕ)^67*20000000000000^51 ≤ 4962178301021^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108157193 312500000 4962178301021 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1483504951/2500000000 : ℝ)^67 ≤ (50378216981391/100000000000000 : ℝ)^51 := by
    have hnat : (1483504951 : ℕ)^67*100000000000000^51 ≤ 50378216981391^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483504951 2500000000 50378216981391 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138441207/400000000 : ℝ)^67 ≤ (3101361436961/12500000000000 : ℝ)^51 := by
    have hnat : (138441207 : ℕ)^67*12500000000000^51 ≤ 3101361436961^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138441207 400000000 3101361436961 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108157193/312500000 : ℝ), (1483504951/2500000000 : ℝ), (138441207/400000000 : ℝ)] ![(4962178301021/20000000000000 : ℝ), (50378216981391/100000000000000 : ℝ), (3101361436961/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108157193/312500000 : ℝ)|^67 ≤ (4962178301021/20000000000000 : ℝ)^51
        have hw : |(108157193/312500000 : ℝ)|=(108157193/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1483504951/2500000000 : ℝ)|^67 ≤ (50378216981391/100000000000000 : ℝ)^51
        have hw : |(1483504951/2500000000 : ℝ)|=(1483504951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138441207/400000000 : ℝ)|^67 ≤ (3101361436961/12500000000000 : ℝ)^51
        have hw : |(138441207/400000000 : ℝ)|=(138441207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302024_s0_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (108157193/312500000 : ℝ)*x 0 + (1483504951/2500000000 : ℝ)*x 1 + (-138441207/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108157193/312500000 : ℝ)^67 ≤ (4962178301021/20000000000000 : ℝ)^51 := by
    have hnat : (108157193 : ℕ)^67*20000000000000^51 ≤ 4962178301021^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108157193 312500000 4962178301021 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1483504951/2500000000 : ℝ)^67 ≤ (50378216981391/100000000000000 : ℝ)^51 := by
    have hnat : (1483504951 : ℕ)^67*100000000000000^51 ≤ 50378216981391^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483504951 2500000000 50378216981391 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138441207/400000000 : ℝ)^67 ≤ (3101361436961/12500000000000 : ℝ)^51 := by
    have hnat : (138441207 : ℕ)^67*12500000000000^51 ≤ 3101361436961^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138441207 400000000 3101361436961 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108157193/312500000 : ℝ), (1483504951/2500000000 : ℝ), (-138441207/400000000 : ℝ)] ![(4962178301021/20000000000000 : ℝ), (50378216981391/100000000000000 : ℝ), (3101361436961/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108157193/312500000 : ℝ)|^67 ≤ (4962178301021/20000000000000 : ℝ)^51
        have hw : |(108157193/312500000 : ℝ)|=(108157193/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1483504951/2500000000 : ℝ)|^67 ≤ (50378216981391/100000000000000 : ℝ)^51
        have hw : |(1483504951/2500000000 : ℝ)|=(1483504951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138441207/400000000 : ℝ)|^67 ≤ (3101361436961/12500000000000 : ℝ)^51
        have hw : |(-138441207/400000000 : ℝ)|=(138441207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302024 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-984868939/2000000000 : ℝ)*X 0 0+(1531912337/5000000000 : ℝ)*X 0 1+(-2462172347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302024_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((984868939/2000000000 : ℝ)*X 1 0+(-1531912337/5000000000 : ℝ)*X 1 1+(-2462172347/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302024_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((108157193/312500000 : ℝ)*X 2 0+(1483504951/2500000000 : ℝ)*X 2 1+(138441207/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302024_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((108157193/312500000 : ℝ)*X 0 0+(1483504951/2500000000 : ℝ)*X 0 1+(-138441207/400000000 : ℝ)*X 0 2+(108157193/312500000 : ℝ)*X 1 0+(1483504951/2500000000 : ℝ)*X 1 1+(-138441207/400000000 : ℝ)*X 1 2+(108157193/312500000 : ℝ)*X 2 0+(1483504951/2500000000 : ℝ)*X 2 1+(-138441207/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302024_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-743055751384066457428294953/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12443736649/40000000000 : ℝ)*(base5) + (4281/1000000000000 : ℝ)*(base18) + (8209/1000000000000 : ℝ)*(base33) + (45912418053/500000000000 : ℝ)*(base39) + (54821519867/200000000000 : ℝ)*(base49) + (4557069153/25000000000 : ℝ)*(base50) + (1283/200000000000 : ℝ)*(base54) + (145058826013/500000000000 : ℝ)*(base59) + (1491699991791/1000000000000 : ℝ)*(major_s0_0) + (14917/10000 : ℝ)*(major_s0_1) + (298339998717/200000000000 : ℝ)*(major_s0_2) + (1981482003687/1000000000000 : ℝ)*(sp_s0_0) + (1981481991197/1000000000000 : ℝ)*(sp_s0_1) + (286571925661/125000000000 : ℝ)*(sp_s0_2) + (8611332217/12500000000 : ℝ)*(sp_s0_6) + (1981482003687/1000000000000 : ℝ)*(f.sum) + (1163310887743591/2000000000000000000000000000 : ℝ)*base62 + (823840935010629/2000000000000000000000000000 : ℝ)*base64 + (1017136161/5000000000000000000000 : ℝ)*base66 + (1114295143743591/2000000000000000000000000000 : ℝ)*base68 + (933955876217663/2500000000000000000000000000 : ℝ)*base70 + (5974180045677433/10000000000000000000000000000 : ℝ)*base72 + (2078501287/2500000000000000000000 : ℝ)*base74 + (1241947637817507/10000000000000000000000000000 : ℝ)*base76 + (1631401263677433/10000000000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b011 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=22 ∨ c=23 ∨ c=24 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c302022 p hpa (by linarith only [hpb]) X hX
  · exact collision_c10023 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c302024 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b011 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
