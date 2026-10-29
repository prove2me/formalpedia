-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:56:39.844793+00:00
-- url     : https://prove2.me/submissions/910d58d2-f2be-4c0b-b30d-013d5d1a6b3c

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
theorem collision_support_c324049_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3217107791/10000000000 : ℝ)*x 0 + (402138481/1250000000 : ℝ)*x 1 + (2860314501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3217107791/10000000000 : ℝ)^43 ≤ (1551552020407/6250000000000 : ℝ)^35 := by
    have hnat : (3217107791 : ℕ)^43*6250000000000^35 ≤ 1551552020407^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3217107791 10000000000 1551552020407 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402138481/1250000000 : ℝ)^43 ≤ (3103104108361/12500000000000 : ℝ)^35 := by
    have hnat : (402138481 : ℕ)^43*12500000000000^35 ≤ 3103104108361^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402138481 1250000000 3103104108361 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2860314501/5000000000 : ℝ)^43 ≤ (50350334790483/100000000000000 : ℝ)^35 := by
    have hnat : (2860314501 : ℕ)^43*100000000000000^35 ≤ 50350334790483^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860314501 5000000000 50350334790483 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3217107791/10000000000 : ℝ), (402138481/1250000000 : ℝ), (2860314501/5000000000 : ℝ)] ![(1551552020407/6250000000000 : ℝ), (3103104108361/12500000000000 : ℝ), (50350334790483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3217107791/10000000000 : ℝ)|^43 ≤ (1551552020407/6250000000000 : ℝ)^35
        have hw : |(-3217107791/10000000000 : ℝ)|=(3217107791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402138481/1250000000 : ℝ)|^43 ≤ (3103104108361/12500000000000 : ℝ)^35
        have hw : |(402138481/1250000000 : ℝ)|=(402138481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2860314501/5000000000 : ℝ)|^43 ≤ (50350334790483/100000000000000 : ℝ)^35
        have hw : |(2860314501/5000000000 : ℝ)|=(2860314501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2423391449/10000000000 : ℝ)*x 0 + (-605847873/2500000000 : ℝ)*x 1 + (7037537999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2423391449/10000000000 : ℝ)^43 ≤ (17527516612111/100000000000000 : ℝ)^35 := by
    have hnat : (2423391449 : ℕ)^43*100000000000000^35 ≤ 17527516612111^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423391449 10000000000 17527516612111 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605847873/2500000000 : ℝ)^43 ≤ (17527516994201/100000000000000 : ℝ)^35 := by
    have hnat : (605847873 : ℕ)^43*100000000000000^35 ≤ 17527516994201^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605847873 2500000000 17527516994201 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7037537999/10000000000 : ℝ)^43 ≤ (64944966382219/100000000000000 : ℝ)^35 := by
    have hnat : (7037537999 : ℕ)^43*100000000000000^35 ≤ 64944966382219^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7037537999 10000000000 64944966382219 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2423391449/10000000000 : ℝ), (-605847873/2500000000 : ℝ), (7037537999/10000000000 : ℝ)] ![(17527516612111/100000000000000 : ℝ), (17527516994201/100000000000000 : ℝ), (64944966382219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2423391449/10000000000 : ℝ)|^43 ≤ (17527516612111/100000000000000 : ℝ)^35
        have hw : |(2423391449/10000000000 : ℝ)|=(2423391449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605847873/2500000000 : ℝ)|^43 ≤ (17527516994201/100000000000000 : ℝ)^35
        have hw : |(-605847873/2500000000 : ℝ)|=(605847873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7037537999/10000000000 : ℝ)|^43 ≤ (64944966382219/100000000000000 : ℝ)^35
        have hw : |(7037537999/10000000000 : ℝ)|=(7037537999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2783230017/10000000000 : ℝ)*x 0 + (1776886667/10000000000 : ℝ)*x 1 + (7240277341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2783230017/10000000000 : ℝ)^43 ≤ (5194322407881/25000000000000 : ℝ)^35 := by
    have hnat : (2783230017 : ℕ)^43*25000000000000^35 ≤ 5194322407881^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783230017 10000000000 5194322407881 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1776886667/10000000000 : ℝ)^43 ≤ (478865304717/4000000000000 : ℝ)^35 := by
    have hnat : (1776886667 : ℕ)^43*4000000000000^35 ≤ 478865304717^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776886667 10000000000 478865304717 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7240277341/10000000000 : ℝ)^43 ≤ (67251077735121/100000000000000 : ℝ)^35 := by
    have hnat : (7240277341 : ℕ)^43*100000000000000^35 ≤ 67251077735121^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7240277341 10000000000 67251077735121 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2783230017/10000000000 : ℝ), (1776886667/10000000000 : ℝ), (7240277341/10000000000 : ℝ)] ![(5194322407881/25000000000000 : ℝ), (478865304717/4000000000000 : ℝ), (67251077735121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2783230017/10000000000 : ℝ)|^43 ≤ (5194322407881/25000000000000 : ℝ)^35
        have hw : |(-2783230017/10000000000 : ℝ)|=(2783230017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1776886667/10000000000 : ℝ)|^43 ≤ (478865304717/4000000000000 : ℝ)^35
        have hw : |(1776886667/10000000000 : ℝ)|=(1776886667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7240277341/10000000000 : ℝ)|^43 ≤ (67251077735121/100000000000000 : ℝ)^35
        have hw : |(7240277341/10000000000 : ℝ)|=(7240277341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (74932091/500000000 : ℝ)*x 0 + (-969166471/10000000000 : ℝ)*x 1 + (4363833779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74932091/500000000 : ℝ)^43 ≤ (2427872833551/25000000000000 : ℝ)^35 := by
    have hnat : (74932091 : ℕ)^43*25000000000000^35 ≤ 2427872833551^35*500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74932091 500000000 2427872833551 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969166471/10000000000 : ℝ)^43 ≤ (2842418461811/50000000000000 : ℝ)^35 := by
    have hnat : (969166471 : ℕ)^43*50000000000000^35 ≤ 2842418461811^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969166471 10000000000 2842418461811 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4363833779/5000000000 : ℝ)^43 ≤ (84603671724733/100000000000000 : ℝ)^35 := by
    have hnat : (4363833779 : ℕ)^43*100000000000000^35 ≤ 84603671724733^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363833779 5000000000 84603671724733 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(74932091/500000000 : ℝ), (-969166471/10000000000 : ℝ), (4363833779/5000000000 : ℝ)] ![(2427872833551/25000000000000 : ℝ), (2842418461811/50000000000000 : ℝ), (84603671724733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(74932091/500000000 : ℝ)|^43 ≤ (2427872833551/25000000000000 : ℝ)^35
        have hw : |(74932091/500000000 : ℝ)|=(74932091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969166471/10000000000 : ℝ)|^43 ≤ (2842418461811/50000000000000 : ℝ)^35
        have hw : |(-969166471/10000000000 : ℝ)|=(969166471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4363833779/5000000000 : ℝ)|^43 ≤ (84603671724733/100000000000000 : ℝ)^35
        have hw : |(4363833779/5000000000 : ℝ)|=(4363833779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3663388569/10000000000 : ℝ)*x 0 + (3757993553/5000000000 : ℝ)*x 1 + (-63545969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3663388569/10000000000 : ℝ)^43 ≤ (2912051806749/10000000000000 : ℝ)^35 := by
    have hnat : (3663388569 : ℕ)^43*10000000000000^35 ≤ 2912051806749^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663388569 10000000000 2912051806749 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3757993553/5000000000 : ℝ)^43 ≤ (35205456461599/50000000000000 : ℝ)^35 := by
    have hnat : (3757993553 : ℕ)^43*50000000000000^35 ≤ 35205456461599^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3757993553 5000000000 35205456461599 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63545969/5000000000 : ℝ)^43 ≤ (468568992243/100000000000000 : ℝ)^35 := by
    have hnat : (63545969 : ℕ)^43*100000000000000^35 ≤ 468568992243^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63545969 5000000000 468568992243 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3663388569/10000000000 : ℝ), (3757993553/5000000000 : ℝ), (-63545969/5000000000 : ℝ)] ![(2912051806749/10000000000000 : ℝ), (35205456461599/50000000000000 : ℝ), (468568992243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3663388569/10000000000 : ℝ)|^43 ≤ (2912051806749/10000000000000 : ℝ)^35
        have hw : |(3663388569/10000000000 : ℝ)|=(3663388569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3757993553/5000000000 : ℝ)|^43 ≤ (35205456461599/50000000000000 : ℝ)^35
        have hw : |(3757993553/5000000000 : ℝ)|=(3757993553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63545969/5000000000 : ℝ)|^43 ≤ (468568992243/100000000000000 : ℝ)^35
        have hw : |(-63545969/5000000000 : ℝ)|=(63545969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_12 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3655519371/10000000000 : ℝ)*x 0 + (7502286169/10000000000 : ℝ)*x 1 + (44206989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3655519371/10000000000 : ℝ)^43 ≤ (5808737278303/20000000000000 : ℝ)^35 := by
    have hnat : (3655519371 : ℕ)^43*20000000000000^35 ≤ 5808737278303^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3655519371 10000000000 5808737278303 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7502286169/10000000000 : ℝ)^43 ≤ (17563313904399/25000000000000 : ℝ)^35 := by
    have hnat : (7502286169 : ℕ)^43*25000000000000^35 ≤ 17563313904399^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7502286169 10000000000 17563313904399 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44206989/2500000000 : ℝ)^43 ≤ (175764493647/25000000000000 : ℝ)^35 := by
    have hnat : (44206989 : ℕ)^43*25000000000000^35 ≤ 175764493647^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44206989 2500000000 175764493647 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3655519371/10000000000 : ℝ), (7502286169/10000000000 : ℝ), (44206989/2500000000 : ℝ)] ![(5808737278303/20000000000000 : ℝ), (17563313904399/25000000000000 : ℝ), (175764493647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3655519371/10000000000 : ℝ)|^43 ≤ (5808737278303/20000000000000 : ℝ)^35
        have hw : |(3655519371/10000000000 : ℝ)|=(3655519371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7502286169/10000000000 : ℝ)|^43 ≤ (17563313904399/25000000000000 : ℝ)^35
        have hw : |(7502286169/10000000000 : ℝ)|=(7502286169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44206989/2500000000 : ℝ)|^43 ≤ (175764493647/25000000000000 : ℝ)^35
        have hw : |(44206989/2500000000 : ℝ)|=(44206989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-894498811/5000000000 : ℝ)*x 0 + (17327477/62500000 : ℝ)*x 1 + (7240188989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894498811/5000000000 : ℝ)^43 ≤ (241439156321/2000000000000 : ℝ)^35 := by
    have hnat : (894498811 : ℕ)^43*2000000000000^35 ≤ 241439156321^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894498811 5000000000 241439156321 2000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17327477/62500000 : ℝ)^43 ≤ (20677972662991/100000000000000 : ℝ)^35 := by
    have hnat : (17327477 : ℕ)^43*100000000000000^35 ≤ 20677972662991^35*62500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17327477 62500000 20677972662991 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7240188989/10000000000 : ℝ)^43 ≤ (210156467199/312500000000 : ℝ)^35 := by
    have hnat : (7240188989 : ℕ)^43*312500000000^35 ≤ 210156467199^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7240188989 10000000000 210156467199 312500000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894498811/5000000000 : ℝ), (17327477/62500000 : ℝ), (7240188989/10000000000 : ℝ)] ![(241439156321/2000000000000 : ℝ), (20677972662991/100000000000000 : ℝ), (210156467199/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894498811/5000000000 : ℝ)|^43 ≤ (241439156321/2000000000000 : ℝ)^35
        have hw : |(-894498811/5000000000 : ℝ)|=(894498811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17327477/62500000 : ℝ)|^43 ≤ (20677972662991/100000000000000 : ℝ)^35
        have hw : |(17327477/62500000 : ℝ)|=(17327477/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7240188989/10000000000 : ℝ)|^43 ≤ (210156467199/312500000000 : ℝ)^35
        have hw : |(7240188989/10000000000 : ℝ)|=(7240188989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (239495091/2500000000 : ℝ)*x 0 + (-377335981/2500000000 : ℝ)*x 1 + (1090908403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239495091/2500000000 : ℝ)^43 ≤ (1401082925497/25000000000000 : ℝ)^35 := by
    have hnat : (239495091 : ℕ)^43*25000000000000^35 ≤ 1401082925497^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239495091 2500000000 1401082925497 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377335981/2500000000 : ℝ)^43 ≤ (9796764288369/100000000000000 : ℝ)^35 := by
    have hnat : (377335981 : ℕ)^43*100000000000000^35 ≤ 9796764288369^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377335981 2500000000 9796764288369 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090908403/1250000000 : ℝ)^43 ≤ (5287431499689/6250000000000 : ℝ)^35 := by
    have hnat : (1090908403 : ℕ)^43*6250000000000^35 ≤ 5287431499689^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090908403 1250000000 5287431499689 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(239495091/2500000000 : ℝ), (-377335981/2500000000 : ℝ), (1090908403/1250000000 : ℝ)] ![(1401082925497/25000000000000 : ℝ), (9796764288369/100000000000000 : ℝ), (5287431499689/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(239495091/2500000000 : ℝ)|^43 ≤ (1401082925497/25000000000000 : ℝ)^35
        have hw : |(239495091/2500000000 : ℝ)|=(239495091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377335981/2500000000 : ℝ)|^43 ≤ (9796764288369/100000000000000 : ℝ)^35
        have hw : |(-377335981/2500000000 : ℝ)|=(377335981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090908403/1250000000 : ℝ)|^43 ≤ (5287431499689/6250000000000 : ℝ)^35
        have hw : |(1090908403/1250000000 : ℝ)|=(1090908403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1879273723/2500000000 : ℝ)*x 0 + (916217519/2500000000 : ℝ)*x 1 + (-756559/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879273723/2500000000 : ℝ)^43 ≤ (35211831569679/50000000000000 : ℝ)^35 := by
    have hnat : (1879273723 : ℕ)^43*50000000000000^35 ≤ 35211831569679^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879273723 2500000000 35211831569679 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916217519/2500000000 : ℝ)^43 ≤ (29134987126901/100000000000000 : ℝ)^35 := by
    have hnat : (916217519 : ℕ)^43*100000000000000^35 ≤ 29134987126901^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916217519 2500000000 29134987126901 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (756559/62500000 : ℝ)^43 ≤ (55168714277/12500000000000 : ℝ)^35 := by
    have hnat : (756559 : ℕ)^43*12500000000000^35 ≤ 55168714277^35*62500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756559 62500000 55168714277 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1879273723/2500000000 : ℝ), (916217519/2500000000 : ℝ), (-756559/62500000 : ℝ)] ![(35211831569679/50000000000000 : ℝ), (29134987126901/100000000000000 : ℝ), (55168714277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1879273723/2500000000 : ℝ)|^43 ≤ (35211831569679/50000000000000 : ℝ)^35
        have hw : |(1879273723/2500000000 : ℝ)|=(1879273723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916217519/2500000000 : ℝ)|^43 ≤ (29134987126901/100000000000000 : ℝ)^35
        have hw : |(916217519/2500000000 : ℝ)|=(916217519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-756559/62500000 : ℝ)|^43 ≤ (55168714277/12500000000000 : ℝ)^35
        have hw : |(-756559/62500000 : ℝ)|=(756559/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_18 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7499485743/10000000000 : ℝ)*x 0 + (1827377267/5000000000 : ℝ)*x 1 + (184909927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7499485743/10000000000 : ℝ)^43 ≤ (17555259770961/25000000000000 : ℝ)^35 := by
    have hnat : (7499485743 : ℕ)^43*25000000000000^35 ≤ 17555259770961^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7499485743 10000000000 17555259770961 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827377267/5000000000 : ℝ)^43 ≤ (14518110422857/50000000000000 : ℝ)^35 := by
    have hnat : (1827377267 : ℕ)^43*50000000000000^35 ≤ 14518110422857^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827377267 5000000000 14518110422857 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184909927/10000000000 : ℝ)^43 ≤ (74274006357/10000000000000 : ℝ)^35 := by
    have hnat : (184909927 : ℕ)^43*10000000000000^35 ≤ 74274006357^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184909927 10000000000 74274006357 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7499485743/10000000000 : ℝ), (1827377267/5000000000 : ℝ), (184909927/10000000000 : ℝ)] ![(17555259770961/25000000000000 : ℝ), (14518110422857/50000000000000 : ℝ), (74274006357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7499485743/10000000000 : ℝ)|^43 ≤ (17555259770961/25000000000000 : ℝ)^35
        have hw : |(7499485743/10000000000 : ℝ)|=(7499485743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1827377267/5000000000 : ℝ)|^43 ≤ (14518110422857/50000000000000 : ℝ)^35
        have hw : |(1827377267/5000000000 : ℝ)|=(1827377267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184909927/10000000000 : ℝ)|^43 ≤ (74274006357/10000000000000 : ℝ)^35
        have hw : |(184909927/10000000000 : ℝ)|=(184909927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_19 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4228795887/10000000000 : ℝ)*x 0 + (316138281/1250000000 : ℝ)*x 1 + (5389373501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228795887/10000000000 : ℝ)^43 ≤ (34736059168239/100000000000000 : ℝ)^35 := by
    have hnat : (4228795887 : ℕ)^43*100000000000000^35 ≤ 34736059168239^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228795887 10000000000 34736059168239 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316138281/1250000000 : ℝ)^43 ≤ (18471510272461/100000000000000 : ℝ)^35 := by
    have hnat : (316138281 : ℕ)^43*100000000000000^35 ≤ 18471510272461^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316138281 1250000000 18471510272461 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389373501/10000000000 : ℝ)^43 ≤ (9358486109187/20000000000000 : ℝ)^35 := by
    have hnat : (5389373501 : ℕ)^43*20000000000000^35 ≤ 9358486109187^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389373501 10000000000 9358486109187 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4228795887/10000000000 : ℝ), (316138281/1250000000 : ℝ), (5389373501/10000000000 : ℝ)] ![(34736059168239/100000000000000 : ℝ), (18471510272461/100000000000000 : ℝ), (9358486109187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4228795887/10000000000 : ℝ)|^43 ≤ (34736059168239/100000000000000 : ℝ)^35
        have hw : |(-4228795887/10000000000 : ℝ)|=(4228795887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316138281/1250000000 : ℝ)|^43 ≤ (18471510272461/100000000000000 : ℝ)^35
        have hw : |(316138281/1250000000 : ℝ)|=(316138281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389373501/10000000000 : ℝ)|^43 ≤ (9358486109187/20000000000000 : ℝ)^35
        have hw : |(5389373501/10000000000 : ℝ)|=(5389373501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1575784071/10000000000 : ℝ)*x 0 + (-3275476443/10000000000 : ℝ)*x 1 + (1395968711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1575784071/10000000000 : ℝ)^43 ≤ (10329216533303/100000000000000 : ℝ)^35 := by
    have hnat : (1575784071 : ℕ)^43*100000000000000^35 ≤ 10329216533303^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575784071 10000000000 10329216533303 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3275476443/10000000000 : ℝ)^43 ≤ (12689662752891/50000000000000 : ℝ)^35 := by
    have hnat : (3275476443 : ℕ)^43*50000000000000^35 ≤ 12689662752891^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3275476443 10000000000 12689662752891 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395968711/2000000000 : ℝ)^43 ≤ (16072864488497/25000000000000 : ℝ)^35 := by
    have hnat : (1395968711 : ℕ)^43*25000000000000^35 ≤ 16072864488497^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395968711 2000000000 16072864488497 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1575784071/10000000000 : ℝ), (-3275476443/10000000000 : ℝ), (1395968711/2000000000 : ℝ)] ![(10329216533303/100000000000000 : ℝ), (12689662752891/50000000000000 : ℝ), (16072864488497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1575784071/10000000000 : ℝ)|^43 ≤ (10329216533303/100000000000000 : ℝ)^35
        have hw : |(1575784071/10000000000 : ℝ)|=(1575784071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3275476443/10000000000 : ℝ)|^43 ≤ (12689662752891/50000000000000 : ℝ)^35
        have hw : |(-3275476443/10000000000 : ℝ)|=(3275476443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1395968711/2000000000 : ℝ)|^43 ≤ (16072864488497/25000000000000 : ℝ)^35
        have hw : |(1395968711/2000000000 : ℝ)|=(1395968711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1417256941/2500000000 : ℝ)*x 0 + (5669029083/10000000000 : ℝ)*x 1 + (-3591743/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1417256941/2500000000 : ℝ)^43 ≤ (24896465362963/50000000000000 : ℝ)^35 := by
    have hnat : (1417256941 : ℕ)^43*50000000000000^35 ≤ 24896465362963^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417256941 2500000000 24896465362963 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5669029083/10000000000 : ℝ)^43 ≤ (3112059059949/6250000000000 : ℝ)^35 := by
    have hnat : (5669029083 : ℕ)^43*6250000000000^35 ≤ 3112059059949^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669029083 10000000000 3112059059949 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3591743/312500000 : ℝ)^43 ≤ (51765537409/12500000000000 : ℝ)^35 := by
    have hnat : (3591743 : ℕ)^43*12500000000000^35 ≤ 51765537409^35*312500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3591743 312500000 51765537409 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1417256941/2500000000 : ℝ), (5669029083/10000000000 : ℝ), (-3591743/312500000 : ℝ)] ![(24896465362963/50000000000000 : ℝ), (3112059059949/6250000000000 : ℝ), (51765537409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1417256941/2500000000 : ℝ)|^43 ≤ (24896465362963/50000000000000 : ℝ)^35
        have hw : |(1417256941/2500000000 : ℝ)|=(1417256941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5669029083/10000000000 : ℝ)|^43 ≤ (3112059059949/6250000000000 : ℝ)^35
        have hw : |(5669029083/10000000000 : ℝ)|=(5669029083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3591743/312500000 : ℝ)|^43 ≤ (51765537409/12500000000000 : ℝ)^35
        have hw : |(-3591743/312500000 : ℝ)|=(3591743/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3594736993/10000000000 : ℝ)*x 0 + (3594762411/10000000000 : ℝ)*x 1 + (100805609/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3594736993/10000000000 : ℝ)^43 ≤ (28451509966467/100000000000000 : ℝ)^35 := by
    have hnat : (3594736993 : ℕ)^43*100000000000000^35 ≤ 28451509966467^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594736993 10000000000 28451509966467 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3594762411/10000000000 : ℝ)^43 ≤ (2845175712769/10000000000000 : ℝ)^35 := by
    have hnat : (3594762411 : ℕ)^43*10000000000000^35 ≤ 2845175712769^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594762411 10000000000 2845175712769 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100805609/200000000 : ℝ)^43 ≤ (1346772903171/3125000000000 : ℝ)^35 := by
    have hnat : (100805609 : ℕ)^43*3125000000000^35 ≤ 1346772903171^35*200000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100805609 200000000 1346772903171 3125000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3594736993/10000000000 : ℝ), (3594762411/10000000000 : ℝ), (100805609/200000000 : ℝ)] ![(28451509966467/100000000000000 : ℝ), (2845175712769/10000000000000 : ℝ), (1346772903171/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3594736993/10000000000 : ℝ)|^43 ≤ (28451509966467/100000000000000 : ℝ)^35
        have hw : |(-3594736993/10000000000 : ℝ)|=(3594736993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3594762411/10000000000 : ℝ)|^43 ≤ (2845175712769/10000000000000 : ℝ)^35
        have hw : |(3594762411/10000000000 : ℝ)|=(3594762411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100805609/200000000 : ℝ)|^43 ≤ (1346772903171/3125000000000 : ℝ)^35
        have hw : |(100805609/200000000 : ℝ)|=(100805609/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (739147787/2500000000 : ℝ)*x 0 + (-2956612053/10000000000 : ℝ)*x 1 + (6169153081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (739147787/2500000000 : ℝ)^43 ≤ (11189206313917/50000000000000 : ℝ)^35 := by
    have hnat : (739147787 : ℕ)^43*50000000000000^35 ≤ 11189206313917^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739147787 2500000000 11189206313917 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2956612053/10000000000 : ℝ)^43 ≤ (22378607024557/100000000000000 : ℝ)^35 := by
    have hnat : (2956612053 : ℕ)^43*100000000000000^35 ≤ 22378607024557^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956612053 10000000000 22378607024557 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6169153081/10000000000 : ℝ)^43 ≤ (55242980332659/100000000000000 : ℝ)^35 := by
    have hnat : (6169153081 : ℕ)^43*100000000000000^35 ≤ 55242980332659^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6169153081 10000000000 55242980332659 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(739147787/2500000000 : ℝ), (-2956612053/10000000000 : ℝ), (6169153081/10000000000 : ℝ)] ![(11189206313917/50000000000000 : ℝ), (22378607024557/100000000000000 : ℝ), (55242980332659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(739147787/2500000000 : ℝ)|^43 ≤ (11189206313917/50000000000000 : ℝ)^35
        have hw : |(739147787/2500000000 : ℝ)|=(739147787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2956612053/10000000000 : ℝ)|^43 ≤ (22378607024557/100000000000000 : ℝ)^35
        have hw : |(-2956612053/10000000000 : ℝ)|=(2956612053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6169153081/10000000000 : ℝ)|^43 ≤ (55242980332659/100000000000000 : ℝ)^35
        have hw : |(6169153081/10000000000 : ℝ)|=(6169153081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5225112433/10000000000 : ℝ)*x 0 + (5225077423/10000000000 : ℝ)*x 1 + (-1523217773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225112433/10000000000 : ℝ)^43 ≤ (22523213936461/50000000000000 : ℝ)^35 := by
    have hnat : (5225112433 : ℕ)^43*50000000000000^35 ≤ 22523213936461^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225112433 10000000000 22523213936461 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225077423/10000000000 : ℝ)^43 ≤ (11261514264563/25000000000000 : ℝ)^35 := by
    have hnat : (5225077423 : ℕ)^43*25000000000000^35 ≤ 11261514264563^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225077423 10000000000 11261514264563 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523217773/10000000000 : ℝ)^43 ≤ (1981503011029/20000000000000 : ℝ)^35 := by
    have hnat : (1523217773 : ℕ)^43*20000000000000^35 ≤ 1981503011029^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523217773 10000000000 1981503011029 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225112433/10000000000 : ℝ), (5225077423/10000000000 : ℝ), (-1523217773/10000000000 : ℝ)] ![(22523213936461/50000000000000 : ℝ), (11261514264563/25000000000000 : ℝ), (1981503011029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225112433/10000000000 : ℝ)|^43 ≤ (22523213936461/50000000000000 : ℝ)^35
        have hw : |(5225112433/10000000000 : ℝ)|=(5225112433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225077423/10000000000 : ℝ)|^43 ≤ (11261514264563/25000000000000 : ℝ)^35
        have hw : |(5225077423/10000000000 : ℝ)|=(5225077423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1523217773/10000000000 : ℝ)|^43 ≤ (1981503011029/20000000000000 : ℝ)^35
        have hw : |(-1523217773/10000000000 : ℝ)|=(1523217773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324049_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (621745101/1250000000 : ℝ)*x 0 + (124348187/250000000 : ℝ)*x 1 + (1078910489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621745101/1250000000 : ℝ)^43 ≤ (42401105890667/100000000000000 : ℝ)^35 := by
    have hnat : (621745101 : ℕ)^43*100000000000000^35 ≤ 42401105890667^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621745101 1250000000 42401105890667 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124348187/250000000 : ℝ)^43 ≤ (42400756843469/100000000000000 : ℝ)^35 := by
    have hnat : (124348187 : ℕ)^43*100000000000000^35 ≤ 42400756843469^35*250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124348187 250000000 42400756843469 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078910489/5000000000 : ℝ)^43 ≤ (15198137243479/100000000000000 : ℝ)^35 := by
    have hnat : (1078910489 : ℕ)^43*100000000000000^35 ≤ 15198137243479^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078910489 5000000000 15198137243479 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(621745101/1250000000 : ℝ), (124348187/250000000 : ℝ), (1078910489/5000000000 : ℝ)] ![(42401105890667/100000000000000 : ℝ), (42400756843469/100000000000000 : ℝ), (15198137243479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(621745101/1250000000 : ℝ)|^43 ≤ (42401105890667/100000000000000 : ℝ)^35
        have hw : |(621745101/1250000000 : ℝ)|=(621745101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124348187/250000000 : ℝ)|^43 ≤ (42400756843469/100000000000000 : ℝ)^35
        have hw : |(124348187/250000000 : ℝ)|=(124348187/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078910489/5000000000 : ℝ)|^43 ≤ (15198137243479/100000000000000 : ℝ)^35
        have hw : |(1078910489/5000000000 : ℝ)|=(1078910489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324049 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3217107791/10000000000 : ℝ)*X 0 0+(402138481/1250000000 : ℝ)*X 0 1+(2860314501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2423391449/10000000000 : ℝ)*X 1 0+(-605847873/2500000000 : ℝ)*X 1 1+(7037537999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2783230017/10000000000 : ℝ)*X 0 0+(1776886667/10000000000 : ℝ)*X 0 1+(7240277341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((74932091/500000000 : ℝ)*X 1 0+(-969166471/10000000000 : ℝ)*X 1 1+(4363833779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3663388569/10000000000 : ℝ)*X 2 0+(3757993553/5000000000 : ℝ)*X 2 1+(-63545969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((3655519371/10000000000 : ℝ)*X 0 0+(7502286169/10000000000 : ℝ)*X 0 1+(44206989/2500000000 : ℝ)*X 0 2+(3655519371/10000000000 : ℝ)*X 1 0+(7502286169/10000000000 : ℝ)*X 1 1+(44206989/2500000000 : ℝ)*X 1 2+(3655519371/10000000000 : ℝ)*X 2 0+(7502286169/10000000000 : ℝ)*X 2 1+(44206989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-894498811/5000000000 : ℝ)*X 0 0+(17327477/62500000 : ℝ)*X 0 1+(7240188989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((239495091/2500000000 : ℝ)*X 1 0+(-377335981/2500000000 : ℝ)*X 1 1+(1090908403/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1879273723/2500000000 : ℝ)*X 2 0+(916217519/2500000000 : ℝ)*X 2 1+(-756559/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((7499485743/10000000000 : ℝ)*X 0 0+(1827377267/5000000000 : ℝ)*X 0 1+(184909927/10000000000 : ℝ)*X 0 2+(7499485743/10000000000 : ℝ)*X 1 0+(1827377267/5000000000 : ℝ)*X 1 1+(184909927/10000000000 : ℝ)*X 1 2+(7499485743/10000000000 : ℝ)*X 2 0+(1827377267/5000000000 : ℝ)*X 2 1+(184909927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-4228795887/10000000000 : ℝ)*X 0 0+(316138281/1250000000 : ℝ)*X 0 1+(5389373501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1575784071/10000000000 : ℝ)*X 1 0+(-3275476443/10000000000 : ℝ)*X 1 1+(1395968711/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1417256941/2500000000 : ℝ)*X 2 0+(5669029083/10000000000 : ℝ)*X 2 1+(-3591743/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((63651/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63651/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16788263049226053493587/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106224628267/1000000000000 : ℝ)*(base5) + (57176379783/62500000000 : ℝ)*(base7) + (4492984657/500000000000 : ℝ)*(base60) + (960545410729/500000000000 : ℝ)*(major_s0_0) + (960545410729/500000000000 : ℝ)*(major_s0_1) + (960545410729/500000000000 : ℝ)*(major_s0_2) + (2913137/500000000000 : ℝ)*(sp_s0_0) + (1592347/250000000000 : ℝ)*(sp_s0_1) + (1183396463651/500000000000 : ℝ)*(sp_s0_7) + (18490318679/7812500000 : ℝ)*(sp_s0_8) + (2473043189213/1000000000000 : ℝ)*(sp_s0_9) + (444363915617/250000000000 : ℝ)*(sp_s0_12) + (1980737/100000000000 : ℝ)*(sp_s0_13) + (25700323/500000000000 : ℝ)*(sp_s0_14) + (968858214207/1000000000000 : ℝ)*(f.failure) + (1183409280473/500000000000 : ℝ)*(f.sum) + (294023431/500000000000000000000 : ℝ)*base62 + (2112203188055701/5000000000000000000000000000 : ℝ)*base65 + (98951893055701/5000000000000000000000000000 : ℝ)*base67 + (237114907165477/500000000000000000000000000 : ℝ)*base68 + (1838755616710471/5000000000000000000000000000 : ℝ)*base71 + (49380137055701/5000000000000000000000000000 : ℝ)*base72 + (36601924715477/500000000000000000000000000 : ℝ)*base75 + (95845982465477/500000000000000000000000000 : ℝ)*base77 + (30745307/5000000000000000000000 : ℝ)*base78 + (5197/25000000000000000 : ℝ)*base87 + (5197/25000000000000000 : ℝ)*base89 + (5197/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12731/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12731/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47016269891676697983/9765625000000000000000000 : ℝ) := by norm_num
    linear_combination (25169438043/125000000000 : ℝ)*(base5) + (914254457863/1000000000000 : ℝ)*(base7) + (32434911929/200000000000 : ℝ)*(base60) + (7506893793/3906250000 : ℝ)*(major_s0_0) + (7506893793/3906250000 : ℝ)*(major_s0_1) + (7506893793/3906250000 : ℝ)*(major_s0_2) + (779379/250000000000 : ℝ)*(sp_s0_0) + (459519/200000000000 : ℝ)*(sp_s0_1) + (639203/1000000000000 : ℝ)*(sp_s0_7) + (14837173/500000000000 : ℝ)*(sp_s0_8) + (2368140011909/1000000000000 : ℝ)*(sp_s0_13) + (2368111796687/1000000000000 : ℝ)*(sp_s0_14) + (2569499272971/1000000000000 : ℝ)*(sp_s0_15) + (1682097078939/1000000000000 : ℝ)*(sp_s0_18) + (48459906271/50000000000 : ℝ)*(f.failure) + (592035942157/250000000000 : ℝ)*(f.sum) + (454083583/625000000000000000000 : ℝ)*base63 + (118340796152807/156250000000000000000000000 : ℝ)*base64 + (96831256059057/156250000000000000000000000 : ℝ)*base66 + (1246405324257/7812500000000000000000000 : ℝ)*base69 + (3251570402009/19531250000000000000000000 : ℝ)*base70 + (57630383868909/78125000000000000000000000 : ℝ)*base72 + (1389266387653/31250000000000000000000000 : ℝ)*base74 + (4828765089139/15625000000000000000000000 : ℝ)*base76 + (22958787/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (259/1250000000000000 : ℝ)*base86 + (259/1250000000000000 : ℝ)*base88 + (259/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5861/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5861/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (136766574674912145867/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (53271740009/62500000000 : ℝ)*(base5) + (23164916469/500000000000 : ℝ)*(base7) + (2830809/500000000000 : ℝ)*(base16) + (23127791903/1000000000000 : ℝ)*(base39) + (60103633741/1000000000000 : ℝ)*(base49) + (8537022837/10000000000 : ℝ)*(base59) + (24971949147/15625000000 : ℝ)*(major_s0_0) + (24971949147/15625000000 : ℝ)*(major_s0_1) + (24971949147/15625000000 : ℝ)*(major_s0_2) + (31450401/1000000000000 : ℝ)*(sp_s0_1) + (1101529/1000000000000 : ℝ)*(sp_s0_15) + (94589573649/40000000000 : ℝ)*(sp_s0_19) + (472940445841/200000000000 : ℝ)*(sp_s0_20) + (3217086079841/1000000000000 : ℝ)*(sp_s0_21) + (403009003603/500000000000 : ℝ)*(f.failure) + (94589573649/40000000000 : ℝ)*(f.sum) + (25218337/400000000000000000000 : ℝ)*base62 + (41726211591657/156250000000000000000000000 : ℝ)*base64 + (5227480727609/78125000000000000000000000 : ℝ)*base67 + (247595775661/15625000000000000000000000 : ℝ)*base68 + (12644630746959/19531250000000000000000000 : ℝ)*base70 + (99151443247907/156250000000000000000000000 : ℝ)*base73 + (10455544843089/15625000000000000000000000 : ℝ)*base74 + (18379735358053/31250000000000000000000000 : ℝ)*base76 + (74873209/156250000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base85 + (4313/12500000000000000 : ℝ)*base87 + (4313/12500000000000000 : ℝ)*base89 + (4313/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (63651/100000 : ℝ) ^ (21/4 : ℝ) ≤ (4666029364801190989/50000000000000000000 : ℝ) := by
    have hpowers : (63651/100000 : ℝ)^21 ≤ (4666029364801190989/50000000000000000000 : ℝ)^4 := by
      have hnat : (63651 : ℕ)^21*50000000000000000000^4 ≤ 4666029364801190989^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63651 100000 4666029364801190989 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63651/100000 : ℝ)) (X := (4666029364801190989/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (54666029364801190989/50000000000000000000 : ℝ) ≤ (10171394085043481/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (54666029364801190989/50000000000000000000 : ℝ)^4 ≤ (10171394085043481/10000000000000000 : ℝ)^21 := by
      have hnat : (54666029364801190989 : ℕ)^4*10000000000000000^21 ≤ 10171394085043481^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54666029364801190989 50000000000000000000 10171394085043481 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10171394085043481/10000000000000000 : ℝ)) (X := (54666029364801190989/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (29666029364801190989/25000000000000000000 : ℝ) ≤ (2066265262172183/2000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (29666029364801190989/25000000000000000000 : ℝ)^4 ≤ (2066265262172183/2000000000000000 : ℝ)^21 := by
      have hnat : (29666029364801190989 : ℕ)^4*2000000000000000^21 ≤ 2066265262172183^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29666029364801190989 25000000000000000000 2066265262172183 2000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2066265262172183/2000000000000000 : ℝ)) (X := (29666029364801190989/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(171394085043481/6365100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1631961487933/64950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (63651/100000 : ℝ)) (alpha := (171394085043481/6365100000000000 : ℝ)) (beta := (1631961487933/64950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (63651/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(171394085043481/6365100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1631961487933/64950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (12731/20000 : ℝ) ^ (21/4 : ℝ) ≤ (1867027602405084419/20000000000000000000 : ℝ) := by
    have hpowers : (12731/20000 : ℝ)^21 ≤ (1867027602405084419/20000000000000000000 : ℝ)^4 := by
      have hnat : (12731 : ℕ)^21*20000000000000000000^4 ≤ 1867027602405084419^4*20000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12731 20000 1867027602405084419 20000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12731/20000 : ℝ)) (X := (1867027602405084419/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (21867027602405084419/20000000000000000000 : ℝ) ≤ (10171448650554129/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (21867027602405084419/20000000000000000000 : ℝ)^4 ≤ (10171448650554129/10000000000000000 : ℝ)^21 := by
      have hnat : (21867027602405084419 : ℕ)^4*10000000000000000^21 ≤ 10171448650554129^21*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21867027602405084419 20000000000000000000 10171448650554129 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10171448650554129/10000000000000000 : ℝ)) (X := (21867027602405084419/20000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11867027602405084419/10000000000000000000 : ℝ) ≤ (413257137582001/400000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (11867027602405084419/10000000000000000000 : ℝ)^4 ≤ (413257137582001/400000000000000 : ℝ)^21 := by
      have hnat : (11867027602405084419 : ℕ)^4*400000000000000^21 ≤ 413257137582001^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11867027602405084419 10000000000000000000 413257137582001 400000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (413257137582001/400000000000000 : ℝ)) (X := (11867027602405084419/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5912022432901/219500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(19997473624487/795687500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (12731/20000 : ℝ)) (alpha := (5912022432901/219500000000000 : ℝ)) (beta := (19997473624487/795687500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12731/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5912022432901/219500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(19997473624487/795687500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5861/50000 : ℝ) ^ (21/4 : ℝ) ≤ (647483966910987/50000000000000000000 : ℝ) := by
    have hpowers : (5861/50000 : ℝ)^21 ≤ (647483966910987/50000000000000000000 : ℝ)^4 := by
      have hnat : (5861 : ℕ)^21*50000000000000000000^4 ≤ 647483966910987^4*50000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5861 50000 647483966910987 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5861/50000 : ℝ)) (X := (647483966910987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50000647483966910987/50000000000000000000 : ℝ) ≤ (2500006166481649/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50000647483966910987/50000000000000000000 : ℝ)^4 ≤ (2500006166481649/2500000000000000 : ℝ)^21 := by
      have hnat : (50000647483966910987 : ℕ)^4*2500000000000000^21 ≤ 2500006166481649^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000647483966910987 50000000000000000000 2500006166481649 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500006166481649/2500000000000000 : ℝ)) (X := (50000647483966910987/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25000647483966910987/25000000000000000000 : ℝ) ≤ (10000049331594621/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (25000647483966910987/25000000000000000000 : ℝ)^4 ≤ (10000049331594621/10000000000000000 : ℝ)^21 := by
      have hnat : (25000647483966910987 : ℕ)^4*10000000000000000^21 ≤ 10000049331594621^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000647483966910987 25000000000000000000 10000049331594621 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000049331594621/10000000000000000 : ℝ)) (X := (25000647483966910987/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6166481649/293050000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(986626721/46888000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (5861/50000 : ℝ)) (alpha := (6166481649/293050000000000 : ℝ)) (beta := (986626721/46888000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5861/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6166481649/293050000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(986626721/46888000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3594736993/10000000000 : ℝ)*X 0 0+(3594762411/10000000000 : ℝ)*X 0 1+(100805609/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((739147787/2500000000 : ℝ)*X 1 0+(-2956612053/10000000000 : ℝ)*X 1 1+(6169153081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5225112433/10000000000 : ℝ)*X 2 0+(5225077423/10000000000 : ℝ)*X 2 1+(-1523217773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((621745101/1250000000 : ℝ)*X 0 0+(124348187/250000000 : ℝ)*X 0 1+(1078910489/5000000000 : ℝ)*X 0 2+(621745101/1250000000 : ℝ)*X 1 0+(124348187/250000000 : ℝ)*X 1 1+(1078910489/5000000000 : ℝ)*X 1 2+(621745101/1250000000 : ℝ)*X 2 0+(124348187/250000000 : ℝ)*X 2 1+(1078910489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324049_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-19686838839622434754582829043727/2228199814000000000000000000000 : ℝ) := by norm_num
    linear_combination (389/100000000000 : ℝ)*(base8) + (477/50000000000 : ℝ)*(base19) + (47/31250000000 : ℝ)*(base23) + (743/500000000000 : ℝ)*(base40) + (339/200000000000 : ℝ)*(base43) + (116404825847/500000000000 : ℝ)*(base49) + (1041366138183/1000000000000 : ℝ)*(base59) + (122931086501/200000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s1_0) + (396567999661/200000000000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (2945103737789/1000000000000 : ℝ)*(sp_s1_0) + (1472551866917/500000000000 : ℝ)*(sp_s1_1) + (1472551870087/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2945103743373/1000000000000 : ℝ)*(f.sum) + (236253957052323851/257297900000000000000000000000 : ℝ)*base63 + (47019100224219/58610000000000000000000000 : ℝ)*base64 + (3863733159541/10975000000000000000000000 : ℝ)*base66 + (1651044638381/7326250000000000000000000 : ℝ)*base69 + (597296657024184889/1865292555000000000000000000000 : ℝ)*base70 + (5145993138823/6495000000000000000000000 : ℝ)*base72 + (4024326375181/43900000000000000000000000 : ℝ)*base75 + (12379019020549/318255000000000000000000000 : ℝ)*base77 + (4540151243641079/14256525000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b025 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 49 ≤ c.val) (hhi : c.val < 50)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=49 := by omega
  rcases hc with rfl
  · exact collision_c324049 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 49 ≤ c.val) (hhi : c.val < 50)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
