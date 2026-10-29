-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:15:40.149611+00:00
-- url     : https://prove2.me/submissions/052531f5-9f9a-471a-ab94-8abf10aca6c2

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
theorem collision_support_c327059_s0_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-290973089/1000000000 : ℝ)*x 0 + (5819461/20000000 : ℝ)*x 1 + (3067600861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290973089/1000000000 : ℝ)^91 ≤ (2236015246481/10000000000000 : ℝ)^75 := by
    have hnat : (290973089 : ℕ)^91*10000000000000^75 ≤ 2236015246481^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290973089 1000000000 2236015246481 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5819461/20000000 : ℝ)^91 ≤ (5590037207113/25000000000000 : ℝ)^75 := by
    have hnat : (5819461 : ℕ)^91*25000000000000^75 ≤ 5590037207113^75*20000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5819461 20000000 5590037207113 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3067600861/5000000000 : ℝ)^91 ≤ (55279698701449/100000000000000 : ℝ)^75 := by
    have hnat : (3067600861 : ℕ)^91*100000000000000^75 ≤ 55279698701449^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3067600861 5000000000 55279698701449 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290973089/1000000000 : ℝ), (5819461/20000000 : ℝ), (3067600861/5000000000 : ℝ)] ![(2236015246481/10000000000000 : ℝ), (5590037207113/25000000000000 : ℝ), (55279698701449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290973089/1000000000 : ℝ)|^91 ≤ (2236015246481/10000000000000 : ℝ)^75
        have hw : |(-290973089/1000000000 : ℝ)|=(290973089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5819461/20000000 : ℝ)|^91 ≤ (5590037207113/25000000000000 : ℝ)^75
        have hw : |(5819461/20000000 : ℝ)|=(5819461/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3067600861/5000000000 : ℝ)|^91 ≤ (55279698701449/100000000000000 : ℝ)^75
        have hw : |(3067600861/5000000000 : ℝ)|=(3067600861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2909730909/10000000000 : ℝ)*x 0 + (-2909730397/10000000000 : ℝ)*x 1 + (6135201793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2909730909/10000000000 : ℝ)^91 ≤ (11180076320983/50000000000000 : ℝ)^75 := by
    have hnat : (2909730909 : ℕ)^91*50000000000000^75 ≤ 11180076320983^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909730909 10000000000 11180076320983 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2909730397/10000000000 : ℝ)^91 ≤ (279501848351/1250000000000 : ℝ)^75 := by
    have hnat : (2909730397 : ℕ)^91*1250000000000^75 ≤ 279501848351^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909730397 10000000000 279501848351 1250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6135201793/10000000000 : ℝ)^91 ≤ (13819924869413/25000000000000 : ℝ)^75 := by
    have hnat : (6135201793 : ℕ)^91*25000000000000^75 ≤ 13819924869413^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6135201793 10000000000 13819924869413 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2909730909/10000000000 : ℝ), (-2909730397/10000000000 : ℝ), (6135201793/10000000000 : ℝ)] ![(11180076320983/50000000000000 : ℝ), (279501848351/1250000000000 : ℝ), (13819924869413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2909730909/10000000000 : ℝ)|^91 ≤ (11180076320983/50000000000000 : ℝ)^75
        have hw : |(2909730909/10000000000 : ℝ)|=(2909730909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2909730397/10000000000 : ℝ)|^91 ≤ (279501848351/1250000000000 : ℝ)^75
        have hw : |(-2909730397/10000000000 : ℝ)|=(2909730397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6135201793/10000000000 : ℝ)|^91 ≤ (13819924869413/25000000000000 : ℝ)^75
        have hw : |(6135201793/10000000000 : ℝ)|=(6135201793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1444395597/5000000000 : ℝ)*x 0 + (6330105159/10000000000 : ℝ)*x 1 + (1349856079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1444395597/5000000000 : ℝ)^91 ≤ (5541265246083/25000000000000 : ℝ)^75 := by
    have hnat : (1444395597 : ℕ)^91*25000000000000^75 ≤ 5541265246083^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444395597 5000000000 5541265246083 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6330105159/10000000000 : ℝ)^91 ≤ (28708814541407/50000000000000 : ℝ)^75 := by
    have hnat : (6330105159 : ℕ)^91*50000000000000^75 ≤ 28708814541407^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6330105159 10000000000 28708814541407 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349856079/5000000000 : ℝ)^91 ≤ (2552163739353/12500000000000 : ℝ)^75 := by
    have hnat : (1349856079 : ℕ)^91*12500000000000^75 ≤ 2552163739353^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349856079 5000000000 2552163739353 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1444395597/5000000000 : ℝ), (6330105159/10000000000 : ℝ), (1349856079/5000000000 : ℝ)] ![(5541265246083/25000000000000 : ℝ), (28708814541407/50000000000000 : ℝ), (2552163739353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1444395597/5000000000 : ℝ)|^91 ≤ (5541265246083/25000000000000 : ℝ)^75
        have hw : |(1444395597/5000000000 : ℝ)|=(1444395597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6330105159/10000000000 : ℝ)|^91 ≤ (28708814541407/50000000000000 : ℝ)^75
        have hw : |(6330105159/10000000000 : ℝ)|=(6330105159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349856079/5000000000 : ℝ)|^91 ≤ (2552163739353/12500000000000 : ℝ)^75
        have hw : |(1349856079/5000000000 : ℝ)|=(1349856079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-143061571/625000000 : ℝ)*x 0 + (582937267/10000000000 : ℝ)*x 1 + (2082359433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (143061571/625000000 : ℝ)^91 ≤ (8356097093989/50000000000000 : ℝ)^75 := by
    have hnat : (143061571 : ℕ)^91*50000000000000^75 ≤ 8356097093989^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143061571 625000000 8356097093989 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582937267/10000000000 : ℝ)^91 ≤ (127159203883/4000000000000 : ℝ)^75 := by
    have hnat : (582937267 : ℕ)^91*4000000000000^75 ≤ 127159203883^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582937267 10000000000 127159203883 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082359433/2500000000 : ℝ)^91 ≤ (80108825703937/100000000000000 : ℝ)^75 := by
    have hnat : (2082359433 : ℕ)^91*100000000000000^75 ≤ 80108825703937^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082359433 2500000000 80108825703937 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-143061571/625000000 : ℝ), (582937267/10000000000 : ℝ), (2082359433/2500000000 : ℝ)] ![(8356097093989/50000000000000 : ℝ), (127159203883/4000000000000 : ℝ), (80108825703937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-143061571/625000000 : ℝ)|^91 ≤ (8356097093989/50000000000000 : ℝ)^75
        have hw : |(-143061571/625000000 : ℝ)|=(143061571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582937267/10000000000 : ℝ)|^91 ≤ (127159203883/4000000000000 : ℝ)^75
        have hw : |(582937267/10000000000 : ℝ)|=(582937267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2082359433/2500000000 : ℝ)|^91 ≤ (80108825703937/100000000000000 : ℝ)^75
        have hw : |(2082359433/2500000000 : ℝ)|=(2082359433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (859862117/5000000000 : ℝ)*x 0 + (-1257298071/10000000000 : ℝ)*x 1 + (8329437647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859862117/5000000000 : ℝ)^91 ≤ (2953226111817/25000000000000 : ℝ)^75 := by
    have hnat : (859862117 : ℕ)^91*25000000000000^75 ≤ 2953226111817^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859862117 5000000000 2953226111817 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257298071/10000000000 : ℝ)^91 ≤ (8078270829211/100000000000000 : ℝ)^75 := by
    have hnat : (1257298071 : ℕ)^91*100000000000000^75 ≤ 8078270829211^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257298071 10000000000 8078270829211 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8329437647/10000000000 : ℝ)^91 ≤ (80108824712047/100000000000000 : ℝ)^75 := by
    have hnat : (8329437647 : ℕ)^91*100000000000000^75 ≤ 80108824712047^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8329437647 10000000000 80108824712047 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859862117/5000000000 : ℝ), (-1257298071/10000000000 : ℝ), (8329437647/10000000000 : ℝ)] ![(2953226111817/25000000000000 : ℝ), (8078270829211/100000000000000 : ℝ), (80108824712047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859862117/5000000000 : ℝ)|^91 ≤ (2953226111817/25000000000000 : ℝ)^75
        have hw : |(859862117/5000000000 : ℝ)|=(859862117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1257298071/10000000000 : ℝ)|^91 ≤ (8078270829211/100000000000000 : ℝ)^75
        have hw : |(-1257298071/10000000000 : ℝ)|=(1257298071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8329437647/10000000000 : ℝ)|^91 ≤ (80108824712047/100000000000000 : ℝ)^75
        have hw : |(8329437647/10000000000 : ℝ)|=(8329437647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2069159949/5000000000 : ℝ)*x 0 + (7074727871/10000000000 : ℝ)*x 1 + (-647061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069159949/5000000000 : ℝ)^91 ≤ (17141541041287/50000000000000 : ℝ)^75 := by
    have hnat : (2069159949 : ℕ)^91*50000000000000^75 ≤ 17141541041287^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069159949 5000000000 17141541041287 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7074727871/10000000000 : ℝ)^91 ≤ (2628498953663/4000000000000 : ℝ)^75 := by
    have hnat : (7074727871 : ℕ)^91*4000000000000^75 ≤ 2628498953663^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7074727871 10000000000 2628498953663 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647061/2500000000 : ℝ)^91 ≤ (277753589/6250000000000 : ℝ)^75 := by
    have hnat : (647061 : ℕ)^91*6250000000000^75 ≤ 277753589^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647061 2500000000 277753589 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069159949/5000000000 : ℝ), (7074727871/10000000000 : ℝ), (-647061/2500000000 : ℝ)] ![(17141541041287/50000000000000 : ℝ), (2628498953663/4000000000000 : ℝ), (277753589/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069159949/5000000000 : ℝ)|^91 ≤ (17141541041287/50000000000000 : ℝ)^75
        have hw : |(2069159949/5000000000 : ℝ)|=(2069159949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7074727871/10000000000 : ℝ)|^91 ≤ (2628498953663/4000000000000 : ℝ)^75
        have hw : |(7074727871/10000000000 : ℝ)|=(7074727871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-647061/2500000000 : ℝ)|^91 ≤ (277753589/6250000000000 : ℝ)^75
        have hw : |(-647061/2500000000 : ℝ)|=(647061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (992124149/5000000000 : ℝ)*x 0 + (8070590729/10000000000 : ℝ)*x 1 + (169424553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992124149/5000000000 : ℝ)^91 ≤ (1405237831653/10000000000000 : ℝ)^75 := by
    have hnat : (992124149 : ℕ)^91*10000000000000^75 ≤ 1405237831653^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992124149 5000000000 1405237831653 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8070590729/10000000000 : ℝ)^91 ≤ (38549178813661/50000000000000 : ℝ)^75 := by
    have hnat : (8070590729 : ℕ)^91*50000000000000^75 ≤ 38549178813661^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8070590729 10000000000 38549178813661 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169424553/1250000000 : ℝ)^91 ≤ (8849264043341/100000000000000 : ℝ)^75 := by
    have hnat : (169424553 : ℕ)^91*100000000000000^75 ≤ 8849264043341^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169424553 1250000000 8849264043341 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(992124149/5000000000 : ℝ), (8070590729/10000000000 : ℝ), (169424553/1250000000 : ℝ)] ![(1405237831653/10000000000000 : ℝ), (38549178813661/50000000000000 : ℝ), (8849264043341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(992124149/5000000000 : ℝ)|^91 ≤ (1405237831653/10000000000000 : ℝ)^75
        have hw : |(992124149/5000000000 : ℝ)|=(992124149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8070590729/10000000000 : ℝ)|^91 ≤ (38549178813661/50000000000000 : ℝ)^75
        have hw : |(8070590729/10000000000 : ℝ)|=(8070590729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169424553/1250000000 : ℝ)|^91 ≤ (8849264043341/100000000000000 : ℝ)^75
        have hw : |(169424553/1250000000 : ℝ)|=(169424553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-94286291/1000000000 : ℝ)*x 0 + (1967375187/10000000000 : ℝ)*x 1 + (8353974323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94286291/1000000000 : ℝ)^91 ≤ (712154554391/12500000000000 : ℝ)^75 := by
    have hnat : (94286291 : ℕ)^91*12500000000000^75 ≤ 712154554391^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94286291 1000000000 712154554391 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1967375187/10000000000 : ℝ)^91 ≤ (6953761552567/50000000000000 : ℝ)^75 := by
    have hnat : (1967375187 : ℕ)^91*50000000000000^75 ≤ 6953761552567^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967375187 10000000000 6953761552567 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8353974323/10000000000 : ℝ)^91 ≤ (10049405055733/12500000000000 : ℝ)^75 := by
    have hnat : (8353974323 : ℕ)^91*12500000000000^75 ≤ 10049405055733^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8353974323 10000000000 10049405055733 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94286291/1000000000 : ℝ), (1967375187/10000000000 : ℝ), (8353974323/10000000000 : ℝ)] ![(712154554391/12500000000000 : ℝ), (6953761552567/50000000000000 : ℝ), (10049405055733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94286291/1000000000 : ℝ)|^91 ≤ (712154554391/12500000000000 : ℝ)^75
        have hw : |(-94286291/1000000000 : ℝ)|=(94286291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1967375187/10000000000 : ℝ)|^91 ≤ (6953761552567/50000000000000 : ℝ)^75
        have hw : |(1967375187/10000000000 : ℝ)|=(1967375187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8353974323/10000000000 : ℝ)|^91 ≤ (10049405055733/12500000000000 : ℝ)^75
        have hw : |(8353974323/10000000000 : ℝ)|=(8353974323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (171526319/2000000000 : ℝ)*x 0 + (-50980801/250000000 : ℝ)*x 1 + (1670794837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171526319/2000000000 : ℝ)^91 ≤ (1269633224223/25000000000000 : ℝ)^75 := by
    have hnat : (171526319 : ℕ)^91*25000000000000^75 ≤ 1269633224223^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171526319 2000000000 1269633224223 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50980801/250000000 : ℝ)^91 ≤ (7263114124307/50000000000000 : ℝ)^75 := by
    have hnat : (50980801 : ℕ)^91*50000000000000^75 ≤ 7263114124307^75*250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50980801 250000000 7263114124307 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1670794837/2000000000 : ℝ)^91 ≤ (80395238834489/100000000000000 : ℝ)^75 := by
    have hnat : (1670794837 : ℕ)^91*100000000000000^75 ≤ 80395238834489^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670794837 2000000000 80395238834489 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171526319/2000000000 : ℝ), (-50980801/250000000 : ℝ), (1670794837/2000000000 : ℝ)] ![(1269633224223/25000000000000 : ℝ), (7263114124307/50000000000000 : ℝ), (80395238834489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171526319/2000000000 : ℝ)|^91 ≤ (1269633224223/25000000000000 : ℝ)^75
        have hw : |(171526319/2000000000 : ℝ)|=(171526319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50980801/250000000 : ℝ)|^91 ≤ (7263114124307/50000000000000 : ℝ)^75
        have hw : |(-50980801/250000000 : ℝ)|=(50980801/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1670794837/2000000000 : ℝ)|^91 ≤ (80395238834489/100000000000000 : ℝ)^75
        have hw : |(1670794837/2000000000 : ℝ)|=(1670794837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4173208823/5000000000 : ℝ)*x 0 + (2620425401/10000000000 : ℝ)*x 1 + (-356221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173208823/5000000000 : ℝ)^91 ≤ (80307012478257/100000000000000 : ℝ)^75 := by
    have hnat : (4173208823 : ℕ)^91*100000000000000^75 ≤ 80307012478257^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173208823 5000000000 80307012478257 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620425401/10000000000 : ℝ)^91 ≤ (9846029267693/50000000000000 : ℝ)^75 := by
    have hnat : (2620425401 : ℕ)^91*50000000000000^75 ≤ 9846029267693^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620425401 10000000000 9846029267693 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356221/5000000000 : ℝ)^91 ≤ (29030383/3125000000000 : ℝ)^75 := by
    have hnat : (356221 : ℕ)^91*3125000000000^75 ≤ 29030383^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356221 5000000000 29030383 3125000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173208823/5000000000 : ℝ), (2620425401/10000000000 : ℝ), (-356221/5000000000 : ℝ)] ![(80307012478257/100000000000000 : ℝ), (9846029267693/50000000000000 : ℝ), (29030383/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173208823/5000000000 : ℝ)|^91 ≤ (80307012478257/100000000000000 : ℝ)^75
        have hw : |(4173208823/5000000000 : ℝ)|=(4173208823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620425401/10000000000 : ℝ)|^91 ≤ (9846029267693/50000000000000 : ℝ)^75
        have hw : |(2620425401/10000000000 : ℝ)|=(2620425401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356221/5000000000 : ℝ)|^91 ≤ (29030383/3125000000000 : ℝ)^75
        have hw : |(-356221/5000000000 : ℝ)|=(356221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3336600987/5000000000 : ℝ)*x 0 + (171925581/500000000 : ℝ)*x 1 + (1670389747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3336600987/5000000000 : ℝ)^91 ≤ (3060757470111/5000000000000 : ℝ)^75 := by
    have hnat : (3336600987 : ℕ)^91*5000000000000^75 ≤ 3060757470111^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3336600987 5000000000 3060757470111 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171925581/500000000 : ℝ)^91 ≤ (2738185516007/10000000000000 : ℝ)^75 := by
    have hnat : (171925581 : ℕ)^91*10000000000000^75 ≤ 2738185516007^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171925581 500000000 2738185516007 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1670389747/10000000000 : ℝ)^91 ≤ (11402995412033/100000000000000 : ℝ)^75 := by
    have hnat : (1670389747 : ℕ)^91*100000000000000^75 ≤ 11402995412033^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670389747 10000000000 11402995412033 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3336600987/5000000000 : ℝ), (171925581/500000000 : ℝ), (1670389747/10000000000 : ℝ)] ![(3060757470111/5000000000000 : ℝ), (2738185516007/10000000000000 : ℝ), (11402995412033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3336600987/5000000000 : ℝ)|^91 ≤ (3060757470111/5000000000000 : ℝ)^75
        have hw : |(3336600987/5000000000 : ℝ)|=(3336600987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171925581/500000000 : ℝ)|^91 ≤ (2738185516007/10000000000000 : ℝ)^75
        have hw : |(171925581/500000000 : ℝ)|=(171925581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1670389747/10000000000 : ℝ)|^91 ≤ (11402995412033/100000000000000 : ℝ)^75
        have hw : |(1670389747/10000000000 : ℝ)|=(1670389747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-203753179/400000000 : ℝ)*x 0 + (2148272837/10000000000 : ℝ)*x 1 + (2369691843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203753179/400000000 : ℝ)^91 ≤ (22055515463357/50000000000000 : ℝ)^75 := by
    have hnat : (203753179 : ℕ)^91*50000000000000^75 ≤ 22055515463357^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203753179 400000000 22055515463357 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148272837/10000000000 : ℝ)^91 ≤ (15473973561123/100000000000000 : ℝ)^75 := by
    have hnat : (2148272837 : ℕ)^91*100000000000000^75 ≤ 15473973561123^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148272837 10000000000 15473973561123 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2369691843/5000000000 : ℝ)^91 ≤ (10103748873653/25000000000000 : ℝ)^75 := by
    have hnat : (2369691843 : ℕ)^91*25000000000000^75 ≤ 10103748873653^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369691843 5000000000 10103748873653 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203753179/400000000 : ℝ), (2148272837/10000000000 : ℝ), (2369691843/5000000000 : ℝ)] ![(22055515463357/50000000000000 : ℝ), (15473973561123/100000000000000 : ℝ), (10103748873653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203753179/400000000 : ℝ)|^91 ≤ (22055515463357/50000000000000 : ℝ)^75
        have hw : |(-203753179/400000000 : ℝ)|=(203753179/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2148272837/10000000000 : ℝ)|^91 ≤ (15473973561123/100000000000000 : ℝ)^75
        have hw : |(2148272837/10000000000 : ℝ)|=(2148272837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2369691843/5000000000 : ℝ)|^91 ≤ (10103748873653/25000000000000 : ℝ)^75
        have hw : |(2369691843/5000000000 : ℝ)|=(2369691843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1795672683/10000000000 : ℝ)*x 0 + (-1322449131/5000000000 : ℝ)*x 1 + (3622474513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795672683/10000000000 : ℝ)^91 ≤ (12448842530607/100000000000000 : ℝ)^75 := by
    have hnat : (1795672683 : ℕ)^91*100000000000000^75 ≤ 12448842530607^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795672683 10000000000 12448842530607 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1322449131/5000000000 : ℝ)^91 ≤ (99577118801/500000000000 : ℝ)^75 := by
    have hnat : (1322449131 : ℕ)^91*500000000000^75 ≤ 99577118801^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322449131 5000000000 99577118801 500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3622474513/5000000000 : ℝ)^91 ≤ (67635733695817/100000000000000 : ℝ)^75 := by
    have hnat : (3622474513 : ℕ)^91*100000000000000^75 ≤ 67635733695817^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3622474513 5000000000 67635733695817 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1795672683/10000000000 : ℝ), (-1322449131/5000000000 : ℝ), (3622474513/5000000000 : ℝ)] ![(12448842530607/100000000000000 : ℝ), (99577118801/500000000000 : ℝ), (67635733695817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1795672683/10000000000 : ℝ)|^91 ≤ (12448842530607/100000000000000 : ℝ)^75
        have hw : |(1795672683/10000000000 : ℝ)|=(1795672683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1322449131/5000000000 : ℝ)|^91 ≤ (99577118801/500000000000 : ℝ)^75
        have hw : |(-1322449131/5000000000 : ℝ)|=(1322449131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3622474513/5000000000 : ℝ)|^91 ≤ (67635733695817/100000000000000 : ℝ)^75
        have hw : |(3622474513/5000000000 : ℝ)|=(3622474513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8434409489/10000000000 : ℝ)*x 0 + (2507188217/10000000000 : ℝ)*x 1 + (-208911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8434409489/10000000000 : ℝ)^91 ≤ (40667706941157/50000000000000 : ℝ)^75 := by
    have hnat : (8434409489 : ℕ)^91*50000000000000^75 ≤ 40667706941157^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8434409489 10000000000 40667706941157 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507188217/10000000000 : ℝ)^91 ≤ (2333047053681/12500000000000 : ℝ)^75 := by
    have hnat : (2507188217 : ℕ)^91*12500000000000^75 ≤ 2333047053681^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507188217 10000000000 2333047053681 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208911/10000000000 : ℝ)^91 ≤ (209678091/100000000000000 : ℝ)^75 := by
    have hnat : (208911 : ℕ)^91*100000000000000^75 ≤ 209678091^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208911 10000000000 209678091 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8434409489/10000000000 : ℝ), (2507188217/10000000000 : ℝ), (-208911/10000000000 : ℝ)] ![(40667706941157/50000000000000 : ℝ), (2333047053681/12500000000000 : ℝ), (209678091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8434409489/10000000000 : ℝ)|^91 ≤ (40667706941157/50000000000000 : ℝ)^75
        have hw : |(8434409489/10000000000 : ℝ)|=(8434409489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507188217/10000000000 : ℝ)|^91 ≤ (2333047053681/12500000000000 : ℝ)^75
        have hw : |(2507188217/10000000000 : ℝ)|=(2507188217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208911/10000000000 : ℝ)|^91 ≤ (209678091/100000000000000 : ℝ)^75
        have hw : |(-208911/10000000000 : ℝ)|=(208911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s0_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (89927643/1000000000 : ℝ)*x 0 + (4381379527/5000000000 : ℝ)*x 1 + (1428000621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89927643/1000000000 : ℝ)^91 ≤ (5379275191159/100000000000000 : ℝ)^75 := by
    have hnat : (89927643 : ℕ)^91*100000000000000^75 ≤ 5379275191159^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89927643 1000000000 5379275191159 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4381379527/5000000000 : ℝ)^91 ≤ (21298266873141/25000000000000 : ℝ)^75 := by
    have hnat : (4381379527 : ℕ)^91*25000000000000^75 ≤ 21298266873141^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381379527 5000000000 21298266873141 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1428000621/10000000000 : ℝ)^91 ≤ (377106292169/4000000000000 : ℝ)^75 := by
    have hnat : (1428000621 : ℕ)^91*4000000000000^75 ≤ 377106292169^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428000621 10000000000 377106292169 4000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89927643/1000000000 : ℝ), (4381379527/5000000000 : ℝ), (1428000621/10000000000 : ℝ)] ![(5379275191159/100000000000000 : ℝ), (21298266873141/25000000000000 : ℝ), (377106292169/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89927643/1000000000 : ℝ)|^91 ≤ (5379275191159/100000000000000 : ℝ)^75
        have hw : |(89927643/1000000000 : ℝ)|=(89927643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4381379527/5000000000 : ℝ)|^91 ≤ (21298266873141/25000000000000 : ℝ)^75
        have hw : |(4381379527/5000000000 : ℝ)|=(4381379527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1428000621/10000000000 : ℝ)|^91 ≤ (377106292169/4000000000000 : ℝ)^75
        have hw : |(1428000621/10000000000 : ℝ)|=(1428000621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-643816101/2000000000 : ℝ)*x 0 + (3217768301/10000000000 : ℝ)*x 1 + (1119540887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643816101/2000000000 : ℝ)^91 ≤ (5055273139079/20000000000000 : ℝ)^75 := by
    have hnat : (643816101 : ℕ)^91*20000000000000^75 ≤ 5055273139079^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643816101 2000000000 5055273139079 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3217768301/10000000000 : ℝ)^91 ≤ (25263864677053/100000000000000 : ℝ)^75 := by
    have hnat : (3217768301 : ℕ)^91*100000000000000^75 ≤ 25263864677053^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3217768301 10000000000 25263864677053 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119540887/2000000000 : ℝ)^91 ≤ (49459769612627/100000000000000 : ℝ)^75 := by
    have hnat : (1119540887 : ℕ)^91*100000000000000^75 ≤ 49459769612627^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119540887 2000000000 49459769612627 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-643816101/2000000000 : ℝ), (3217768301/10000000000 : ℝ), (1119540887/2000000000 : ℝ)] ![(5055273139079/20000000000000 : ℝ), (25263864677053/100000000000000 : ℝ), (49459769612627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-643816101/2000000000 : ℝ)|^91 ≤ (5055273139079/20000000000000 : ℝ)^75
        have hw : |(-643816101/2000000000 : ℝ)|=(643816101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3217768301/10000000000 : ℝ)|^91 ≤ (25263864677053/100000000000000 : ℝ)^75
        have hw : |(3217768301/10000000000 : ℝ)|=(3217768301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119540887/2000000000 : ℝ)|^91 ≤ (49459769612627/100000000000000 : ℝ)^75
        have hw : |(1119540887/2000000000 : ℝ)|=(1119540887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1608899473/5000000000 : ℝ)*x 0 + (-201029713/625000000 : ℝ)*x 1 + (5599991977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1608899473/5000000000 : ℝ)^91 ≤ (25264156611413/100000000000000 : ℝ)^75 := by
    have hnat : (1608899473 : ℕ)^91*100000000000000^75 ≤ 25264156611413^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608899473 5000000000 25264156611413 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201029713/625000000 : ℝ)^91 ≤ (12625774346543/50000000000000 : ℝ)^75 := by
    have hnat : (201029713 : ℕ)^91*50000000000000^75 ≤ 12625774346543^75*625000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201029713 625000000 12625774346543 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5599991977/10000000000 : ℝ)^91 ≤ (989685893657/2000000000000 : ℝ)^75 := by
    have hnat : (5599991977 : ℕ)^91*2000000000000^75 ≤ 989685893657^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5599991977 10000000000 989685893657 2000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1608899473/5000000000 : ℝ), (-201029713/625000000 : ℝ), (5599991977/10000000000 : ℝ)] ![(25264156611413/100000000000000 : ℝ), (12625774346543/50000000000000 : ℝ), (989685893657/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1608899473/5000000000 : ℝ)|^91 ≤ (25264156611413/100000000000000 : ℝ)^75
        have hw : |(1608899473/5000000000 : ℝ)|=(1608899473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201029713/625000000 : ℝ)|^91 ≤ (12625774346543/50000000000000 : ℝ)^75
        have hw : |(-201029713/625000000 : ℝ)|=(201029713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5599991977/10000000000 : ℝ)|^91 ≤ (989685893657/2000000000000 : ℝ)^75
        have hw : |(5599991977/10000000000 : ℝ)|=(5599991977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (85094633/156250000 : ℝ)*x 0 + (5382853373/10000000000 : ℝ)*x 1 + (-423016537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85094633/156250000 : ℝ)^91 ≤ (47838732845777/100000000000000 : ℝ)^75 := by
    have hnat : (85094633 : ℕ)^91*100000000000000^75 ≤ 47838732845777^75*156250000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85094633 156250000 47838732845777 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5382853373/10000000000 : ℝ)^91 ≤ (47165947212889/100000000000000 : ℝ)^75 := by
    have hnat : (5382853373 : ℕ)^91*100000000000000^75 ≤ 47165947212889^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382853373 10000000000 47165947212889 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423016537/5000000000 : ℝ)^91 ≤ (4995319920119/100000000000000 : ℝ)^75 := by
    have hnat : (423016537 : ℕ)^91*100000000000000^75 ≤ 4995319920119^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423016537 5000000000 4995319920119 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85094633/156250000 : ℝ), (5382853373/10000000000 : ℝ), (-423016537/5000000000 : ℝ)] ![(47838732845777/100000000000000 : ℝ), (47165947212889/100000000000000 : ℝ), (4995319920119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85094633/156250000 : ℝ)|^91 ≤ (47838732845777/100000000000000 : ℝ)^75
        have hw : |(85094633/156250000 : ℝ)|=(85094633/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5382853373/10000000000 : ℝ)|^91 ≤ (47165947212889/100000000000000 : ℝ)^75
        have hw : |(5382853373/10000000000 : ℝ)|=(5382853373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423016537/5000000000 : ℝ)|^91 ≤ (4995319920119/100000000000000 : ℝ)^75
        have hw : |(-423016537/5000000000 : ℝ)|=(423016537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327059_s1_6 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2071400897/5000000000 : ℝ)*x 0 + (34018277/78125000 : ℝ)*x 1 + (3626176673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071400897/5000000000 : ℝ)^91 ≤ (6865627517407/20000000000000 : ℝ)^75 := by
    have hnat : (2071400897 : ℕ)^91*20000000000000^75 ≤ 6865627517407^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071400897 5000000000 6865627517407 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34018277/78125000 : ℝ)^91 ≤ (18233178099427/50000000000000 : ℝ)^75 := by
    have hnat : (34018277 : ℕ)^91*50000000000000^75 ≤ 18233178099427^75*78125000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34018277 78125000 18233178099427 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3626176673/10000000000 : ℝ)^91 ≤ (29205506192209/100000000000000 : ℝ)^75 := by
    have hnat : (3626176673 : ℕ)^91*100000000000000^75 ≤ 29205506192209^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3626176673 10000000000 29205506192209 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2071400897/5000000000 : ℝ), (34018277/78125000 : ℝ), (3626176673/10000000000 : ℝ)] ![(6865627517407/20000000000000 : ℝ), (18233178099427/50000000000000 : ℝ), (29205506192209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2071400897/5000000000 : ℝ)|^91 ≤ (6865627517407/20000000000000 : ℝ)^75
        have hw : |(2071400897/5000000000 : ℝ)|=(2071400897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34018277/78125000 : ℝ)|^91 ≤ (18233178099427/50000000000000 : ℝ)^75
        have hw : |(34018277/78125000 : ℝ)|=(34018277/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3626176673/10000000000 : ℝ)|^91 ≤ (29205506192209/100000000000000 : ℝ)^75
        have hw : |(3626176673/10000000000 : ℝ)|=(3626176673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327059 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (32523/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(331768592948963/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (89/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^89 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^89*1^16 ≤ 1^16*1^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2831768592948963/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2831768592948963/2500000000000000 : ℝ)^89 := by
      have hnat : (2 : ℕ)^16*2500000000000000^89 ≤ 2831768592948963^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2831768592948963 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2831768592948963/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6091785627482579/5000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6091785627482579/5000000000000000 : ℝ)^89 := by
      have hnat : (3 : ℕ)^16*5000000000000000^89 ≤ 6091785627482579^89*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6091785627482579 5000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6091785627482579/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (331768592948963/2500000000000000 : ℝ)) (beta := (428248441584653/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(331768592948963/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(428248441584653/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-290973089/1000000000 : ℝ)*X 0 0+(5819461/20000000 : ℝ)*X 0 1+(3067600861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2909730909/10000000000 : ℝ)*X 1 0+(-2909730397/10000000000 : ℝ)*X 1 1+(6135201793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1444395597/5000000000 : ℝ)*X 0 0+(6330105159/10000000000 : ℝ)*X 0 1+(1349856079/5000000000 : ℝ)*X 0 2+(1444395597/5000000000 : ℝ)*X 1 0+(6330105159/10000000000 : ℝ)*X 1 1+(1349856079/5000000000 : ℝ)*X 1 2+(1444395597/5000000000 : ℝ)*X 2 0+(6330105159/10000000000 : ℝ)*X 2 1+(1349856079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-143061571/625000000 : ℝ)*X 0 0+(582937267/10000000000 : ℝ)*X 0 1+(2082359433/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((859862117/5000000000 : ℝ)*X 1 0+(-1257298071/10000000000 : ℝ)*X 1 1+(8329437647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2069159949/5000000000 : ℝ)*X 2 0+(7074727871/10000000000 : ℝ)*X 2 1+(-647061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((992124149/5000000000 : ℝ)*X 0 0+(8070590729/10000000000 : ℝ)*X 0 1+(169424553/1250000000 : ℝ)*X 0 2+(992124149/5000000000 : ℝ)*X 1 0+(8070590729/10000000000 : ℝ)*X 1 1+(169424553/1250000000 : ℝ)*X 1 2+(992124149/5000000000 : ℝ)*X 2 0+(8070590729/10000000000 : ℝ)*X 2 1+(169424553/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-94286291/1000000000 : ℝ)*X 0 0+(1967375187/10000000000 : ℝ)*X 0 1+(8353974323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((171526319/2000000000 : ℝ)*X 1 0+(-50980801/250000000 : ℝ)*X 1 1+(1670794837/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4173208823/5000000000 : ℝ)*X 2 0+(2620425401/10000000000 : ℝ)*X 2 1+(-356221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3336600987/5000000000 : ℝ)*X 0 0+(171925581/500000000 : ℝ)*X 0 1+(1670389747/10000000000 : ℝ)*X 0 2+(3336600987/5000000000 : ℝ)*X 1 0+(171925581/500000000 : ℝ)*X 1 1+(1670389747/10000000000 : ℝ)*X 1 2+(3336600987/5000000000 : ℝ)*X 2 0+(171925581/500000000 : ℝ)*X 2 1+(1670389747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-203753179/400000000 : ℝ)*X 0 0+(2148272837/10000000000 : ℝ)*X 0 1+(2369691843/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1795672683/10000000000 : ℝ)*X 1 0+(-1322449131/5000000000 : ℝ)*X 1 1+(3622474513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8434409489/10000000000 : ℝ)*X 2 0+(2507188217/10000000000 : ℝ)*X 2 1+(-208911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((89927643/1000000000 : ℝ)*X 0 0+(4381379527/5000000000 : ℝ)*X 0 1+(1428000621/10000000000 : ℝ)*X 0 2+(89927643/1000000000 : ℝ)*X 1 0+(4381379527/5000000000 : ℝ)*X 1 1+(1428000621/10000000000 : ℝ)*X 1 2+(89927643/1000000000 : ℝ)*X 2 0+(4381379527/5000000000 : ℝ)*X 2 1+(1428000621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((12847/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12847/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2093250307847303149731/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (298100811519/250000000000 : ℝ)*(base7) + (2509/500000000000 : ℝ)*(base50) + (1343/100000000000 : ℝ)*(base60) + (46968254713/31250000000 : ℝ)*(major_s0_0) + (46968254713/31250000000 : ℝ)*(major_s0_1) + (46968254713/31250000000 : ℝ)*(major_s0_2) + (501839/1000000000000 : ℝ)*(sp_s0_0) + (196721/31250000000 : ℝ)*(sp_s0_6) + (82466299551/50000000000 : ℝ)*(sp_s0_7) + (1649363611863/1000000000000 : ℝ)*(sp_s0_8) + (1649363611863/1000000000000 : ℝ)*(sp_s0_9) + (1902618985651/1000000000000 : ℝ)*(sp_s0_13) + (9279751/250000000000 : ℝ)*(sp_s0_14) + (36009981/1000000000000 : ℝ)*(sp_s0_27) + (710258044627/1000000000000 : ℝ)*(f.failure) + (1649363611863/1000000000000 : ℝ)*(f.sum) + (2191544363/5000000000000000000000 : ℝ)*base62 + (6456188326067/19531250000000000000000000 : ℝ)*base64 + (24717795898857/78125000000000000000000000 : ℝ)*base67 + (479325471383/2441406250000000000000000 : ℝ)*base69 + (96127928605173/156250000000000000000000000 : ℝ)*base70 + (4916574936661/156250000000000000000000000 : ℝ)*base72 + (10690963432753/39062500000000000000000000 : ℝ)*base74 + (24442494307753/39062500000000000000000000 : ℝ)*base76 + (35097270361053/156250000000000000000000000 : ℝ)*base79 + (35903/100000000000000000 : ℝ)*base86 + (35903/100000000000000000 : ℝ)*base88 + (35903/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63979/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63979/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38959166854466597063793/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91524383059/250000000000 : ℝ)*(base5) + (1191933963987/1000000000000 : ℝ)*(base7) + (562689/500000000000 : ℝ)*(base19) + (311287/1000000000000 : ℝ)*(base53) + (132352300581/1000000000000 : ℝ)*(base60) + (372998711827/250000000000 : ℝ)*(major_s0_0) + (372998711827/250000000000 : ℝ)*(major_s0_1) + (1491994536021/1000000000000 : ℝ)*(major_s0_2) + (13262429/200000000000 : ℝ)*(sp_s0_8) + (408207875413/250000000000 : ℝ)*(sp_s0_14) + (163276406413/100000000000 : ℝ)*(sp_s0_15) + (999329605283/500000000000 : ℝ)*(sp_s0_16) + (306180262737/200000000000 : ℝ)*(sp_s0_20) + (270134609/1000000000000 : ℝ)*(sp_s0_23) + (705064881933/1000000000000 : ℝ)*(f.failure) + (1632831812939/1000000000000 : ℝ)*(f.sum) + (915178413654619/2500000000000000000000000000 : ℝ)*base62 + (1805239582714287/5000000000000000000000000000 : ℝ)*base64 + (78531088583969/1250000000000000000000000000 : ℝ)*base66 + (1526669185596223/2500000000000000000000000000 : ℝ)*base68 + (550423129331079/5000000000000000000000000000 : ℝ)*base70 + (1126121747208969/1250000000000000000000000000 : ℝ)*base72 + (373246258702099/625000000000000000000000000 : ℝ)*base74 + (229248895702099/625000000000000000000000000 : ℝ)*base76 + (58511472458969/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (75937/100000000000000000 : ℝ)*base86 + (75937/100000000000000000 : ℝ)*base88 + (75937/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(45701/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(45701/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15662199634797030489/4882812500000000000000000 : ℝ) := by norm_num
    linear_combination (19456629851/31250000000 : ℝ)*(base7) + (321853/200000000000 : ℝ)*(base11) + (253316887097/500000000000 : ℝ)*(base44) + (51025852899/500000000000 : ℝ)*(base50) + (780043311249/500000000000 : ℝ)*(major_s0_0) + (65840803019/62500000000 : ℝ)*(major_s0_1) + (780043311249/500000000000 : ℝ)*(major_s0_2) + (13029881/1000000000000 : ℝ)*(sp_s0_1) + (10239599/500000000000 : ℝ)*(sp_s0_13) + (14883683/125000000000 : ℝ)*(sp_s0_16) + (2045440960723/1000000000000 : ℝ)*(sp_s0_21) + (1538795765913/1000000000000 : ℝ)*(sp_s0_22) + (81812940021/40000000000 : ℝ)*(sp_s0_23) + (213300147223/250000000000 : ℝ)*(sp_s0_27) + (184310671763/250000000000 : ℝ)*(f.failure) + (511360642497/250000000000 : ℝ)*(f.sum) + (300086821605411/1250000000000000000000000000 : ℝ)*base62 + (2060233695411597/2500000000000000000000000000 : ℝ)*base65 + (136670922029907/312500000000000000000000000 : ℝ)*base67 + (169984447715213/1250000000000000000000000000 : ℝ)*base69 + (589777335481171/2500000000000000000000000000 : ℝ)*base71 + (750570546911597/2500000000000000000000000000 : ℝ)*base73 + (9912873087041/19531250000000000000000000 : ℝ)*base74 + (525313118409787/1250000000000000000000000000 : ℝ)*base77 + (674595822150853/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (9807/25000000000000000 : ℝ)*base86 + (9807/25000000000000000 : ℝ)*base88 + (9807/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (12847/20000 : ℝ) ^ (89/16 : ℝ) ≤ (852570378495241829/10000000000000000000 : ℝ) := by
    have hpowers : (12847/20000 : ℝ)^89 ≤ (852570378495241829/10000000000000000000 : ℝ)^16 := by
      have hnat : (12847 : ℕ)^89*10000000000000000000^16 ≤ 852570378495241829^16*20000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12847 20000 852570378495241829 10000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12847/20000 : ℝ)) (X := (852570378495241829/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10852570378495241829/10000000000000000000 : ℝ) ≤ (2537043383776359/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (10852570378495241829/10000000000000000000 : ℝ)^16 ≤ (2537043383776359/2500000000000000 : ℝ)^89 := by
      have hnat : (10852570378495241829 : ℕ)^16*2500000000000000^89 ≤ 2537043383776359^89*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10852570378495241829 10000000000000000000 2537043383776359 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2537043383776359/2500000000000000 : ℝ)) (X := (10852570378495241829/10000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5852570378495241829/5000000000000000000 : ℝ) ≤ (10287087402561893/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (5852570378495241829/5000000000000000000 : ℝ)^16 ≤ (10287087402561893/10000000000000000 : ℝ)^89 := by
      have hnat : (5852570378495241829 : ℕ)^16*10000000000000000^89 ≤ 10287087402561893^89*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5852570378495241829 5000000000000000000 10287087402561893 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10287087402561893/10000000000000000 : ℝ)) (X := (5852570378495241829/5000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(37043383776359/1605875000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(138913867456457/6423500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (12847/20000 : ℝ)) (alpha := (37043383776359/1605875000000000 : ℝ)) (beta := (138913867456457/6423500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12847/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(37043383776359/1605875000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(138913867456457/6423500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (63979/100000 : ℝ) ^ (89/16 : ℝ) ≤ (833841110133961891/10000000000000000000 : ℝ) := by
    have hpowers : (63979/100000 : ℝ)^89 ≤ (833841110133961891/10000000000000000000 : ℝ)^16 := by
      have hnat : (63979 : ℕ)^89*10000000000000000000^16 ≤ 833841110133961891^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63979 100000 833841110133961891 10000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63979/100000 : ℝ)) (X := (833841110133961891/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10833841110133961891/10000000000000000000 : ℝ) ≤ (2536255696800747/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (10833841110133961891/10000000000000000000 : ℝ)^16 ≤ (2536255696800747/2500000000000000 : ℝ)^89 := by
      have hnat : (10833841110133961891 : ℕ)^16*2500000000000000^89 ≤ 2536255696800747^89*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10833841110133961891 10000000000000000000 2536255696800747 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2536255696800747/2500000000000000 : ℝ)) (X := (10833841110133961891/10000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5833841110133961891/5000000000000000000 : ℝ) ≤ (10281161325568493/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (5833841110133961891/5000000000000000000 : ℝ)^16 ≤ (10281161325568493/10000000000000000 : ℝ)^89 := by
      have hnat : (5833841110133961891 : ℕ)^16*10000000000000000^89 ≤ 10281161325568493^89*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5833841110133961891 5000000000000000000 10281161325568493 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10281161325568493/10000000000000000 : ℝ)) (X := (5833841110133961891/5000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(36255696800747/1599475000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(27227707673101/1279580000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (63979/100000 : ℝ)) (alpha := (36255696800747/1599475000000000 : ℝ)) (beta := (27227707673101/1279580000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (63979/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(36255696800747/1599475000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(27227707673101/1279580000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (45701/100000 : ℝ) ^ (89/16 : ℝ) ≤ (320831300944017137/25000000000000000000 : ℝ) := by
    have hpowers : (45701/100000 : ℝ)^89 ≤ (320831300944017137/25000000000000000000 : ℝ)^16 := by
      have hnat : (45701 : ℕ)^89*25000000000000000000^16 ≤ 320831300944017137^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45701 100000 320831300944017137 25000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45701/100000 : ℝ)) (X := (320831300944017137/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25320831300944017137/25000000000000000000 : ℝ) ≤ (2505737631851849/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (25320831300944017137/25000000000000000000 : ℝ)^16 ≤ (2505737631851849/2500000000000000 : ℝ)^89 := by
      have hnat : (25320831300944017137 : ℕ)^16*2500000000000000^89 ≤ 2505737631851849^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25320831300944017137 25000000000000000000 2505737631851849 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505737631851849/2500000000000000 : ℝ)) (X := (25320831300944017137/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12820831300944017137/12500000000000000000 : ℝ) ≤ (2511415940335787/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (12820831300944017137/12500000000000000000 : ℝ)^16 ≤ (2511415940335787/2500000000000000 : ℝ)^89 := by
      have hnat : (12820831300944017137 : ℕ)^16*2500000000000000^89 ≤ 2511415940335787^89*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12820831300944017137 12500000000000000000 2511415940335787 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511415940335787/2500000000000000 : ℝ)) (X := (12820831300944017137/12500000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5737631851849/1142525000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2839154241969/571262500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (45701/100000 : ℝ)) (alpha := (5737631851849/1142525000000000 : ℝ)) (beta := (2839154241969/571262500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (45701/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5737631851849/1142525000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2839154241969/571262500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-643816101/2000000000 : ℝ)*X 0 0+(3217768301/10000000000 : ℝ)*X 0 1+(1119540887/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1608899473/5000000000 : ℝ)*X 1 0+(-201029713/625000000 : ℝ)*X 1 1+(5599991977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((85094633/156250000 : ℝ)*X 2 0+(5382853373/10000000000 : ℝ)*X 2 1+(-423016537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2071400897/5000000000 : ℝ)*X 0 0+(34018277/78125000 : ℝ)*X 0 1+(3626176673/10000000000 : ℝ)*X 0 2+(2071400897/5000000000 : ℝ)*X 1 0+(34018277/78125000 : ℝ)*X 1 1+(3626176673/10000000000 : ℝ)*X 1 2+(2071400897/5000000000 : ℝ)*X 2 0+(34018277/78125000 : ℝ)*X 2 1+(3626176673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-484833/50000 : ℝ) < ((-211611/100000 : ℝ)*P 0+(-211611/100000 : ℝ)*P 1+(-211611/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-484833/50000 : ℝ) < (-3620690995870307230641038962913366343/375633982723130000000000000000000000 : ℝ) := by norm_num
    linear_combination (3151/125000000000 : ℝ)*(base1) + (53041/200000000000 : ℝ)*(base13) + (47639/1000000000000 : ℝ)*(base16) + (43447/1000000000000 : ℝ)*(base21) + (1913/100000000000 : ℝ)*(base31) + (3513/125000000000 : ℝ)*(base40) + (17683/1000000000000 : ℝ)*(base50) + (657337025973/1000000000000 : ℝ)*(base60) + (211611/100000 : ℝ)*(major_s1_0) + (211611/100000 : ℝ)*(major_s1_1) + (211611/100000 : ℝ)*(major_s1_2) + (321295985981/100000000000 : ℝ)*(sp_s1_0) + (3212960052169/1000000000000 : ℝ)*(sp_s1_1) + (3212960056361/1000000000000 : ℝ)*(sp_s1_2) + (999999955663/1000000000000 : ℝ)*(sp_s1_6) + (100405003119/31250000000 : ℝ)*(f.sum) + (3424234260606265803/7309760697500000000000000000000 : ℝ)*base63 + (91793703435631/228505000000000000000000000 : ℝ)*base65 + (28834241898471/639790000000000000000000000 : ℝ)*base66 + (7939661518719/28563125000000000000000000 : ℝ)*base69 + (162202331186217883/366950466875000000000000000000 : ℝ)*base71 + (3443723630227/4014687500000000000000000 : ℝ)*base72 + (26243264839333/319895000000000000000000000 : ℝ)*base74 + (21392810179093/128470000000000000000000000 : ℝ)*base77 + (1183074348892675661/1643876426000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p027_b029 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c327059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p027_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
