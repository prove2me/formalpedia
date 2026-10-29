-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:33:16.619043+00:00
-- url     : https://prove2.me/submissions/c5a25f69-a780-48b4-b33c-672db0671008

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
theorem collision_support_c330060_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-608749009/5000000000 : ℝ)*x 0 + (179208379/400000000 : ℝ)*x 1 + (-2985286187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (608749009/5000000000 : ℝ)^6 ≤ (199756961863/2500000000000 : ℝ)^5 := by
    have hnat : (608749009 : ℕ)^6*2500000000000^5 ≤ 199756961863^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608749009 5000000000 199756961863 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179208379/400000000 : ℝ)^6 ≤ (38155573375869/100000000000000 : ℝ)^5 := by
    have hnat : (179208379 : ℕ)^6*100000000000000^5 ≤ 38155573375869^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179208379 400000000 38155573375869 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2985286187/5000000000 : ℝ)^6 ≤ (10770829625813/20000000000000 : ℝ)^5 := by
    have hnat : (2985286187 : ℕ)^6*20000000000000^5 ≤ 10770829625813^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985286187 5000000000 10770829625813 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-608749009/5000000000 : ℝ), (179208379/400000000 : ℝ), (-2985286187/5000000000 : ℝ)] ![(199756961863/2500000000000 : ℝ), (38155573375869/100000000000000 : ℝ), (10770829625813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-608749009/5000000000 : ℝ)|^6 ≤ (199756961863/2500000000000 : ℝ)^5
        have hw : |(-608749009/5000000000 : ℝ)|=(608749009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179208379/400000000 : ℝ)|^6 ≤ (38155573375869/100000000000000 : ℝ)^5
        have hw : |(179208379/400000000 : ℝ)|=(179208379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2985286187/5000000000 : ℝ)|^6 ≤ (10770829625813/20000000000000 : ℝ)^5
        have hw : |(-2985286187/5000000000 : ℝ)|=(2985286187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2240105053/5000000000 : ℝ)*x 0 + (-608748759/5000000000 : ℝ)*x 1 + (-5970572143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240105053/5000000000 : ℝ)^6 ≤ (38155579824541/100000000000000 : ℝ)^5 := by
    have hnat : (2240105053 : ℕ)^6*100000000000000^5 ≤ 38155579824541^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240105053 5000000000 38155579824541 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608748759/5000000000 : ℝ)^6 ≤ (9987843171/125000000000 : ℝ)^5 := by
    have hnat : (608748759 : ℕ)^6*125000000000^5 ≤ 9987843171^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608748759 5000000000 9987843171 125000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5970572143/10000000000 : ℝ)^6 ≤ (2692707281437/5000000000000 : ℝ)^5 := by
    have hnat : (5970572143 : ℕ)^6*5000000000000^5 ≤ 2692707281437^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970572143 10000000000 2692707281437 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240105053/5000000000 : ℝ), (-608748759/5000000000 : ℝ), (-5970572143/10000000000 : ℝ)] ![(38155579824541/100000000000000 : ℝ), (9987843171/125000000000 : ℝ), (2692707281437/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240105053/5000000000 : ℝ)|^6 ≤ (38155579824541/100000000000000 : ℝ)^5
        have hw : |(2240105053/5000000000 : ℝ)|=(2240105053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608748759/5000000000 : ℝ)|^6 ≤ (9987843171/125000000000 : ℝ)^5
        have hw : |(-608748759/5000000000 : ℝ)|=(608748759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5970572143/10000000000 : ℝ)|^6 ≤ (2692707281437/5000000000000 : ℝ)^5
        have hw : |(-5970572143/10000000000 : ℝ)|=(5970572143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-376352399/2000000000 : ℝ)*x 0 + (1531793279/10000000000 : ℝ)*x 1 + (-1591158553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376352399/2000000000 : ℝ)^6 ≤ (6736706643817/50000000000000 : ℝ)^5 := by
    have hnat : (376352399 : ℕ)^6*50000000000000^5 ≤ 6736706643817^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376352399 2000000000 6736706643817 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531793279/10000000000 : ℝ)^6 ≤ (10525438344109/100000000000000 : ℝ)^5 := by
    have hnat : (1531793279 : ℕ)^6*100000000000000^5 ≤ 10525438344109^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531793279 10000000000 10525438344109 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1591158553/2000000000 : ℝ)^6 ≤ (19000287086991/25000000000000 : ℝ)^5 := by
    have hnat : (1591158553 : ℕ)^6*25000000000000^5 ≤ 19000287086991^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591158553 2000000000 19000287086991 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-376352399/2000000000 : ℝ), (1531793279/10000000000 : ℝ), (-1591158553/2000000000 : ℝ)] ![(6736706643817/50000000000000 : ℝ), (10525438344109/100000000000000 : ℝ), (19000287086991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-376352399/2000000000 : ℝ)|^6 ≤ (6736706643817/50000000000000 : ℝ)^5
        have hw : |(-376352399/2000000000 : ℝ)|=(376352399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1531793279/10000000000 : ℝ)|^6 ≤ (10525438344109/100000000000000 : ℝ)^5
        have hw : |(1531793279/10000000000 : ℝ)|=(1531793279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1591158553/2000000000 : ℝ)|^6 ≤ (19000287086991/25000000000000 : ℝ)^5
        have hw : |(-1591158553/2000000000 : ℝ)|=(1591158553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2579084807/10000000000 : ℝ)*x 0 + (-3654139/50000000 : ℝ)*x 1 + (-1988948589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2579084807/10000000000 : ℝ)^6 ≤ (245849178097/1250000000000 : ℝ)^5 := by
    have hnat : (2579084807 : ℕ)^6*1250000000000^5 ≤ 245849178097^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579084807 10000000000 245849178097 1250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3654139/50000000 : ℝ)^6 ≤ (2165449575891/50000000000000 : ℝ)^5 := by
    have hnat : (3654139 : ℕ)^6*50000000000000^5 ≤ 2165449575891^5*50000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3654139 50000000 2165449575891 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988948589/2500000000 : ℝ)^6 ≤ (76001166586423/100000000000000 : ℝ)^5 := by
    have hnat : (1988948589 : ℕ)^6*100000000000000^5 ≤ 76001166586423^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988948589 2500000000 76001166586423 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2579084807/10000000000 : ℝ), (-3654139/50000000 : ℝ), (-1988948589/2500000000 : ℝ)] ![(245849178097/1250000000000 : ℝ), (2165449575891/50000000000000 : ℝ), (76001166586423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2579084807/10000000000 : ℝ)|^6 ≤ (245849178097/1250000000000 : ℝ)^5
        have hw : |(2579084807/10000000000 : ℝ)|=(2579084807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3654139/50000000 : ℝ)|^6 ≤ (2165449575891/50000000000000 : ℝ)^5
        have hw : |(-3654139/50000000 : ℝ)|=(3654139/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988948589/2500000000 : ℝ)|^6 ≤ (76001166586423/100000000000000 : ℝ)^5
        have hw : |(-1988948589/2500000000 : ℝ)|=(1988948589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2340344331/10000000000 : ℝ)*x 0 + (1951023791/2500000000 : ℝ)*x 1 + (623967049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2340344331/10000000000 : ℝ)^6 ≤ (1750393576759/10000000000000 : ℝ)^5 := by
    have hnat : (2340344331 : ℕ)^6*10000000000000^5 ≤ 1750393576759^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340344331 10000000000 1750393576759 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1951023791/2500000000 : ℝ)^6 ≤ (74265492916917/100000000000000 : ℝ)^5 := by
    have hnat : (1951023791 : ℕ)^6*100000000000000^5 ≤ 74265492916917^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951023791 2500000000 74265492916917 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623967049/5000000000 : ℝ)^6 ≤ (4115285651249/50000000000000 : ℝ)^5 := by
    have hnat : (623967049 : ℕ)^6*50000000000000^5 ≤ 4115285651249^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623967049 5000000000 4115285651249 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2340344331/10000000000 : ℝ), (1951023791/2500000000 : ℝ), (623967049/5000000000 : ℝ)] ![(1750393576759/10000000000000 : ℝ), (74265492916917/100000000000000 : ℝ), (4115285651249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2340344331/10000000000 : ℝ)|^6 ≤ (1750393576759/10000000000000 : ℝ)^5
        have hw : |(2340344331/10000000000 : ℝ)|=(2340344331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1951023791/2500000000 : ℝ)|^6 ≤ (74265492916917/100000000000000 : ℝ)^5
        have hw : |(1951023791/2500000000 : ℝ)|=(1951023791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(623967049/5000000000 : ℝ)|^6 ≤ (4115285651249/50000000000000 : ℝ)^5
        have hw : |(623967049/5000000000 : ℝ)|=(623967049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (859663899/2000000000 : ℝ)*x 0 + (6866496087/10000000000 : ℝ)*x 1 + (-3423/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859663899/2000000000 : ℝ)^6 ≤ (7260866101113/20000000000000 : ℝ)^5 := by
    have hnat : (859663899 : ℕ)^6*20000000000000^5 ≤ 7260866101113^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859663899 2000000000 7260866101113 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6866496087/10000000000 : ℝ)^6 ≤ (2547664312823/4000000000000 : ℝ)^5 := by
    have hnat : (6866496087 : ℕ)^6*4000000000000^5 ≤ 2547664312823^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6866496087 10000000000 2547664312823 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3423/15625000 : ℝ)^6 ≤ (4061666377/100000000000000 : ℝ)^5 := by
    have hnat : (3423 : ℕ)^6*100000000000000^5 ≤ 4061666377^5*15625000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423 15625000 4061666377 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859663899/2000000000 : ℝ), (6866496087/10000000000 : ℝ), (-3423/15625000 : ℝ)] ![(7260866101113/20000000000000 : ℝ), (2547664312823/4000000000000 : ℝ), (4061666377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859663899/2000000000 : ℝ)|^6 ≤ (7260866101113/20000000000000 : ℝ)^5
        have hw : |(859663899/2000000000 : ℝ)|=(859663899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6866496087/10000000000 : ℝ)|^6 ≤ (2547664312823/4000000000000 : ℝ)^5
        have hw : |(6866496087/10000000000 : ℝ)|=(6866496087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3423/15625000 : ℝ)|^6 ≤ (4061666377/100000000000000 : ℝ)^5
        have hw : |(-3423/15625000 : ℝ)|=(3423/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-241034981/2500000000 : ℝ)*x 0 + (223173371/1000000000 : ℝ)*x 1 + (-8080001153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241034981/2500000000 : ℝ)^6 ≤ (1509760605181/25000000000000 : ℝ)^5 := by
    have hnat : (241034981 : ℕ)^6*25000000000000^5 ≤ 1509760605181^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241034981 2500000000 1509760605181 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223173371/1000000000 : ℝ)^6 ≤ (16533730262887/100000000000000 : ℝ)^5 := by
    have hnat : (223173371 : ℕ)^6*100000000000000^5 ≤ 16533730262887^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223173371 1000000000 16533730262887 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8080001153/10000000000 : ℝ)^6 ≤ (19356806825637/25000000000000 : ℝ)^5 := by
    have hnat : (8080001153 : ℕ)^6*25000000000000^5 ≤ 19356806825637^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8080001153 10000000000 19356806825637 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241034981/2500000000 : ℝ), (223173371/1000000000 : ℝ), (-8080001153/10000000000 : ℝ)] ![(1509760605181/25000000000000 : ℝ), (16533730262887/100000000000000 : ℝ), (19356806825637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241034981/2500000000 : ℝ)|^6 ≤ (1509760605181/25000000000000 : ℝ)^5
        have hw : |(-241034981/2500000000 : ℝ)|=(241034981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223173371/1000000000 : ℝ)|^6 ≤ (16533730262887/100000000000000 : ℝ)^5
        have hw : |(223173371/1000000000 : ℝ)|=(223173371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8080001153/10000000000 : ℝ)|^6 ≤ (19356806825637/25000000000000 : ℝ)^5
        have hw : |(-8080001153/10000000000 : ℝ)|=(8080001153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (532283731/5000000000 : ℝ)*x 0 + (-2145631833/10000000000 : ℝ)*x 1 + (-4039999233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532283731/5000000000 : ℝ)^6 ≤ (3400774456721/50000000000000 : ℝ)^5 := by
    have hnat : (532283731 : ℕ)^6*50000000000000^5 ≤ 3400774456721^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532283731 5000000000 3400774456721 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145631833/10000000000 : ℝ)^6 ≤ (7885627333743/50000000000000 : ℝ)^5 := by
    have hnat : (2145631833 : ℕ)^6*50000000000000^5 ≤ 7885627333743^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145631833 10000000000 7885627333743 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4039999233/5000000000 : ℝ)^6 ≤ (7742719640449/10000000000000 : ℝ)^5 := by
    have hnat : (4039999233 : ℕ)^6*10000000000000^5 ≤ 7742719640449^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039999233 5000000000 7742719640449 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532283731/5000000000 : ℝ), (-2145631833/10000000000 : ℝ), (-4039999233/5000000000 : ℝ)] ![(3400774456721/50000000000000 : ℝ), (7885627333743/50000000000000 : ℝ), (7742719640449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532283731/5000000000 : ℝ)|^6 ≤ (3400774456721/50000000000000 : ℝ)^5
        have hw : |(532283731/5000000000 : ℝ)|=(532283731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145631833/10000000000 : ℝ)|^6 ≤ (7885627333743/50000000000000 : ℝ)^5
        have hw : |(-2145631833/10000000000 : ℝ)|=(2145631833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4039999233/5000000000 : ℝ)|^6 ≤ (7742719640449/10000000000000 : ℝ)^5
        have hw : |(-4039999233/5000000000 : ℝ)|=(4039999233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (810987153/1250000000 : ℝ)*x 0 + (3775706067/10000000000 : ℝ)*x 1 + (139710839/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810987153/1250000000 : ℝ)^6 ≤ (59501067007853/100000000000000 : ℝ)^5 := by
    have hnat : (810987153 : ℕ)^6*100000000000000^5 ≤ 59501067007853^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810987153 1250000000 59501067007853 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3775706067/10000000000 : ℝ)^6 ≤ (31074046645791/100000000000000 : ℝ)^5 := by
    have hnat : (3775706067 : ℕ)^6*100000000000000^5 ≤ 31074046645791^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3775706067 10000000000 31074046645791 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139710839/1000000000 : ℝ)^6 ≤ (1884977265161/20000000000000 : ℝ)^5 := by
    have hnat : (139710839 : ℕ)^6*20000000000000^5 ≤ 1884977265161^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139710839 1000000000 1884977265161 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(810987153/1250000000 : ℝ), (3775706067/10000000000 : ℝ), (139710839/1000000000 : ℝ)] ![(59501067007853/100000000000000 : ℝ), (31074046645791/100000000000000 : ℝ), (1884977265161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(810987153/1250000000 : ℝ)|^6 ≤ (59501067007853/100000000000000 : ℝ)^5
        have hw : |(810987153/1250000000 : ℝ)|=(810987153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3775706067/10000000000 : ℝ)|^6 ≤ (31074046645791/100000000000000 : ℝ)^5
        have hw : |(3775706067/10000000000 : ℝ)|=(3775706067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139710839/1000000000 : ℝ)|^6 ≤ (1884977265161/20000000000000 : ℝ)^5
        have hw : |(139710839/1000000000 : ℝ)|=(139710839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (8345133171/10000000000 : ℝ)*x 0 + (160112837/625000000 : ℝ)*x 1 + (-559067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8345133171/10000000000 : ℝ)^6 ≤ (16097184487729/20000000000000 : ℝ)^5 := by
    have hnat : (8345133171 : ℕ)^6*20000000000000^5 ≤ 16097184487729^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8345133171 10000000000 16097184487729 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160112837/625000000 : ℝ)^6 ≤ (19509914335281/100000000000000 : ℝ)^5 := by
    have hnat : (160112837 : ℕ)^6*100000000000000^5 ≤ 19509914335281^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160112837 625000000 19509914335281 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559067/2500000000 : ℝ)^6 ≤ (4163212887/100000000000000 : ℝ)^5 := by
    have hnat : (559067 : ℕ)^6*100000000000000^5 ≤ 4163212887^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559067 2500000000 4163212887 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8345133171/10000000000 : ℝ), (160112837/625000000 : ℝ), (-559067/2500000000 : ℝ)] ![(16097184487729/20000000000000 : ℝ), (19509914335281/100000000000000 : ℝ), (4163212887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8345133171/10000000000 : ℝ)|^6 ≤ (16097184487729/20000000000000 : ℝ)^5
        have hw : |(8345133171/10000000000 : ℝ)|=(8345133171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160112837/625000000 : ℝ)|^6 ≤ (19509914335281/100000000000000 : ℝ)^5
        have hw : |(160112837/625000000 : ℝ)|=(160112837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559067/2500000000 : ℝ)|^6 ≤ (4163212887/100000000000000 : ℝ)^5
        have hw : |(-559067/2500000000 : ℝ)|=(559067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-93858193/2500000000 : ℝ)*x 0 + (769357429/1250000000 : ℝ)*x 1 + (-4872375473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93858193/2500000000 : ℝ)^6 ≤ (24341572401/1250000000000 : ℝ)^5 := by
    have hnat : (93858193 : ℕ)^6*1250000000000^5 ≤ 24341572401^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93858193 2500000000 24341572401 1250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769357429/1250000000 : ℝ)^6 ≤ (2234198509793/4000000000000 : ℝ)^5 := by
    have hnat : (769357429 : ℕ)^6*4000000000000^5 ≤ 2234198509793^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769357429 1250000000 2234198509793 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4872375473/10000000000 : ℝ)^6 ≤ (10549427860671/25000000000000 : ℝ)^5 := by
    have hnat : (4872375473 : ℕ)^6*25000000000000^5 ≤ 10549427860671^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4872375473 10000000000 10549427860671 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93858193/2500000000 : ℝ), (769357429/1250000000 : ℝ), (-4872375473/10000000000 : ℝ)] ![(24341572401/1250000000000 : ℝ), (2234198509793/4000000000000 : ℝ), (10549427860671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93858193/2500000000 : ℝ)|^6 ≤ (24341572401/1250000000000 : ℝ)^5
        have hw : |(-93858193/2500000000 : ℝ)|=(93858193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769357429/1250000000 : ℝ)|^6 ≤ (2234198509793/4000000000000 : ℝ)^5
        have hw : |(769357429/1250000000 : ℝ)|=(769357429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4872375473/10000000000 : ℝ)|^6 ≤ (10549427860671/25000000000000 : ℝ)^5
        have hw : |(-4872375473/10000000000 : ℝ)|=(4872375473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3318876401/5000000000 : ℝ)*x 0 + (-858326133/10000000000 : ℝ)*x 1 + (-12590991/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3318876401/5000000000 : ℝ)^6 ≤ (30577029623319/50000000000000 : ℝ)^5 := by
    have hnat : (3318876401 : ℕ)^6*50000000000000^5 ≤ 30577029623319^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3318876401 5000000000 30577029623319 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858326133/10000000000 : ℝ)^6 ≤ (262635124039/5000000000000 : ℝ)^5 := by
    have hnat : (858326133 : ℕ)^6*5000000000000^5 ≤ 262635124039^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858326133 10000000000 262635124039 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12590991/31250000 : ℝ)^6 ≤ (1679661912969/5000000000000 : ℝ)^5 := by
    have hnat : (12590991 : ℕ)^6*5000000000000^5 ≤ 1679661912969^5*31250000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12590991 31250000 1679661912969 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3318876401/5000000000 : ℝ), (-858326133/10000000000 : ℝ), (-12590991/31250000 : ℝ)] ![(30577029623319/50000000000000 : ℝ), (262635124039/5000000000000 : ℝ), (1679661912969/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3318876401/5000000000 : ℝ)|^6 ≤ (30577029623319/50000000000000 : ℝ)^5
        have hw : |(3318876401/5000000000 : ℝ)|=(3318876401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-858326133/10000000000 : ℝ)|^6 ≤ (262635124039/5000000000000 : ℝ)^5
        have hw : |(-858326133/10000000000 : ℝ)|=(858326133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12590991/31250000 : ℝ)|^6 ≤ (1679661912969/5000000000000 : ℝ)^5
        have hw : |(-12590991/31250000 : ℝ)|=(12590991/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (37188011/250000000 : ℝ)*x 0 + (60795109/78125000 : ℝ)*x 1 + (17216401/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37188011/250000000 : ℝ)^6 ≤ (10161446395899/100000000000000 : ℝ)^5 := by
    have hnat : (37188011 : ℕ)^6*100000000000000^5 ≤ 10161446395899^5*250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37188011 250000000 10161446395899 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60795109/78125000 : ℝ)^6 ≤ (74010669578877/100000000000000 : ℝ)^5 := by
    have hnat : (60795109 : ℕ)^6*100000000000000^5 ≤ 74010669578877^5*78125000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60795109 78125000 74010669578877 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17216401/80000000 : ℝ)^6 ≤ (126623072109/800000000000 : ℝ)^5 := by
    have hnat : (17216401 : ℕ)^6*800000000000^5 ≤ 126623072109^5*80000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17216401 80000000 126623072109 800000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(37188011/250000000 : ℝ), (60795109/78125000 : ℝ), (17216401/80000000 : ℝ)] ![(10161446395899/100000000000000 : ℝ), (74010669578877/100000000000000 : ℝ), (126623072109/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(37188011/250000000 : ℝ)|^6 ≤ (10161446395899/100000000000000 : ℝ)^5
        have hw : |(37188011/250000000 : ℝ)|=(37188011/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60795109/78125000 : ℝ)|^6 ≤ (74010669578877/100000000000000 : ℝ)^5
        have hw : |(60795109/78125000 : ℝ)|=(60795109/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17216401/80000000 : ℝ)|^6 ≤ (126623072109/800000000000 : ℝ)^5
        have hw : |(17216401/80000000 : ℝ)|=(17216401/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (285612993/312500000 : ℝ)*x 0 + (1477501279/10000000000 : ℝ)*x 1 + (-45388039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285612993/312500000 : ℝ)^6 ≤ (22441585418569/25000000000000 : ℝ)^5 := by
    have hnat : (285612993 : ℕ)^6*25000000000000^5 ≤ 22441585418569^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285612993 312500000 22441585418569 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477501279/10000000000 : ℝ)^6 ≤ (10079371177717/100000000000000 : ℝ)^5 := by
    have hnat : (1477501279 : ℕ)^6*100000000000000^5 ≤ 10079371177717^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477501279 10000000000 10079371177717 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45388039/10000000000 : ℝ)^6 ≤ (154287130969/100000000000000 : ℝ)^5 := by
    have hnat : (45388039 : ℕ)^6*100000000000000^5 ≤ 154287130969^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45388039 10000000000 154287130969 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(285612993/312500000 : ℝ), (1477501279/10000000000 : ℝ), (-45388039/10000000000 : ℝ)] ![(22441585418569/25000000000000 : ℝ), (10079371177717/100000000000000 : ℝ), (154287130969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(285612993/312500000 : ℝ)|^6 ≤ (22441585418569/25000000000000 : ℝ)^5
        have hw : |(285612993/312500000 : ℝ)|=(285612993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477501279/10000000000 : ℝ)|^6 ≤ (10079371177717/100000000000000 : ℝ)^5
        have hw : |(1477501279/10000000000 : ℝ)|=(1477501279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45388039/10000000000 : ℝ)|^6 ≤ (154287130969/100000000000000 : ℝ)^5
        have hw : |(-45388039/10000000000 : ℝ)|=(45388039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-232729467/1250000000 : ℝ)*x 0 + (1899611043/5000000000 : ℝ)*x 1 + (-611224127/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232729467/1250000000 : ℝ)^6 ≤ (3325597177671/25000000000000 : ℝ)^5 := by
    have hnat : (232729467 : ℕ)^6*25000000000000^5 ≤ 3325597177671^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232729467 1250000000 3325597177671 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899611043/5000000000 : ℝ)^6 ≤ (31306435150389/100000000000000 : ℝ)^5 := by
    have hnat : (1899611043 : ℕ)^6*100000000000000^5 ≤ 31306435150389^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899611043 5000000000 31306435150389 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611224127/1000000000 : ℝ)^6 ≤ (55391176131441/100000000000000 : ℝ)^5 := by
    have hnat : (611224127 : ℕ)^6*100000000000000^5 ≤ 55391176131441^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611224127 1000000000 55391176131441 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232729467/1250000000 : ℝ), (1899611043/5000000000 : ℝ), (-611224127/1000000000 : ℝ)] ![(3325597177671/25000000000000 : ℝ), (31306435150389/100000000000000 : ℝ), (55391176131441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232729467/1250000000 : ℝ)|^6 ≤ (3325597177671/25000000000000 : ℝ)^5
        have hw : |(-232729467/1250000000 : ℝ)|=(232729467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1899611043/5000000000 : ℝ)|^6 ≤ (31306435150389/100000000000000 : ℝ)^5
        have hw : |(1899611043/5000000000 : ℝ)|=(1899611043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-611224127/1000000000 : ℝ)|^6 ≤ (55391176131441/100000000000000 : ℝ)^5
        have hw : |(-611224127/1000000000 : ℝ)|=(611224127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2261199167/5000000000 : ℝ)*x 0 + (-2584501159/10000000000 : ℝ)*x 1 + (-602998699/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2261199167/5000000000 : ℝ)^6 ≤ (19293569298583/50000000000000 : ℝ)^5 := by
    have hnat : (2261199167 : ℕ)^6*50000000000000^5 ≤ 19293569298583^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261199167 5000000000 19293569298583 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584501159/10000000000 : ℝ)^6 ≤ (3943502070421/20000000000000 : ℝ)^5 := by
    have hnat : (2584501159 : ℕ)^6*20000000000000^5 ≤ 3943502070421^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584501159 10000000000 3943502070421 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602998699/1250000000 : ℝ)^6 ≤ (41695351036213/100000000000000 : ℝ)^5 := by
    have hnat : (602998699 : ℕ)^6*100000000000000^5 ≤ 41695351036213^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602998699 1250000000 41695351036213 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2261199167/5000000000 : ℝ), (-2584501159/10000000000 : ℝ), (-602998699/1250000000 : ℝ)] ![(19293569298583/50000000000000 : ℝ), (3943502070421/20000000000000 : ℝ), (41695351036213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2261199167/5000000000 : ℝ)|^6 ≤ (19293569298583/50000000000000 : ℝ)^5
        have hw : |(2261199167/5000000000 : ℝ)|=(2261199167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2584501159/10000000000 : ℝ)|^6 ≤ (3943502070421/20000000000000 : ℝ)^5
        have hw : |(-2584501159/10000000000 : ℝ)|=(2584501159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-602998699/1250000000 : ℝ)|^6 ≤ (41695351036213/100000000000000 : ℝ)^5
        have hw : |(-602998699/1250000000 : ℝ)|=(602998699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4570269013/10000000000 : ℝ)*x 0 + (688803727/1250000000 : ℝ)*x 1 + (341951281/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4570269013/10000000000 : ℝ)^6 ≤ (9769450247953/25000000000000 : ℝ)^5 := by
    have hnat : (4570269013 : ℕ)^6*25000000000000^5 ≤ 9769450247953^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570269013 10000000000 9769450247953 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688803727/1250000000 : ℝ)^6 ≤ (24456402579253/50000000000000 : ℝ)^5 := by
    have hnat : (688803727 : ℕ)^6*50000000000000^5 ≤ 24456402579253^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688803727 1250000000 24456402579253 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341951281/2000000000 : ℝ)^6 ≤ (6004696916589/50000000000000 : ℝ)^5 := by
    have hnat : (341951281 : ℕ)^6*50000000000000^5 ≤ 6004696916589^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341951281 2000000000 6004696916589 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4570269013/10000000000 : ℝ), (688803727/1250000000 : ℝ), (341951281/2000000000 : ℝ)] ![(9769450247953/25000000000000 : ℝ), (24456402579253/50000000000000 : ℝ), (6004696916589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4570269013/10000000000 : ℝ)|^6 ≤ (9769450247953/25000000000000 : ℝ)^5
        have hw : |(4570269013/10000000000 : ℝ)|=(4570269013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688803727/1250000000 : ℝ)|^6 ≤ (24456402579253/50000000000000 : ℝ)^5
        have hw : |(688803727/1250000000 : ℝ)|=(688803727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341951281/2000000000 : ℝ)|^6 ≤ (6004696916589/50000000000000 : ℝ)^5
        have hw : |(341951281/2000000000 : ℝ)|=(341951281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330060_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (6930916579/10000000000 : ℝ)*x 0 + (226138371/625000000 : ℝ)*x 1 + (-193530393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6930916579/10000000000 : ℝ)^6 ≤ (32204666814007/50000000000000 : ℝ)^5 := by
    have hnat : (6930916579 : ℕ)^6*50000000000000^5 ≤ 32204666814007^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6930916579 10000000000 32204666814007 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226138371/625000000 : ℝ)^6 ≤ (29525216472061/100000000000000 : ℝ)^5 := by
    have hnat : (226138371 : ℕ)^6*100000000000000^5 ≤ 29525216472061^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226138371 625000000 29525216472061 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193530393/2000000000 : ℝ)^6 ≤ (151636247357/2500000000000 : ℝ)^5 := by
    have hnat : (193530393 : ℕ)^6*2500000000000^5 ≤ 151636247357^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193530393 2000000000 151636247357 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6930916579/10000000000 : ℝ), (226138371/625000000 : ℝ), (-193530393/2000000000 : ℝ)] ![(32204666814007/50000000000000 : ℝ), (29525216472061/100000000000000 : ℝ), (151636247357/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6930916579/10000000000 : ℝ)|^6 ≤ (32204666814007/50000000000000 : ℝ)^5
        have hw : |(6930916579/10000000000 : ℝ)|=(6930916579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226138371/625000000 : ℝ)|^6 ≤ (29525216472061/100000000000000 : ℝ)^5
        have hw : |(226138371/625000000 : ℝ)|=(226138371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193530393/2000000000 : ℝ)|^6 ≤ (151636247357/2500000000000 : ℝ)^5
        have hw : |(-193530393/2000000000 : ℝ)|=(193530393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330060 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-608749009/5000000000 : ℝ)*X 0 0+(179208379/400000000 : ℝ)*X 0 1+(-2985286187/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2240105053/5000000000 : ℝ)*X 1 0+(-608748759/5000000000 : ℝ)*X 1 1+(-5970572143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-376352399/2000000000 : ℝ)*X 0 0+(1531793279/10000000000 : ℝ)*X 0 1+(-1591158553/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2579084807/10000000000 : ℝ)*X 1 0+(-3654139/50000000 : ℝ)*X 1 1+(-1988948589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2340344331/10000000000 : ℝ)*X 2 0+(1951023791/2500000000 : ℝ)*X 2 1+(623967049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((859663899/2000000000 : ℝ)*X 0 0+(6866496087/10000000000 : ℝ)*X 0 1+(-3423/15625000 : ℝ)*X 0 2+(859663899/2000000000 : ℝ)*X 1 0+(6866496087/10000000000 : ℝ)*X 1 1+(-3423/15625000 : ℝ)*X 1 2+(859663899/2000000000 : ℝ)*X 2 0+(6866496087/10000000000 : ℝ)*X 2 1+(-3423/15625000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-241034981/2500000000 : ℝ)*X 0 0+(223173371/1000000000 : ℝ)*X 0 1+(-8080001153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((532283731/5000000000 : ℝ)*X 1 0+(-2145631833/10000000000 : ℝ)*X 1 1+(-4039999233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((810987153/1250000000 : ℝ)*X 2 0+(3775706067/10000000000 : ℝ)*X 2 1+(139710839/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8345133171/10000000000 : ℝ)*X 0 0+(160112837/625000000 : ℝ)*X 0 1+(-559067/2500000000 : ℝ)*X 0 2+(8345133171/10000000000 : ℝ)*X 1 0+(160112837/625000000 : ℝ)*X 1 1+(-559067/2500000000 : ℝ)*X 1 2+(8345133171/10000000000 : ℝ)*X 2 0+(160112837/625000000 : ℝ)*X 2 1+(-559067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-93858193/2500000000 : ℝ)*X 0 0+(769357429/1250000000 : ℝ)*X 0 1+(-4872375473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3318876401/5000000000 : ℝ)*X 1 0+(-858326133/10000000000 : ℝ)*X 1 1+(-12590991/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((37188011/250000000 : ℝ)*X 2 0+(60795109/78125000 : ℝ)*X 2 1+(17216401/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((285612993/312500000 : ℝ)*X 0 0+(1477501279/10000000000 : ℝ)*X 0 1+(-45388039/10000000000 : ℝ)*X 0 2+(285612993/312500000 : ℝ)*X 1 0+(1477501279/10000000000 : ℝ)*X 1 1+(-45388039/10000000000 : ℝ)*X 1 2+(285612993/312500000 : ℝ)*X 2 0+(1477501279/10000000000 : ℝ)*X 2 1+(-45388039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((29307/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29307/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84118187287157055468237/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192059765403/1000000000000 : ℝ)*(base5) + (1239434145573/1000000000000 : ℝ)*(base7) + (271557/200000000000 : ℝ)*(base59) + (1627541530681/1000000000000 : ℝ)*(major_s0_0) + (1627541530681/1000000000000 : ℝ)*(major_s0_1) + (1627541530681/1000000000000 : ℝ)*(major_s0_2) + (9314579/1000000000000 : ℝ)*(sp_s0_0) + (2224613/250000000000 : ℝ)*(sp_s0_1) + (941354211597/500000000000 : ℝ)*(sp_s0_7) + (1882739606159/1000000000000 : ℝ)*(sp_s0_8) + (1037411663/500000000 : ℝ)*(sp_s0_9) + (1761982543699/1000000000000 : ℝ)*(sp_s0_13) + (5727853/125000000000 : ℝ)*(sp_s0_14) + (3011197/200000000000 : ℝ)*(sp_s0_15) + (89326020441/125000000000 : ℝ)*(f.failure) + (1882763560597/1000000000000 : ℝ)*(f.sum) + (280236048860281/5000000000000000000000000000 : ℝ)*base63 + (4247531788656079/10000000000000000000000000000 : ℝ)*base64 + (276798907343921/10000000000000000000000000000 : ℝ)*base66 + (2388866837360281/10000000000000000000000000000 : ℝ)*base69 + (2638665809647899/5000000000000000000000000000 : ℝ)*base70 + (7700566685343921/10000000000000000000000000000 : ℝ)*base72 + (117996867639719/10000000000000000000000000000 : ℝ)*base74 + (837448675639719/10000000000000000000000000000 : ℝ)*base76 + (117857575343921/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (13427/12500000000000000 : ℝ)*base86 + (13427/12500000000000000 : ℝ)*base88 + (13427/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58533/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8488312114729296597663/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61629273203/50000000000 : ℝ)*(base7) + (244911/1000000000000 : ℝ)*(base12) + (238733/1000000000000 : ℝ)*(base39) + (358621/500000000000 : ℝ)*(base53) + (42468924243/1000000000000 : ℝ)*(base60) + (62005440137/40000000000 : ℝ)*(major_s0_0) + (62005440137/40000000000 : ℝ)*(major_s0_1) + (1550135286183/1000000000000 : ℝ)*(major_s0_2) + (113801/5000000000 : ℝ)*(sp_s0_7) + (220694265521/125000000000 : ℝ)*(sp_s0_14) + (1765577129279/1000000000000 : ℝ)*(sp_s0_15) + (1765577846521/1000000000000 : ℝ)*(sp_s0_16) + (956600289361/500000000000 : ℝ)*(sp_s0_20) + (321869/50000000000 : ℝ)*(sp_s0_27) + (680621552043/1000000000000 : ℝ)*(f.failure) + (1765577846521/1000000000000 : ℝ)*(f.sum) + (1283071585622801/1250000000000000000000000000 : ℝ)*base63 + (1204546584668497/10000000000000000000000000000 : ℝ)*base64 + (169910132432383/400000000000000000000000000 : ℝ)*base67 + (4810038888998983/10000000000000000000000000000 : ℝ)*base69 + (268570160519683/625000000000000000000000000 : ℝ)*base71 + (296652824832383/400000000000000000000000000 : ℝ)*base73 + (97035184799337/400000000000000000000000000 : ℝ)*base75 + (151003571400663/400000000000000000000000000 : ℝ)*base76 + (47437414152383/200000000000000000000000000 : ℝ)*base79 + (50621/100000000000000000 : ℝ)*base86 + (50621/100000000000000000 : ℝ)*base88 + (50621/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9549/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9549/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14896609305708113271009/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912637003011/1000000000000 : ℝ)*(base7) + (163727157449/1000000000000 : ℝ)*(base39) + (3879243/500000000000 : ℝ)*(base43) + (104007/50000000000 : ℝ)*(base50) + (777089676163/500000000000 : ℝ)*(major_s0_0) + (19427144923/12500000000 : ℝ)*(major_s0_1) + (777089676163/500000000000 : ℝ)*(major_s0_2) + (2139053/250000000000 : ℝ)*(sp_s0_0) + (34662941/500000000000 : ℝ)*(sp_s0_9) + (2811801/1000000000000 : ℝ)*(sp_s0_20) + (970825358961/500000000000 : ℝ)*(sp_s0_21) + (1941667032619/1000000000000 : ℝ)*(sp_s0_22) + (1941589948251/1000000000000 : ℝ)*(sp_s0_23) + (1595031065159/1000000000000 : ℝ)*(sp_s0_27) + (13647937479/20000000000 : ℝ)*(f.failure) + (1941667032619/1000000000000 : ℝ)*(f.sum) + (782576383274117/5000000000000000000000000000 : ℝ)*base62 + (2607679139299317/5000000000000000000000000000 : ℝ)*base64 + (119282030307657/125000000000000000000000000 : ℝ)*base67 + (367044620056963/5000000000000000000000000000 : ℝ)*base69 + (74034978621177/2500000000000000000000000000 : ℝ)*base70 + (816004535299317/5000000000000000000000000000 : ℝ)*base73 + (55009284770777/125000000000000000000000000 : ℝ)*base74 + (184287540056963/5000000000000000000000000000 : ℝ)*base77 + (1728491070605597/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (2687/2000000000000000 : ℝ)*base87 + (2687/2000000000000000 : ℝ)*base89 + (2687/2000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (29307/50000 : ℝ) ^ (95/16 : ℝ) ≤ (2096418962186151763/50000000000000000000 : ℝ) := by
    have hpowers : (29307/50000 : ℝ)^95 ≤ (2096418962186151763/50000000000000000000 : ℝ)^16 := by
      have hnat : (29307 : ℕ)^95*50000000000000000000^16 ≤ 2096418962186151763^16*50000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29307 50000 2096418962186151763 50000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29307/50000 : ℝ)) (X := (2096418962186151763/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (52096418962186151763/50000000000000000000 : ℝ) ≤ (10069415745759839/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (52096418962186151763/50000000000000000000 : ℝ)^16 ≤ (10069415745759839/10000000000000000 : ℝ)^95 := by
      have hnat : (52096418962186151763 : ℕ)^16*10000000000000000^95 ≤ 10069415745759839^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52096418962186151763 50000000000000000000 10069415745759839 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10069415745759839/10000000000000000 : ℝ)) (X := (52096418962186151763/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (27096418962186151763/25000000000000000000 : ℝ) ≤ (316767067584489/312500000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (27096418962186151763/25000000000000000000 : ℝ)^16 ≤ (316767067584489/312500000000000 : ℝ)^95 := by
      have hnat : (27096418962186151763 : ℕ)^16*312500000000000^95 ≤ 316767067584489^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27096418962186151763 25000000000000000000 316767067584489 312500000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (316767067584489/312500000000000 : ℝ)) (X := (27096418962186151763/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(69415745759839/5861400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(67130416943809/5861400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (29307/50000 : ℝ)) (alpha := (69415745759839/5861400000000000 : ℝ)) (beta := (67130416943809/5861400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29307/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(69415745759839/5861400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(67130416943809/5861400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (58533/100000 : ℝ) ^ (95/16 : ℝ) ≤ (4158552157409609667/100000000000000000000 : ℝ) := by
    have hpowers : (58533/100000 : ℝ)^95 ≤ (4158552157409609667/100000000000000000000 : ℝ)^16 := by
      have hnat : (58533 : ℕ)^95*100000000000000000000^16 ≤ 4158552157409609667^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58533 100000 4158552157409609667 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58533/100000 : ℝ)) (X := (4158552157409609667/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (104158552157409609667/100000000000000000000 : ℝ) ≤ (10068857614843949/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (104158552157409609667/100000000000000000000 : ℝ)^16 ≤ (10068857614843949/10000000000000000 : ℝ)^95 := by
      have hnat : (104158552157409609667 : ℕ)^16*10000000000000000^95 ≤ 10068857614843949^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104158552157409609667 100000000000000000000 10068857614843949 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10068857614843949/10000000000000000 : ℝ)) (X := (104158552157409609667/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (54158552157409609667/50000000000000000000 : ℝ) ≤ (5067732896214307/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (54158552157409609667/50000000000000000000 : ℝ)^16 ≤ (5067732896214307/5000000000000000 : ℝ)^95 := by
      have hnat : (54158552157409609667 : ℕ)^16*5000000000000000^95 ≤ 5067732896214307^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54158552157409609667 50000000000000000000 5067732896214307 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5067732896214307/5000000000000000 : ℝ)) (X := (54158552157409609667/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(68857614843949/5853300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(4440545172311/390220000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (58533/100000 : ℝ)) (alpha := (68857614843949/5853300000000000 : ℝ)) (beta := (4440545172311/390220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (58533/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(68857614843949/5853300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(4440545172311/390220000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9549/20000 : ℝ) ^ (95/16 : ℝ) ≤ (1240607471786946789/100000000000000000000 : ℝ) := by
    have hpowers : (9549/20000 : ℝ)^95 ≤ (1240607471786946789/100000000000000000000 : ℝ)^16 := by
      have hnat : (9549 : ℕ)^95*100000000000000000000^16 ≤ 1240607471786946789^16*20000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9549 20000 1240607471786946789 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9549/20000 : ℝ)) (X := (1240607471786946789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101240607471786946789/100000000000000000000 : ℝ) ≤ (10020787470762693/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (101240607471786946789/100000000000000000000 : ℝ)^16 ≤ (10020787470762693/10000000000000000 : ℝ)^95 := by
      have hnat : (101240607471786946789 : ℕ)^16*10000000000000000^95 ≤ 10020787470762693^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101240607471786946789 100000000000000000000 10020787470762693 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020787470762693/10000000000000000 : ℝ)) (X := (101240607471786946789/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51240607471786946789/50000000000000000000 : ℝ) ≤ (10041364181034477/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (51240607471786946789/50000000000000000000 : ℝ)^16 ≤ (10041364181034477/10000000000000000 : ℝ)^95 := by
      have hnat : (51240607471786946789 : ℕ)^16*10000000000000000^95 ≤ 10041364181034477^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51240607471786946789 50000000000000000000 10041364181034477 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041364181034477/10000000000000000 : ℝ)) (X := (51240607471786946789/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(20787470762693/4774500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(857362927991/198937500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (9549/20000 : ℝ)) (alpha := (20787470762693/4774500000000000 : ℝ)) (beta := (857362927991/198937500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9549/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(20787470762693/4774500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(857362927991/198937500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-232729467/1250000000 : ℝ)*X 0 0+(1899611043/5000000000 : ℝ)*X 0 1+(-611224127/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2261199167/5000000000 : ℝ)*X 1 0+(-2584501159/10000000000 : ℝ)*X 1 1+(-602998699/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4570269013/10000000000 : ℝ)*X 2 0+(688803727/1250000000 : ℝ)*X 2 1+(341951281/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6930916579/10000000000 : ℝ)*X 0 0+(226138371/625000000 : ℝ)*X 0 1+(-193530393/2000000000 : ℝ)*X 0 2+(6930916579/10000000000 : ℝ)*X 1 0+(226138371/625000000 : ℝ)*X 1 1+(-193530393/2000000000 : ℝ)*X 1 2+(6930916579/10000000000 : ℝ)*X 2 0+(226138371/625000000 : ℝ)*X 2 1+(-193530393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330060_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-2063558710641531823782576397/195110000000000000000000000 : ℝ) := by norm_num
    linear_combination (3561/15625000000 : ℝ)*(base11) + (364489/1000000000000 : ℝ)*(base12) + (4237/500000000000 : ℝ)*(base25) + (113500292321/250000000000 : ℝ)*(base39) + (76157/1000000000000 : ℝ)*(base40) + (6819/100000000000 : ℝ)*(base43) + (4797/500000000000 : ℝ)*(base53) + (70811467131/125000000000 : ℝ)*(base59) + (227753/100000 : ℝ)*(major_s1_0) + (227752993181/100000000000 : ℝ)*(major_s1_1) + (1138764995203/500000000000 : ℝ)*(major_s1_2) + (70509227901/20000000000 : ℝ)*(sp_s1_0) + (3525462055633/1000000000000 : ℝ)*(sp_s1_1) + (1762730994281/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1762731032613/500000000000 : ℝ)*(f.sum) + (442750562682608393/5822204343750000000000000000000 : ℝ)*base63 + (77723891790029/198937500000000000000000000 : ℝ)*base65 + (39148179830991/39022000000000000000000000 : ℝ)*base67 + (496096297755271/2387250000000000000000000000 : ℝ)*base68 + (284946919412565071/7773681750000000000000000000000 : ℝ)*base70 + (28004309895869/36633750000000000000000000 : ℝ)*base73 + (68571883743671/585330000000000000000000000 : ℝ)*base75 + (1261444412641/18316875000000000000000000 : ℝ)*base77 + (130393882044798257/1143617754000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b031 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 61)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=60 := by omega
  rcases hc with rfl
  · exact collision_c330060 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 60 ≤ c.val) (hhi : c.val < 61)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
