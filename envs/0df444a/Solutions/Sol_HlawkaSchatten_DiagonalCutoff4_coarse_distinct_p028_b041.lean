-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b041
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:07.46541+00:00
-- url     : https://prove2.me/submissions/4fc80375-f2d7-461a-bd09-8ab77121ea48

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
theorem collision_support_c328085_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052046023/10000000000 : ℝ)*x 0 + (-6738098257/10000000000 : ℝ)*x 1 + (595747133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052046023/10000000000 : ℝ)^93 ≤ (14766070416271/100000000000000 : ℝ)^77 := by
    have hnat : (2052046023 : ℕ)^93*100000000000000^77 ≤ 14766070416271^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052046023 10000000000 14766070416271 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6738098257/10000000000 : ℝ)^93 ≤ (31036928755243/50000000000000 : ℝ)^77 := by
    have hnat : (6738098257 : ℕ)^93*50000000000000^77 ≤ 31036928755243^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6738098257 10000000000 31036928755243 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595747133/2000000000 : ℝ)^93 ≤ (23160072053331/100000000000000 : ℝ)^77 := by
    have hnat : (595747133 : ℕ)^93*100000000000000^77 ≤ 23160072053331^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595747133 2000000000 23160072053331 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052046023/10000000000 : ℝ), (-6738098257/10000000000 : ℝ), (595747133/2000000000 : ℝ)] ![(14766070416271/100000000000000 : ℝ), (31036928755243/50000000000000 : ℝ), (23160072053331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052046023/10000000000 : ℝ)|^93 ≤ (14766070416271/100000000000000 : ℝ)^77
        have hw : |(-2052046023/10000000000 : ℝ)|=(2052046023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6738098257/10000000000 : ℝ)|^93 ≤ (31036928755243/50000000000000 : ℝ)^77
        have hw : |(-6738098257/10000000000 : ℝ)|=(6738098257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(595747133/2000000000 : ℝ)|^93 ≤ (23160072053331/100000000000000 : ℝ)^77
        have hw : |(595747133/2000000000 : ℝ)|=(595747133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328085_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5492847539/10000000000 : ℝ)*x 0 + (79877143/312500000 : ℝ)*x 1 + (979533393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492847539/10000000000 : ℝ)^93 ≤ (12124658377197/25000000000000 : ℝ)^77 := by
    have hnat : (5492847539 : ℕ)^93*25000000000000^77 ≤ 12124658377197^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492847539 10000000000 12124658377197 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79877143/312500000 : ℝ)^93 ≤ (1925177083013/10000000000000 : ℝ)^77 := by
    have hnat : (79877143 : ℕ)^93*10000000000000^77 ≤ 1925177083013^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79877143 312500000 1925177083013 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979533393/2500000000 : ℝ)^93 ≤ (32249595641871/100000000000000 : ℝ)^77 := by
    have hnat : (979533393 : ℕ)^93*100000000000000^77 ≤ 32249595641871^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979533393 2500000000 32249595641871 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492847539/10000000000 : ℝ), (79877143/312500000 : ℝ), (979533393/2500000000 : ℝ)] ![(12124658377197/25000000000000 : ℝ), (1925177083013/10000000000000 : ℝ), (32249595641871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492847539/10000000000 : ℝ)|^93 ≤ (12124658377197/25000000000000 : ℝ)^77
        have hw : |(5492847539/10000000000 : ℝ)|=(5492847539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79877143/312500000 : ℝ)|^93 ≤ (1925177083013/10000000000000 : ℝ)^77
        have hw : |(79877143/312500000 : ℝ)|=(79877143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(979533393/2500000000 : ℝ)|^93 ≤ (32249595641871/100000000000000 : ℝ)^77
        have hw : |(979533393/2500000000 : ℝ)|=(979533393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328085_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3653716127/10000000000 : ℝ)*x 0 + (-1589358287/5000000000 : ℝ)*x 1 + (-519204209/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3653716127/10000000000 : ℝ)^93 ≤ (14819873806937/50000000000000 : ℝ)^77 := by
    have hnat : (3653716127 : ℕ)^93*50000000000000^77 ≤ 14819873806937^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3653716127 10000000000 14819873806937 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1589358287/5000000000 : ℝ)^93 ≤ (25050915975371/100000000000000 : ℝ)^77 := by
    have hnat : (1589358287 : ℕ)^93*100000000000000^77 ≤ 25050915975371^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589358287 5000000000 25050915975371 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519204209/1000000000 : ℝ)^93 ≤ (45309336395191/100000000000000 : ℝ)^77 := by
    have hnat : (519204209 : ℕ)^93*100000000000000^77 ≤ 45309336395191^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519204209 1000000000 45309336395191 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3653716127/10000000000 : ℝ), (-1589358287/5000000000 : ℝ), (-519204209/1000000000 : ℝ)] ![(14819873806937/50000000000000 : ℝ), (25050915975371/100000000000000 : ℝ), (45309336395191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3653716127/10000000000 : ℝ)|^93 ≤ (14819873806937/50000000000000 : ℝ)^77
        have hw : |(3653716127/10000000000 : ℝ)|=(3653716127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1589358287/5000000000 : ℝ)|^93 ≤ (25050915975371/100000000000000 : ℝ)^77
        have hw : |(-1589358287/5000000000 : ℝ)|=(1589358287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519204209/1000000000 : ℝ)|^93 ≤ (45309336395191/100000000000000 : ℝ)^77
        have hw : |(-519204209/1000000000 : ℝ)|=(519204209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328085_s0_4 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (293/10000000000 : ℝ)*x 0 + (-4999999993/5000000000 : ℝ)*x 1 + (-293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (293/10000000000 : ℝ)^93 ≤ (19929/25000000000000 : ℝ)^77 := by
    have hnat : (293 : ℕ)^93*25000000000000^77 ≤ 19929^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293 10000000000 19929 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999999993/5000000000 : ℝ)^93 ≤ (9999999983091/10000000000000 : ℝ)^77 := by
    have hnat : (4999999993 : ℕ)^93*10000000000000^77 ≤ 9999999983091^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999993 5000000000 9999999983091 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293/10000000000 : ℝ)^93 ≤ (19929/25000000000000 : ℝ)^77 := by
    have hnat : (293 : ℕ)^93*25000000000000^77 ≤ 19929^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293 10000000000 19929 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(293/10000000000 : ℝ), (-4999999993/5000000000 : ℝ), (-293/10000000000 : ℝ)] ![(19929/25000000000000 : ℝ), (9999999983091/10000000000000 : ℝ), (19929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(293/10000000000 : ℝ)|^93 ≤ (19929/25000000000000 : ℝ)^77
        have hw : |(293/10000000000 : ℝ)|=(293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4999999993/5000000000 : ℝ)|^93 ≤ (9999999983091/10000000000000 : ℝ)^77
        have hw : |(-4999999993/5000000000 : ℝ)|=(4999999993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293/10000000000 : ℝ)|^93 ≤ (19929/25000000000000 : ℝ)^77
        have hw : |(-293/10000000000 : ℝ)|=(293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328085_s0_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6787541837/10000000000 : ℝ)*x 0 + (-1867725147/10000000000 : ℝ)*x 1 + (3088645633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6787541837/10000000000 : ℝ)^93 ≤ (31312208251049/50000000000000 : ℝ)^77 := by
    have hnat : (6787541837 : ℕ)^93*50000000000000^77 ≤ 31312208251049^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6787541837 10000000000 31312208251049 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867725147/10000000000 : ℝ)^93 ≤ (6589727910009/50000000000000 : ℝ)^77 := by
    have hnat : (1867725147 : ℕ)^93*50000000000000^77 ≤ 6589727910009^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867725147 10000000000 6589727910009 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3088645633/10000000000 : ℝ)^93 ≤ (12098063830569/50000000000000 : ℝ)^77 := by
    have hnat : (3088645633 : ℕ)^93*50000000000000^77 ≤ 12098063830569^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088645633 10000000000 12098063830569 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6787541837/10000000000 : ℝ), (-1867725147/10000000000 : ℝ), (3088645633/10000000000 : ℝ)] ![(31312208251049/50000000000000 : ℝ), (6589727910009/50000000000000 : ℝ), (12098063830569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6787541837/10000000000 : ℝ)|^93 ≤ (31312208251049/50000000000000 : ℝ)^77
        have hw : |(6787541837/10000000000 : ℝ)|=(6787541837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1867725147/10000000000 : ℝ)|^93 ≤ (6589727910009/50000000000000 : ℝ)^77
        have hw : |(-1867725147/10000000000 : ℝ)|=(1867725147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3088645633/10000000000 : ℝ)|^93 ≤ (12098063830569/50000000000000 : ℝ)^77
        have hw : |(3088645633/10000000000 : ℝ)|=(3088645633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328085 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2052046023/10000000000 : ℝ)*X 0 0+(-6738098257/10000000000 : ℝ)*X 0 1+(595747133/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5492847539/10000000000 : ℝ)*X 1 0+(79877143/312500000 : ℝ)*X 1 1+(979533393/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3653716127/10000000000 : ℝ)*X 2 0+(-1589358287/5000000000 : ℝ)*X 2 1+(-519204209/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328085_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((293/10000000000 : ℝ)*X 0 0+(-4999999993/5000000000 : ℝ)*X 0 1+(-293/10000000000 : ℝ)*X 0 2+(293/10000000000 : ℝ)*X 2 0+(-4999999993/5000000000 : ℝ)*X 2 1+(-293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328085_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((6787541837/10000000000 : ℝ)*X 0 0+(-1867725147/10000000000 : ℝ)*X 0 1+(3088645633/10000000000 : ℝ)*X 0 2+(6787541837/10000000000 : ℝ)*X 1 0+(-1867725147/10000000000 : ℝ)*X 1 1+(3088645633/10000000000 : ℝ)*X 1 2+(6787541837/10000000000 : ℝ)*X 2 0+(-1867725147/10000000000 : ℝ)*X 2 1+(3088645633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328085_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-24823981124733111902961970197/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177037169863/500000000000 : ℝ)*(base3) + (65833/1000000000000 : ℝ)*(base22) + (26917/500000000000 : ℝ)*(base24) + (715776500173/1000000000000 : ℝ)*(base40) + (19289/1000000000000 : ℝ)*(base43) + (703105043419/1000000000000 : ℝ)*(base50) + (64769/1000000000000 : ℝ)*(base59) + (8679/4000 : ℝ)*(major_s0_0) + (1084875310479/500000000000 : ℝ)*(major_s0_1) + (8679/4000 : ℝ)*(major_s0_2) + (330986413067/100000000000 : ℝ)*(sp_s0_0) + (732787697937/200000000000 : ℝ)*(sp_s0_1) + (3309864011003/1000000000000 : ℝ)*(sp_s0_2) + (320123/500000000000 : ℝ)*(sp_s0_4) + (322962830137/500000000000 : ℝ)*(sp_s0_6) + (1654932074979/500000000000 : ℝ)*(f.sum) + (636414860557/100000000000000000000000000 : ℝ)*base62 + (173387119/2500000000000000000000 : ℝ)*base64 + (745327013295549/5000000000000000000000000000 : ℝ)*base66 + (3253081303/10000000000000000000000 : ℝ)*base68 + (1559867867/2500000000000000000000 : ℝ)*base71 + (2172675381/5000000000000000000000 : ℝ)*base72 + (23559495270557/100000000000000000000000000 : ℝ)*base74 + (162926097/5000000000000000000000 : ℝ)*base76 + (2690827353295549/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1/1000000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c328086_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5811836439/10000000000 : ℝ)*x 0 + (-632628367/2000000000 : ℝ)*x 1 + (-2980503499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5811836439/10000000000 : ℝ)^93 ≤ (51920580705551/100000000000000 : ℝ)^77 := by
    have hnat : (5811836439 : ℕ)^93*100000000000000^77 ≤ 51920580705551^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5811836439 10000000000 51920580705551 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (632628367/2000000000 : ℝ)^93 ≤ (24902744917981/100000000000000 : ℝ)^77 := by
    have hnat : (632628367 : ℕ)^93*100000000000000^77 ≤ 24902744917981^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632628367 2000000000 24902744917981 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980503499/10000000000 : ℝ)^93 ≤ (23176674359569/100000000000000 : ℝ)^77 := by
    have hnat : (2980503499 : ℕ)^93*100000000000000^77 ≤ 23176674359569^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980503499 10000000000 23176674359569 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5811836439/10000000000 : ℝ), (-632628367/2000000000 : ℝ), (-2980503499/10000000000 : ℝ)] ![(51920580705551/100000000000000 : ℝ), (24902744917981/100000000000000 : ℝ), (23176674359569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5811836439/10000000000 : ℝ)|^93 ≤ (51920580705551/100000000000000 : ℝ)^77
        have hw : |(5811836439/10000000000 : ℝ)|=(5811836439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-632628367/2000000000 : ℝ)|^93 ≤ (24902744917981/100000000000000 : ℝ)^77
        have hw : |(-632628367/2000000000 : ℝ)|=(632628367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2980503499/10000000000 : ℝ)|^93 ≤ (23176674359569/100000000000000 : ℝ)^77
        have hw : |(-2980503499/10000000000 : ℝ)|=(2980503499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191143/10000000000 : ℝ)*x 0 + (-8245690193/10000000000 : ℝ)*x 1 + (2722839221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191143/10000000000 : ℝ)^93 ≤ (1902219443/50000000000000 : ℝ)^77 := by
    have hnat : (2191143 : ℕ)^93*50000000000000^77 ≤ 1902219443^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191143 10000000000 1902219443 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8245690193/10000000000 : ℝ)^93 ≤ (79217227690747/100000000000000 : ℝ)^77 := by
    have hnat : (8245690193 : ℕ)^93*100000000000000^77 ≤ 79217227690747^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8245690193 10000000000 79217227690747 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722839221/10000000000 : ℝ)^93 ≤ (1298685491179/6250000000000 : ℝ)^77 := by
    have hnat : (2722839221 : ℕ)^93*6250000000000^77 ≤ 1298685491179^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722839221 10000000000 1298685491179 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191143/10000000000 : ℝ), (-8245690193/10000000000 : ℝ), (2722839221/10000000000 : ℝ)] ![(1902219443/50000000000000 : ℝ), (79217227690747/100000000000000 : ℝ), (1298685491179/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191143/10000000000 : ℝ)|^93 ≤ (1902219443/50000000000000 : ℝ)^77
        have hw : |(-2191143/10000000000 : ℝ)|=(2191143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8245690193/10000000000 : ℝ)|^93 ≤ (79217227690747/100000000000000 : ℝ)^77
        have hw : |(-8245690193/10000000000 : ℝ)|=(8245690193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722839221/10000000000 : ℝ)|^93 ≤ (1298685491179/6250000000000 : ℝ)^77
        have hw : |(2722839221/10000000000 : ℝ)|=(2722839221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5203951203/10000000000 : ℝ)*x 0 + (54897679/125000000 : ℝ)*x 1 + (2367434909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203951203/10000000000 : ℝ)^93 ≤ (45434888661909/100000000000000 : ℝ)^77 := by
    have hnat : (5203951203 : ℕ)^93*100000000000000^77 ≤ 45434888661909^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203951203 10000000000 45434888661909 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54897679/125000000 : ℝ)^93 ≤ (37015887970813/100000000000000 : ℝ)^77 := by
    have hnat : (54897679 : ℕ)^93*100000000000000^77 ≤ 37015887970813^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54897679 125000000 37015887970813 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2367434909/10000000000 : ℝ)^93 ≤ (2193652918129/12500000000000 : ℝ)^77 := by
    have hnat : (2367434909 : ℕ)^93*12500000000000^77 ≤ 2193652918129^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367434909 10000000000 2193652918129 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203951203/10000000000 : ℝ), (54897679/125000000 : ℝ), (2367434909/10000000000 : ℝ)] ![(45434888661909/100000000000000 : ℝ), (37015887970813/100000000000000 : ℝ), (2193652918129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203951203/10000000000 : ℝ)|^93 ≤ (45434888661909/100000000000000 : ℝ)^77
        have hw : |(5203951203/10000000000 : ℝ)|=(5203951203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54897679/125000000 : ℝ)|^93 ≤ (37015887970813/100000000000000 : ℝ)^77
        have hw : |(54897679/125000000 : ℝ)|=(54897679/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2367434909/10000000000 : ℝ)|^93 ≤ (2193652918129/12500000000000 : ℝ)^77
        have hw : |(2367434909/10000000000 : ℝ)|=(2367434909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2545442607/5000000000 : ℝ)*x 0 + (-2806272299/10000000000 : ℝ)*x 1 + (-1028439373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2545442607/5000000000 : ℝ)^93 ≤ (22122654804713/50000000000000 : ℝ)^77 := by
    have hnat : (2545442607 : ℕ)^93*50000000000000^77 ≤ 22122654804713^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545442607 5000000000 22122654804713 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2806272299/10000000000 : ℝ)^93 ≤ (21550407364471/100000000000000 : ℝ)^77 := by
    have hnat : (2806272299 : ℕ)^93*100000000000000^77 ≤ 21550407364471^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806272299 10000000000 21550407364471 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028439373/2500000000 : ℝ)^93 ≤ (8551070752483/25000000000000 : ℝ)^77 := by
    have hnat : (1028439373 : ℕ)^93*25000000000000^77 ≤ 8551070752483^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028439373 2500000000 8551070752483 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2545442607/5000000000 : ℝ), (-2806272299/10000000000 : ℝ), (-1028439373/2500000000 : ℝ)] ![(22122654804713/50000000000000 : ℝ), (21550407364471/100000000000000 : ℝ), (8551070752483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2545442607/5000000000 : ℝ)|^93 ≤ (22122654804713/50000000000000 : ℝ)^77
        have hw : |(2545442607/5000000000 : ℝ)|=(2545442607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2806272299/10000000000 : ℝ)|^93 ≤ (21550407364471/100000000000000 : ℝ)^77
        have hw : |(-2806272299/10000000000 : ℝ)|=(2806272299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028439373/2500000000 : ℝ)|^93 ≤ (8551070752483/25000000000000 : ℝ)^77
        have hw : |(-1028439373/2500000000 : ℝ)|=(1028439373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2408367161/10000000000 : ℝ)*x 0 + (-103484067/10000000000 : ℝ)*x 1 + (264301973/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2408367161/10000000000 : ℝ)^93 ≤ (8958174031547/50000000000000 : ℝ)^77 := by
    have hnat : (2408367161 : ℕ)^93*50000000000000^77 ≤ 8958174031547^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408367161 10000000000 8958174031547 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103484067/10000000000 : ℝ)^93 ≤ (40029454139/10000000000000 : ℝ)^77 := by
    have hnat : (103484067 : ℕ)^93*10000000000000^77 ≤ 40029454139^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103484067 10000000000 40029454139 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264301973/312500000 : ℝ)^93 ≤ (81683357385447/100000000000000 : ℝ)^77 := by
    have hnat : (264301973 : ℕ)^93*100000000000000^77 ≤ 81683357385447^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264301973 312500000 81683357385447 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2408367161/10000000000 : ℝ), (-103484067/10000000000 : ℝ), (264301973/312500000 : ℝ)] ![(8958174031547/50000000000000 : ℝ), (40029454139/10000000000000 : ℝ), (81683357385447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2408367161/10000000000 : ℝ)|^93 ≤ (8958174031547/50000000000000 : ℝ)^77
        have hw : |(2408367161/10000000000 : ℝ)|=(2408367161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103484067/10000000000 : ℝ)|^93 ≤ (40029454139/10000000000000 : ℝ)^77
        have hw : |(-103484067/10000000000 : ℝ)|=(103484067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264301973/312500000 : ℝ)|^93 ≤ (81683357385447/100000000000000 : ℝ)^77
        have hw : |(264301973/312500000 : ℝ)|=(264301973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-603677/5000000000 : ℝ)*x 0 + (-4230455051/10000000000 : ℝ)*x 1 + (6966004827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603677/5000000000 : ℝ)^93 ≤ (1852125417/100000000000000 : ℝ)^77 := by
    have hnat : (603677 : ℕ)^93*100000000000000^77 ≤ 1852125417^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603677 5000000000 1852125417 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230455051/10000000000 : ℝ)^93 ≤ (35379625582329/100000000000000 : ℝ)^77 := by
    have hnat : (4230455051 : ℕ)^93*100000000000000^77 ≤ 35379625582329^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230455051 10000000000 35379625582329 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6966004827/10000000000 : ℝ)^93 ≤ (32309261140021/50000000000000 : ℝ)^77 := by
    have hnat : (6966004827 : ℕ)^93*50000000000000^77 ≤ 32309261140021^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966004827 10000000000 32309261140021 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-603677/5000000000 : ℝ), (-4230455051/10000000000 : ℝ), (6966004827/10000000000 : ℝ)] ![(1852125417/100000000000000 : ℝ), (35379625582329/100000000000000 : ℝ), (32309261140021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-603677/5000000000 : ℝ)|^93 ≤ (1852125417/100000000000000 : ℝ)^77
        have hw : |(-603677/5000000000 : ℝ)|=(603677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4230455051/10000000000 : ℝ)|^93 ≤ (35379625582329/100000000000000 : ℝ)^77
        have hw : |(-4230455051/10000000000 : ℝ)|=(4230455051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6966004827/10000000000 : ℝ)|^93 ≤ (32309261140021/50000000000000 : ℝ)^77
        have hw : |(6966004827/10000000000 : ℝ)|=(6966004827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4155890659/5000000000 : ℝ)*x 0 + (463743997/2000000000 : ℝ)*x 1 + (266719987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155890659/5000000000 : ℝ)^93 ≤ (79984745993543/100000000000000 : ℝ)^77 := by
    have hnat : (4155890659 : ℕ)^93*100000000000000^77 ≤ 79984745993543^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155890659 5000000000 79984745993543 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463743997/2000000000 : ℝ)^93 ≤ (8557006334493/50000000000000 : ℝ)^77 := by
    have hnat : (463743997 : ℕ)^93*50000000000000^77 ≤ 8557006334493^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463743997 2000000000 8557006334493 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266719987/5000000000 : ℝ)^93 ≤ (1450620661339/50000000000000 : ℝ)^77 := by
    have hnat : (266719987 : ℕ)^93*50000000000000^77 ≤ 1450620661339^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266719987 5000000000 1450620661339 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155890659/5000000000 : ℝ), (463743997/2000000000 : ℝ), (266719987/5000000000 : ℝ)] ![(79984745993543/100000000000000 : ℝ), (8557006334493/50000000000000 : ℝ), (1450620661339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155890659/5000000000 : ℝ)|^93 ≤ (79984745993543/100000000000000 : ℝ)^77
        have hw : |(4155890659/5000000000 : ℝ)|=(4155890659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463743997/2000000000 : ℝ)|^93 ≤ (8557006334493/50000000000000 : ℝ)^77
        have hw : |(463743997/2000000000 : ℝ)|=(463743997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266719987/5000000000 : ℝ)|^93 ≤ (1450620661339/50000000000000 : ℝ)^77
        have hw : |(266719987/5000000000 : ℝ)|=(266719987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (936606037/1250000000 : ℝ)*x 0 + (-674563563/2500000000 : ℝ)*x 1 + (-1346982831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936606037/1250000000 : ℝ)^93 ≤ (14113331620627/20000000000000 : ℝ)^77 := by
    have hnat : (936606037 : ℕ)^93*20000000000000^77 ≤ 14113331620627^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936606037 1250000000 14113331620627 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674563563/2500000000 : ℝ)^93 ≤ (2569072359719/12500000000000 : ℝ)^77 := by
    have hnat : (674563563 : ℕ)^93*12500000000000^77 ≤ 2569072359719^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674563563 2500000000 2569072359719 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346982831/10000000000 : ℝ)^93 ≤ (277523843857/3125000000000 : ℝ)^77 := by
    have hnat : (1346982831 : ℕ)^93*3125000000000^77 ≤ 277523843857^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346982831 10000000000 277523843857 3125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(936606037/1250000000 : ℝ), (-674563563/2500000000 : ℝ), (-1346982831/10000000000 : ℝ)] ![(14113331620627/20000000000000 : ℝ), (2569072359719/12500000000000 : ℝ), (277523843857/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(936606037/1250000000 : ℝ)|^93 ≤ (14113331620627/20000000000000 : ℝ)^77
        have hw : |(936606037/1250000000 : ℝ)|=(936606037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674563563/2500000000 : ℝ)|^93 ≤ (2569072359719/12500000000000 : ℝ)^77
        have hw : |(-674563563/2500000000 : ℝ)|=(674563563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1346982831/10000000000 : ℝ)|^93 ≤ (277523843857/3125000000000 : ℝ)^77
        have hw : |(-1346982831/10000000000 : ℝ)|=(1346982831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (505658781/2500000000 : ℝ)*x 0 + (-649766953/5000000000 : ℝ)*x 1 + (8052827409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505658781/2500000000 : ℝ)^93 ≤ (7255421092903/50000000000000 : ℝ)^77 := by
    have hnat : (505658781 : ℕ)^93*50000000000000^77 ≤ 7255421092903^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505658781 2500000000 7255421092903 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649766953/5000000000 : ℝ)^93 ≤ (4252159937931/50000000000000 : ℝ)^77 := by
    have hnat : (649766953 : ℕ)^93*50000000000000^77 ≤ 4252159937931^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649766953 5000000000 4252159937931 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8052827409/10000000000 : ℝ)^93 ≤ (76984837927517/100000000000000 : ℝ)^77 := by
    have hnat : (8052827409 : ℕ)^93*100000000000000^77 ≤ 76984837927517^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8052827409 10000000000 76984837927517 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(505658781/2500000000 : ℝ), (-649766953/5000000000 : ℝ), (8052827409/10000000000 : ℝ)] ![(7255421092903/50000000000000 : ℝ), (4252159937931/50000000000000 : ℝ), (76984837927517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(505658781/2500000000 : ℝ)|^93 ≤ (7255421092903/50000000000000 : ℝ)^77
        have hw : |(505658781/2500000000 : ℝ)|=(505658781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649766953/5000000000 : ℝ)|^93 ≤ (4252159937931/50000000000000 : ℝ)^77
        have hw : |(-649766953/5000000000 : ℝ)|=(649766953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8052827409/10000000000 : ℝ)|^93 ≤ (76984837927517/100000000000000 : ℝ)^77
        have hw : |(8052827409/10000000000 : ℝ)|=(8052827409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (-8430402903/10000000000 : ℝ)*x 1 + (1244012841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^93 ≤ (0 : ℝ)^77 := by
    have hnat : (0 : ℕ)^93*1^77 ≤ 0^77*1^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8430402903/10000000000 : ℝ)^93 ≤ (40682740084203/50000000000000 : ℝ)^77 := by
    have hnat : (8430402903 : ℕ)^93*50000000000000^77 ≤ 40682740084203^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8430402903 10000000000 40682740084203 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244012841/5000000000 : ℝ)^93 ≤ (9317259910943/50000000000000 : ℝ)^77 := by
    have hnat : (1244012841 : ℕ)^93*50000000000000^77 ≤ 9317259910943^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244012841 5000000000 9317259910943 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (-8430402903/10000000000 : ℝ), (1244012841/5000000000 : ℝ)] ![(0 : ℝ), (40682740084203/50000000000000 : ℝ), (9317259910943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^93 ≤ (0 : ℝ)^77
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8430402903/10000000000 : ℝ)|^93 ≤ (40682740084203/50000000000000 : ℝ)^77
        have hw : |(-8430402903/10000000000 : ℝ)|=(8430402903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1244012841/5000000000 : ℝ)|^93 ≤ (9317259910943/50000000000000 : ℝ)^77
        have hw : |(1244012841/5000000000 : ℝ)|=(1244012841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8221623179/10000000000 : ℝ)*x 0 + (1717400641/10000000000 : ℝ)*x 1 + (1381045007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8221623179/10000000000 : ℝ)^93 ≤ (39469026758121/50000000000000 : ℝ)^77 := by
    have hnat : (8221623179 : ℕ)^93*50000000000000^77 ≤ 39469026758121^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8221623179 10000000000 39469026758121 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1717400641/10000000000 : ℝ)^93 ≤ (372163628347/3125000000000 : ℝ)^77 := by
    have hnat : (1717400641 : ℕ)^93*3125000000000^77 ≤ 372163628347^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717400641 10000000000 372163628347 3125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381045007/10000000000 : ℝ)^93 ≤ (2288177590221/25000000000000 : ℝ)^77 := by
    have hnat : (1381045007 : ℕ)^93*25000000000000^77 ≤ 2288177590221^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381045007 10000000000 2288177590221 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8221623179/10000000000 : ℝ), (1717400641/10000000000 : ℝ), (1381045007/10000000000 : ℝ)] ![(39469026758121/50000000000000 : ℝ), (372163628347/3125000000000 : ℝ), (2288177590221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8221623179/10000000000 : ℝ)|^93 ≤ (39469026758121/50000000000000 : ℝ)^77
        have hw : |(8221623179/10000000000 : ℝ)|=(8221623179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1717400641/10000000000 : ℝ)|^93 ≤ (372163628347/3125000000000 : ℝ)^77
        have hw : |(1717400641/10000000000 : ℝ)|=(1717400641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381045007/10000000000 : ℝ)|^93 ≤ (2288177590221/25000000000000 : ℝ)^77
        have hw : |(1381045007/10000000000 : ℝ)|=(1381045007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (528531747/2000000000 : ℝ)*x 0 + (-1386840429/2500000000 : ℝ)*x 1 + (-1889784343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528531747/2000000000 : ℝ)^93 ≤ (626319229273/3125000000000 : ℝ)^77 := by
    have hnat : (528531747 : ℕ)^93*3125000000000^77 ≤ 626319229273^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528531747 2000000000 626319229273 3125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1386840429/2500000000 : ℝ)^93 ≤ (49080575980727/100000000000000 : ℝ)^77 := by
    have hnat : (1386840429 : ℕ)^93*100000000000000^77 ≤ 49080575980727^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386840429 2500000000 49080575980727 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889784343/5000000000 : ℝ)^93 ≤ (6175441733457/20000000000000 : ℝ)^77 := by
    have hnat : (1889784343 : ℕ)^93*20000000000000^77 ≤ 6175441733457^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889784343 5000000000 6175441733457 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528531747/2000000000 : ℝ), (-1386840429/2500000000 : ℝ), (-1889784343/5000000000 : ℝ)] ![(626319229273/3125000000000 : ℝ), (49080575980727/100000000000000 : ℝ), (6175441733457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528531747/2000000000 : ℝ)|^93 ≤ (626319229273/3125000000000 : ℝ)^77
        have hw : |(528531747/2000000000 : ℝ)|=(528531747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1386840429/2500000000 : ℝ)|^93 ≤ (49080575980727/100000000000000 : ℝ)^77
        have hw : |(-1386840429/2500000000 : ℝ)|=(1386840429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889784343/5000000000 : ℝ)|^93 ≤ (6175441733457/20000000000000 : ℝ)^77
        have hw : |(-1889784343/5000000000 : ℝ)|=(1889784343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s0_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6776296061/10000000000 : ℝ)*x 0 + (-30992219/400000000 : ℝ)*x 1 + (398816363/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6776296061/10000000000 : ℝ)^93 ≤ (62499120265319/100000000000000 : ℝ)^77 := by
    have hnat : (6776296061 : ℕ)^93*100000000000000^77 ≤ 62499120265319^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6776296061 10000000000 62499120265319 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30992219/400000000 : ℝ)^93 ≤ (284613563549/6250000000000 : ℝ)^77 := by
    have hnat : (30992219 : ℕ)^93*6250000000000^77 ≤ 284613563549^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30992219 400000000 284613563549 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398816363/1000000000 : ℝ)^93 ≤ (32947062699031/100000000000000 : ℝ)^77 := by
    have hnat : (398816363 : ℕ)^93*100000000000000^77 ≤ 32947062699031^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398816363 1000000000 32947062699031 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6776296061/10000000000 : ℝ), (-30992219/400000000 : ℝ), (398816363/1000000000 : ℝ)] ![(62499120265319/100000000000000 : ℝ), (284613563549/6250000000000 : ℝ), (32947062699031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6776296061/10000000000 : ℝ)|^93 ≤ (62499120265319/100000000000000 : ℝ)^77
        have hw : |(6776296061/10000000000 : ℝ)|=(6776296061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30992219/400000000 : ℝ)|^93 ≤ (284613563549/6250000000000 : ℝ)^77
        have hw : |(-30992219/400000000 : ℝ)|=(30992219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398816363/1000000000 : ℝ)|^93 ≤ (32947062699031/100000000000000 : ℝ)^77
        have hw : |(398816363/1000000000 : ℝ)|=(398816363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-17252261/200000000 : ℝ)*x 0 + (-169827867/312500000 : ℝ)*x 1 + (2673080663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17252261/200000000 : ℝ)^93 ≤ (1296065334673/25000000000000 : ℝ)^77 := by
    have hnat : (17252261 : ℕ)^93*25000000000000^77 ≤ 1296065334673^77*200000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17252261 200000000 1296065334673 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169827867/312500000 : ℝ)^93 ≤ (23938505176287/50000000000000 : ℝ)^77 := by
    have hnat : (169827867 : ℕ)^93*50000000000000^77 ≤ 23938505176287^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169827867 312500000 23938505176287 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2673080663/5000000000 : ℝ)^93 ≤ (733417629563/1562500000000 : ℝ)^77 := by
    have hnat : (2673080663 : ℕ)^93*1562500000000^77 ≤ 733417629563^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673080663 5000000000 733417629563 1562500000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17252261/200000000 : ℝ), (-169827867/312500000 : ℝ), (2673080663/5000000000 : ℝ)] ![(1296065334673/25000000000000 : ℝ), (23938505176287/50000000000000 : ℝ), (733417629563/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17252261/200000000 : ℝ)|^93 ≤ (1296065334673/25000000000000 : ℝ)^77
        have hw : |(-17252261/200000000 : ℝ)|=(17252261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169827867/312500000 : ℝ)|^93 ≤ (23938505176287/50000000000000 : ℝ)^77
        have hw : |(-169827867/312500000 : ℝ)|=(169827867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2673080663/5000000000 : ℝ)|^93 ≤ (733417629563/1562500000000 : ℝ)^77
        have hw : |(2673080663/5000000000 : ℝ)|=(2673080663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1393915461/2500000000 : ℝ)*x 0 + (3268992857/10000000000 : ℝ)*x 1 + (3142239739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1393915461/2500000000 : ℝ)^93 ≤ (49383151375221/100000000000000 : ℝ)^77 := by
    have hnat : (1393915461 : ℕ)^93*100000000000000^77 ≤ 49383151375221^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393915461 2500000000 49383151375221 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3268992857/10000000000 : ℝ)^93 ≤ (6478179648101/25000000000000 : ℝ)^77 := by
    have hnat : (3268992857 : ℕ)^93*25000000000000^77 ≤ 6478179648101^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3268992857 10000000000 6478179648101 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3142239739/10000000000 : ℝ)^93 ≤ (4940826003487/20000000000000 : ℝ)^77 := by
    have hnat : (3142239739 : ℕ)^93*20000000000000^77 ≤ 4940826003487^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142239739 10000000000 4940826003487 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1393915461/2500000000 : ℝ), (3268992857/10000000000 : ℝ), (3142239739/10000000000 : ℝ)] ![(49383151375221/100000000000000 : ℝ), (6478179648101/25000000000000 : ℝ), (4940826003487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1393915461/2500000000 : ℝ)|^93 ≤ (49383151375221/100000000000000 : ℝ)^77
        have hw : |(1393915461/2500000000 : ℝ)|=(1393915461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3268992857/10000000000 : ℝ)|^93 ≤ (6478179648101/25000000000000 : ℝ)^77
        have hw : |(3268992857/10000000000 : ℝ)|=(3268992857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3142239739/10000000000 : ℝ)|^93 ≤ (4940826003487/20000000000000 : ℝ)^77
        have hw : |(3142239739/10000000000 : ℝ)|=(3142239739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (66219559/125000000 : ℝ)*x 0 + (-3429438509/10000000000 : ℝ)*x 1 + (-3290583187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66219559/125000000 : ℝ)^93 ≤ (2321194189229/5000000000000 : ℝ)^77 := by
    have hnat : (66219559 : ℕ)^93*5000000000000^77 ≤ 2321194189229^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66219559 125000000 2321194189229 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3429438509/10000000000 : ℝ)^93 ≤ (27456551236943/100000000000000 : ℝ)^77 := by
    have hnat : (3429438509 : ℕ)^93*100000000000000^77 ≤ 27456551236943^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3429438509 10000000000 27456551236943 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3290583187/10000000000 : ℝ)^93 ≤ (2611956496037/10000000000000 : ℝ)^77 := by
    have hnat : (3290583187 : ℕ)^93*10000000000000^77 ≤ 2611956496037^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3290583187 10000000000 2611956496037 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66219559/125000000 : ℝ), (-3429438509/10000000000 : ℝ), (-3290583187/10000000000 : ℝ)] ![(2321194189229/5000000000000 : ℝ), (27456551236943/100000000000000 : ℝ), (2611956496037/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66219559/125000000 : ℝ)|^93 ≤ (2321194189229/5000000000000 : ℝ)^77
        have hw : |(66219559/125000000 : ℝ)|=(66219559/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3429438509/10000000000 : ℝ)|^93 ≤ (27456551236943/100000000000000 : ℝ)^77
        have hw : |(-3429438509/10000000000 : ℝ)|=(3429438509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3290583187/10000000000 : ℝ)|^93 ≤ (2611956496037/10000000000000 : ℝ)^77
        have hw : |(-3290583187/10000000000 : ℝ)|=(3290583187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s1_3 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999997/10000000000 : ℝ)*x 0 + (1/156250000 : ℝ)*x 1 + (1/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999997/10000000000 : ℝ)^93 ≤ (99999999963767/100000000000000 : ℝ)^77 := by
    have hnat : (9999999997 : ℕ)^93*100000000000000^77 ≤ 99999999963767^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999997 10000000000 99999999963767 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1/156250000 : ℝ)^93 ≤ (6347/50000000000000 : ℝ)^77 := by
    have hnat : (1 : ℕ)^93*50000000000000^77 ≤ 6347^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 156250000 6347 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/156250000 : ℝ)^93 ≤ (6347/50000000000000 : ℝ)^77 := by
    have hnat : (1 : ℕ)^93*50000000000000^77 ≤ 6347^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 156250000 6347 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999997/10000000000 : ℝ), (1/156250000 : ℝ), (1/156250000 : ℝ)] ![(99999999963767/100000000000000 : ℝ), (6347/50000000000000 : ℝ), (6347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999997/10000000000 : ℝ)|^93 ≤ (99999999963767/100000000000000 : ℝ)^77
        have hw : |(9999999997/10000000000 : ℝ)|=(9999999997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1/156250000 : ℝ)|^93 ≤ (6347/50000000000000 : ℝ)^77
        have hw : |(1/156250000 : ℝ)|=(1/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1/156250000 : ℝ)|^93 ≤ (6347/50000000000000 : ℝ)^77
        have hw : |(1/156250000 : ℝ)|=(1/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328086_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2251935031/5000000000 : ℝ)*x 0 + (-637594207/2000000000 : ℝ)*x 1 + (4360896203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251935031/5000000000 : ℝ)^93 ≤ (38159589308779/100000000000000 : ℝ)^77 := by
    have hnat : (2251935031 : ℕ)^93*100000000000000^77 ≤ 38159589308779^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251935031 5000000000 38159589308779 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (637594207/2000000000 : ℝ)^93 ≤ (25139030276731/100000000000000 : ℝ)^77 := by
    have hnat : (637594207 : ℕ)^93*100000000000000^77 ≤ 25139030276731^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637594207 2000000000 25139030276731 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4360896203/10000000000 : ℝ)^93 ≤ (18350690201707/50000000000000 : ℝ)^77 := by
    have hnat : (4360896203 : ℕ)^93*50000000000000^77 ≤ 18350690201707^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360896203 10000000000 18350690201707 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251935031/5000000000 : ℝ), (-637594207/2000000000 : ℝ), (4360896203/10000000000 : ℝ)] ![(38159589308779/100000000000000 : ℝ), (25139030276731/100000000000000 : ℝ), (18350690201707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251935031/5000000000 : ℝ)|^93 ≤ (38159589308779/100000000000000 : ℝ)^77
        have hw : |(2251935031/5000000000 : ℝ)|=(2251935031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-637594207/2000000000 : ℝ)|^93 ≤ (25139030276731/100000000000000 : ℝ)^77
        have hw : |(-637594207/2000000000 : ℝ)|=(637594207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4360896203/10000000000 : ℝ)|^93 ≤ (18350690201707/50000000000000 : ℝ)^77
        have hw : |(4360896203/10000000000 : ℝ)|=(4360896203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328086 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (91/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^91 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^91*1^16 ≤ 1^16*1^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11296095383713331/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11296095383713331/10000000000000000 : ℝ)^91 := by
      have hnat : (2 : ℕ)^16*10000000000000000^91 ≤ 11296095383713331^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11296095383713331 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11296095383713331/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12130800245449181/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12130800245449181/10000000000000000 : ℝ)^91 := by
      have hnat : (3 : ℕ)^16*10000000000000000^91 ≤ 12130800245449181^91*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12130800245449181 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12130800245449181/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_2 : ((5811836439/10000000000 : ℝ)*X 2 0+(-632628367/2000000000 : ℝ)*X 2 1+(-2980503499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2191143/10000000000 : ℝ)*X 0 0+(-8245690193/10000000000 : ℝ)*X 0 1+(2722839221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5203951203/10000000000 : ℝ)*X 1 0+(54897679/125000000 : ℝ)*X 1 1+(2367434909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2545442607/5000000000 : ℝ)*X 2 0+(-2806272299/10000000000 : ℝ)*X 2 1+(-1028439373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2408367161/10000000000 : ℝ)*X 0 0+(-103484067/10000000000 : ℝ)*X 0 1+(264301973/312500000 : ℝ)*X 0 2+(2408367161/10000000000 : ℝ)*X 1 0+(-103484067/10000000000 : ℝ)*X 1 1+(264301973/312500000 : ℝ)*X 1 2+(2408367161/10000000000 : ℝ)*X 2 0+(-103484067/10000000000 : ℝ)*X 2 1+(264301973/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-603677/5000000000 : ℝ)*X 0 0+(-4230455051/10000000000 : ℝ)*X 0 1+(6966004827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4155890659/5000000000 : ℝ)*X 1 0+(463743997/2000000000 : ℝ)*X 1 1+(266719987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((936606037/1250000000 : ℝ)*X 2 0+(-674563563/2500000000 : ℝ)*X 2 1+(-1346982831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((505658781/2500000000 : ℝ)*X 0 0+(-649766953/5000000000 : ℝ)*X 0 1+(8052827409/10000000000 : ℝ)*X 0 2+(505658781/2500000000 : ℝ)*X 1 0+(-649766953/5000000000 : ℝ)*X 1 1+(8052827409/10000000000 : ℝ)*X 1 2+(505658781/2500000000 : ℝ)*X 2 0+(-649766953/5000000000 : ℝ)*X 2 1+(8052827409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-8430402903/10000000000 : ℝ)*X 0 1+(1244012841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8221623179/10000000000 : ℝ)*X 1 0+(1717400641/10000000000 : ℝ)*X 1 1+(1381045007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((528531747/2000000000 : ℝ)*X 2 0+(-1386840429/2500000000 : ℝ)*X 2 1+(-1889784343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6776296061/10000000000 : ℝ)*X 0 0+(-30992219/400000000 : ℝ)*X 0 1+(398816363/1000000000 : ℝ)*X 0 2+(6776296061/10000000000 : ℝ)*X 1 0+(-30992219/400000000 : ℝ)*X 1 1+(398816363/1000000000 : ℝ)*X 1 2+(6776296061/10000000000 : ℝ)*X 2 0+(-30992219/400000000 : ℝ)*X 2 1+(398816363/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5887/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5887/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1625804420215646388051/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (219075991781/250000000000 : ℝ)*(base7) + (4096153/1000000000000 : ℝ)*(base17) + (317187/1000000000000 : ℝ)*(base50) + (9639683351/100000000000 : ℝ)*(base54) + (48923051127/25000000000 : ℝ)*(major_s0_0) + (48923051127/25000000000 : ℝ)*(major_s0_1) + (186052521157/100000000000 : ℝ)*(major_s0_2) + (2540476072109/1000000000000 : ℝ)*(sp_s0_7) + (2540493601021/1000000000000 : ℝ)*(sp_s0_8) + (1222050190451/500000000000 : ℝ)*(sp_s0_9) + (420453033151/250000000000 : ℝ)*(sp_s0_13) + (6301889/1000000000000 : ℝ)*(sp_s0_20) + (4325013/200000000000 : ℝ)*(sp_s0_21) + (241381/500000000000 : ℝ)*(sp_s0_23) + (450955650439/500000000000 : ℝ)*(f.failure) + (1270248848587/500000000000 : ℝ)*(f.sum) + (33712413644233/1000000000000000000000000000 : ℝ)*base62 + (3456681860431/20000000000000000000000000 : ℝ)*base65 + (233186079625963/250000000000000000000000000 : ℝ)*base66 + (577945373856033/1000000000000000000000000000 : ℝ)*base68 + (163862722858849/500000000000000000000000000 : ℝ)*base71 + (4378691540941/5000000000000000000000000 : ℝ)*base72 + (763877412941/5000000000000000000000000 : ℝ)*base74 + (33489179274037/250000000000000000000000000 : ℝ)*base77 + (192267687448013/250000000000000000000000000 : ℝ)*base78 + (81/2000000000000000 : ℝ)*base87 + (81/2000000000000000 : ℝ)*base89 + (81/2000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-7683/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7683/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17789688177954348302289/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611954855777/500000000000 : ℝ)*(base7) + (3201/31250000000 : ℝ)*(base31) + (1374089/1000000000000 : ℝ)*(base33) + (66585219633/1000000000000 : ℝ)*(base60) + (377035905023/250000000000 : ℝ)*(major_s0_0) + (1508144994181/1000000000000 : ℝ)*(major_s0_1) + (1508144994181/1000000000000 : ℝ)*(major_s0_2) + (462699/250000000000 : ℝ)*(sp_s0_2) + (2175153/200000000000 : ℝ)*(sp_s0_13) + (1662770898521/1000000000000 : ℝ)*(sp_s0_14) + (1662725376073/1000000000000 : ℝ)*(sp_s0_15) + (415691918409/250000000000 : ℝ)*(sp_s0_16) + (479744126153/250000000000 : ℝ)*(sp_s0_20) + (44148359/1000000000000 : ℝ)*(sp_s0_22) + (139015554251/200000000000 : ℝ)*(f.failure) + (1662770898521/1000000000000 : ℝ)*(f.sum) + (4985429357215761/10000000000000000000000000000 : ℝ)*base63 + (151205649778223/200000000000000000000000000 : ℝ)*base65 + (2704572952126911/10000000000000000000000000000 : ℝ)*base67 + (4351780639126911/10000000000000000000000000000 : ℝ)*base69 + (2194308896878801/5000000000000000000000000000 : ℝ)*base71 + (5834025468491/50000000000000000000000000 : ℝ)*base73 + (3785661121777/200000000000000000000000000 : ℝ)*base75 + (936773389711613/2500000000000000000000000000 : ℝ)*base77 + (5272162595825111/10000000000000000000000000000 : ℝ)*base79 + (371/800000000000000 : ℝ)*base86 + (371/800000000000000 : ℝ)*base88 + (371/800000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2489/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2489/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43537739215252247641977/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1200744097109/1000000000000 : ℝ)*(base7) + (199957/500000000000 : ℝ)*(base39) + (44093461803/500000000000 : ℝ)*(base40) + (164533420189/500000000000 : ℝ)*(base43) + (685359/250000000000 : ℝ)*(base50) + (800533833217/500000000000 : ℝ)*(major_s0_0) + (159000103257/125000000000 : ℝ)*(major_s0_1) + (800533833217/500000000000 : ℝ)*(major_s0_2) + (8794651/200000000000 : ℝ)*(sp_s0_2) + (29096949/100000000000 : ℝ)*(sp_s0_7) + (93055699717/62500000000 : ℝ)*(sp_s0_21) + (90912450267/50000000000 : ℝ)*(sp_s0_22) + (1489138191707/1000000000000 : ℝ)*(sp_s0_23) + (484662077559/250000000000 : ℝ)*(sp_s0_27) + (92238026641/125000000000 : ℝ)*(f.failure) + (90912450267/50000000000 : ℝ)*(f.sum) + (1004206734830373/5000000000000000000000000000 : ℝ)*base62 + (17361691334589/100000000000000000000000000 : ℝ)*base64 + (1131115603169067/1250000000000000000000000000 : ℝ)*base67 + (2115558765515827/5000000000000000000000000000 : ℝ)*base69 + (463192536213623/5000000000000000000000000000 : ℝ)*base70 + (88367239594589/100000000000000000000000000 : ℝ)*base73 + (5222840208269/25000000000000000000000000 : ℝ)*base75 + (236935987984173/5000000000000000000000000000 : ℝ)*base76 + (2479347071452859/2500000000000000000000000000 : ℝ)*base79 + (239/500000000000000 : ℝ)*base87 + (239/500000000000000 : ℝ)*base89 + (239/500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (5887/12500 : ℝ) ^ (91/16 : ℝ) ≤ (345172857913505171/25000000000000000000 : ℝ) := by
    have hpowers : (5887/12500 : ℝ)^91 ≤ (345172857913505171/25000000000000000000 : ℝ)^16 := by
      have hnat : (5887 : ℕ)^91*25000000000000000000^16 ≤ 345172857913505171^16*12500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5887 12500 345172857913505171 25000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5887/12500 : ℝ)) (X := (345172857913505171/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25345172857913505171/25000000000000000000 : ℝ) ≤ (10024138920066473/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (25345172857913505171/25000000000000000000 : ℝ)^16 ≤ (10024138920066473/10000000000000000 : ℝ)^91 := by
      have hnat : (25345172857913505171 : ℕ)^16*10000000000000000^91 ≤ 10024138920066473^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25345172857913505171 25000000000000000000 10024138920066473 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024138920066473/10000000000000000 : ℝ)) (X := (25345172857913505171/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12845172857913505171/12500000000000000000 : ℝ) ≤ (1004800839962787/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (12845172857913505171/12500000000000000000 : ℝ)^16 ≤ (1004800839962787/1000000000000000 : ℝ)^91 := by
      have hnat : (12845172857913505171 : ℕ)^16*1000000000000000^91 ≤ 1004800839962787^91*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12845172857913505171 12500000000000000000 1004800839962787 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004800839962787/1000000000000000 : ℝ)) (X := (12845172857913505171/12500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(24138920066473/4709600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23869479561397/4709600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (5887/12500 : ℝ)) (alpha := (24138920066473/4709600000000000 : ℝ)) (beta := (23869479561397/4709600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5887/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(24138920066473/4709600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23869479561397/4709600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7683/12500 : ℝ) ^ (91/16 : ℝ) ≤ (156935401725762311/2500000000000000000 : ℝ) := by
    have hpowers : (7683/12500 : ℝ)^91 ≤ (156935401725762311/2500000000000000000 : ℝ)^16 := by
      have hnat : (7683 : ℕ)^91*2500000000000000000^16 ≤ 156935401725762311^16*12500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7683 12500 156935401725762311 2500000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7683/12500 : ℝ)) (X := (156935401725762311/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (2656935401725762311/2500000000000000000 : ℝ) ≤ (252690534117367/250000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (2656935401725762311/2500000000000000000 : ℝ)^16 ≤ (252690534117367/250000000000000 : ℝ)^91 := by
      have hnat : (2656935401725762311 : ℕ)^16*250000000000000^91 ≤ 252690534117367^91*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2656935401725762311 2500000000000000000 252690534117367 250000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252690534117367/250000000000000 : ℝ)) (X := (2656935401725762311/2500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1406935401725762311/1250000000000000000 : ℝ) ≤ (5105062491954683/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (1406935401725762311/1250000000000000000 : ℝ)^16 ≤ (5105062491954683/5000000000000000 : ℝ)^91 := by
      have hnat : (1406935401725762311 : ℕ)^16*5000000000000000^91 ≤ 5105062491954683^91*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1406935401725762311 1250000000000000000 5105062491954683 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5105062491954683/5000000000000000 : ℝ)) (X := (1406935401725762311/1250000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(896844705789/51220000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(17083936535781/1024400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (7683/12500 : ℝ)) (alpha := (896844705789/51220000000000 : ℝ)) (beta := (17083936535781/1024400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7683/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(896844705789/51220000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(17083936535781/1024400000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2489/4000 : ℝ) ^ (91/16 : ℝ) ≤ (6732485066792097023/100000000000000000000 : ℝ) := by
    have hpowers : (2489/4000 : ℝ)^91 ≤ (6732485066792097023/100000000000000000000 : ℝ)^16 := by
      have hnat : (2489 : ℕ)^91*100000000000000000000^16 ≤ 6732485066792097023^16*4000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2489 4000 6732485066792097023 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2489/4000 : ℝ)) (X := (6732485066792097023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (106732485066792097023/100000000000000000000 : ℝ) ≤ (404608704282577/400000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (106732485066792097023/100000000000000000000 : ℝ)^16 ≤ (404608704282577/400000000000000 : ℝ)^91 := by
      have hnat : (106732485066792097023 : ℕ)^16*400000000000000^91 ≤ 404608704282577^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106732485066792097023 100000000000000000000 404608704282577 400000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (404608704282577/400000000000000 : ℝ)) (X := (106732485066792097023/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (56732485066792097023/50000000000000000000 : ℝ) ≤ (10224593042842739/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (56732485066792097023/50000000000000000000 : ℝ)^16 ≤ (10224593042842739/10000000000000000 : ℝ)^91 := by
      have hnat : (56732485066792097023 : ℕ)^16*10000000000000000^91 ≤ 10224593042842739^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56732485066792097023 50000000000000000000 10224593042842739 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10224593042842739/10000000000000000 : ℝ)) (X := (56732485066792097023/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4608704282577/248900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(54687717889157/3111250000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (2489/4000 : ℝ)) (alpha := (4608704282577/248900000000000 : ℝ)) (beta := (54687717889157/3111250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2489/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4608704282577/248900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(54687717889157/3111250000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-17252261/200000000 : ℝ)*X 0 0+(-169827867/312500000 : ℝ)*X 0 1+(2673080663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1393915461/2500000000 : ℝ)*X 1 0+(3268992857/10000000000 : ℝ)*X 1 1+(3142239739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((66219559/125000000 : ℝ)*X 2 0+(-3429438509/10000000000 : ℝ)*X 2 1+(-3290583187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_3 : ((9999999997/10000000000 : ℝ)*X 1 0+(1/156250000 : ℝ)*X 1 1+(1/156250000 : ℝ)*X 1 2+(9999999997/10000000000 : ℝ)*X 2 0+(1/156250000 : ℝ)*X 2 1+(1/156250000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s1_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2251935031/5000000000 : ℝ)*X 0 0+(-637594207/2000000000 : ℝ)*X 0 1+(4360896203/10000000000 : ℝ)*X 0 2+(2251935031/5000000000 : ℝ)*X 1 0+(-637594207/2000000000 : ℝ)*X 1 1+(4360896203/10000000000 : ℝ)*X 1 2+(2251935031/5000000000 : ℝ)*X 2 0+(-637594207/2000000000 : ℝ)*X 2 1+(4360896203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328086_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-3730664690944279530863728609904613/375256748230000000000000000000000 : ℝ) := by norm_num
    linear_combination (37131/200000000000 : ℝ)*(base7) + (284547/500000000000 : ℝ)*(base10) + (11313/25000000000 : ℝ)*(base17) + (5273/1000000000000 : ℝ)*(base21) + (703357681413/1000000000000 : ℝ)*(base40) + (33463/125000000000 : ℝ)*(base43) + (1763342017/20000000000 : ℝ)*(base60) + (542442921571/250000000000 : ℝ)*(major_s1_0) + (271218716537/125000000000 : ℝ)*(major_s1_1) + (8679/4000 : ℝ)*(major_s1_2) + (3313876569447/1000000000000 : ℝ)*(sp_s1_0) + (132555078149/40000000000 : ℝ)*(sp_s1_1) + (3313877133267/1000000000000 : ℝ)*(sp_s1_2) + (5421571/250000000000 : ℝ)*(sp_s1_3) + (200000037131/200000000000 : ℝ)*(sp_s1_6) + (662775481249/200000000000 : ℝ)*(f.sum) + (10271538724314567/318716450000000000000000000000 : ℝ)*base62 + (6816622099077/24890000000000000000000000 : ℝ)*base65 + (482752128527/5122000000000000000000000 : ℝ)*base66 + (1199529733881/12445000000000000000000000 : ℝ)*base68 + (322247818428831773/2930548600000000000000000000000 : ℝ)*base70 + (36086456235153/1177400000000000000000000000 : ℝ)*base72 + (65665975126007/128050000000000000000000000 : ℝ)*base75 + (234578748984437/1177400000000000000000000000 : ℝ)*base76 + (256955269338244993/3015321400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_b041 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=85 ∨ c=86 ∨ c=87 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c328085 p hpa (by linarith only [hpb]) X hX
  · exact collision_c328086 p hpa (by linarith only [hpb]) X hX
  · exact (hn87 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 85 ≤ c.val) (hhi : c.val < 88)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b041 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
