-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:11.930185+00:00
-- url     : https://prove2.me/submissions/efa3c1cb-a1ac-4b56-a24e-33c6dbd09118

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
theorem collision_support_c312029_s0_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971723679/5000000000 : ℝ)*x 0 + (238620731/625000000 : ℝ)*x 1 + (4897447833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971723679/5000000000 : ℝ)^37 ≤ (15253291937557/50000000000000 : ℝ)^29 := by
    have hnat : (1971723679 : ℕ)^37*50000000000000^29 ≤ 15253291937557^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971723679 5000000000 15253291937557 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238620731/625000000 : ℝ)^37 ≤ (29273213752901/100000000000000 : ℝ)^29 := by
    have hnat : (238620731 : ℕ)^37*100000000000000^29 ≤ 29273213752901^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238620731 625000000 29273213752901 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4897447833/10000000000 : ℝ)^37 ≤ (20110101181693/50000000000000 : ℝ)^29 := by
    have hnat : (4897447833 : ℕ)^37*50000000000000^29 ≤ 20110101181693^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4897447833 10000000000 20110101181693 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971723679/5000000000 : ℝ), (238620731/625000000 : ℝ), (4897447833/10000000000 : ℝ)] ![(15253291937557/50000000000000 : ℝ), (29273213752901/100000000000000 : ℝ), (20110101181693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971723679/5000000000 : ℝ)|^37 ≤ (15253291937557/50000000000000 : ℝ)^29
        have hw : |(-1971723679/5000000000 : ℝ)|=(1971723679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238620731/625000000 : ℝ)|^37 ≤ (29273213752901/100000000000000 : ℝ)^29
        have hw : |(238620731/625000000 : ℝ)|=(238620731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4897447833/10000000000 : ℝ)|^37 ≤ (20110101181693/50000000000000 : ℝ)^29
        have hw : |(4897447833/10000000000 : ℝ)|=(4897447833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (608059461/1000000000 : ℝ)*x 0 + (-1012341907/10000000000 : ℝ)*x 1 + (1005913677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (608059461/1000000000 : ℝ)^37 ≤ (3313027020569/6250000000000 : ℝ)^29 := by
    have hnat : (608059461 : ℕ)^37*6250000000000^29 ≤ 3313027020569^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608059461 1000000000 3313027020569 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012341907/10000000000 : ℝ)^37 ≤ (5381888834867/100000000000000 : ℝ)^29 := by
    have hnat : (1012341907 : ℕ)^37*100000000000000^29 ≤ 5381888834867^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012341907 10000000000 5381888834867 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005913677/2000000000 : ℝ)^37 ≤ (20804839414961/50000000000000 : ℝ)^29 := by
    have hnat : (1005913677 : ℕ)^37*50000000000000^29 ≤ 20804839414961^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005913677 2000000000 20804839414961 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(608059461/1000000000 : ℝ), (-1012341907/10000000000 : ℝ), (1005913677/2000000000 : ℝ)] ![(3313027020569/6250000000000 : ℝ), (5381888834867/100000000000000 : ℝ), (20804839414961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(608059461/1000000000 : ℝ)|^37 ≤ (3313027020569/6250000000000 : ℝ)^29
        have hw : |(608059461/1000000000 : ℝ)|=(608059461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1012341907/10000000000 : ℝ)|^37 ≤ (5381888834867/100000000000000 : ℝ)^29
        have hw : |(-1012341907/10000000000 : ℝ)|=(1012341907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005913677/2000000000 : ℝ)|^37 ≤ (20804839414961/50000000000000 : ℝ)^29
        have hw : |(1005913677/2000000000 : ℝ)|=(1005913677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (952466561/5000000000 : ℝ)*x 0 + (7734021339/10000000000 : ℝ)*x 1 + (-924131/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952466561/5000000000 : ℝ)^37 ≤ (6028314072449/50000000000000 : ℝ)^29 := by
    have hnat : (952466561 : ℕ)^37*50000000000000^29 ≤ 6028314072449^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952466561 5000000000 6028314072449 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7734021339/10000000000 : ℝ)^37 ≤ (1801194648869/2500000000000 : ℝ)^29 := by
    have hnat : (7734021339 : ℕ)^37*2500000000000^29 ≤ 1801194648869^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7734021339 10000000000 1801194648869 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924131/3906250 : ℝ)^37 ≤ (635823435321/4000000000000 : ℝ)^29 := by
    have hnat : (924131 : ℕ)^37*4000000000000^29 ≤ 635823435321^29*3906250^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924131 3906250 635823435321 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(952466561/5000000000 : ℝ), (7734021339/10000000000 : ℝ), (-924131/3906250 : ℝ)] ![(6028314072449/50000000000000 : ℝ), (1801194648869/2500000000000 : ℝ), (635823435321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(952466561/5000000000 : ℝ)|^37 ≤ (6028314072449/50000000000000 : ℝ)^29
        have hw : |(952466561/5000000000 : ℝ)|=(952466561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7734021339/10000000000 : ℝ)|^37 ≤ (1801194648869/2500000000000 : ℝ)^29
        have hw : |(7734021339/10000000000 : ℝ)|=(7734021339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924131/3906250 : ℝ)|^37 ≤ (635823435321/4000000000000 : ℝ)^29
        have hw : |(-924131/3906250 : ℝ)|=(924131/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_4 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^37 ≤ (0 : ℝ)^29 := by
    have hnat : (0 : ℕ)^37*1^29 ≤ 0^29*1^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^37 ≤ (1 : ℝ)^29 := by
    have hnat : (1 : ℕ)^37*1^29 ≤ 1^29*1^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^37 ≤ (0 : ℝ)^29 := by
    have hnat : (0 : ℕ)^37*1^29 ≤ 0^29*1^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^37 ≤ (0 : ℝ)^29
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^37 ≤ (1 : ℝ)^29
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^37 ≤ (0 : ℝ)^29
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108362493/5000000000 : ℝ)*x 0 + (2905148443/10000000000 : ℝ)*x 1 + (5451456967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108362493/5000000000 : ℝ)^37 ≤ (16614611314537/50000000000000 : ℝ)^29 := by
    have hnat : (2108362493 : ℕ)^37*50000000000000^29 ≤ 16614611314537^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108362493 5000000000 16614611314537 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2905148443/10000000000 : ℝ)^37 ≤ (20657455818477/100000000000000 : ℝ)^29 := by
    have hnat : (2905148443 : ℕ)^37*100000000000000^29 ≤ 20657455818477^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905148443 10000000000 20657455818477 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451456967/10000000000 : ℝ)^37 ≤ (23056660772843/50000000000000 : ℝ)^29 := by
    have hnat : (5451456967 : ℕ)^37*50000000000000^29 ≤ 23056660772843^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451456967 10000000000 23056660772843 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108362493/5000000000 : ℝ), (2905148443/10000000000 : ℝ), (5451456967/10000000000 : ℝ)] ![(16614611314537/50000000000000 : ℝ), (20657455818477/100000000000000 : ℝ), (23056660772843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108362493/5000000000 : ℝ)|^37 ≤ (16614611314537/50000000000000 : ℝ)^29
        have hw : |(-2108362493/5000000000 : ℝ)|=(2108362493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2905148443/10000000000 : ℝ)|^37 ≤ (20657455818477/100000000000000 : ℝ)^29
        have hw : |(2905148443/10000000000 : ℝ)|=(2905148443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451456967/10000000000 : ℝ)|^37 ≤ (23056660772843/50000000000000 : ℝ)^29
        have hw : |(5451456967/10000000000 : ℝ)|=(5451456967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1380271709/2500000000 : ℝ)*x 0 + (-11049757/400000000 : ℝ)*x 1 + (2999722613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380271709/2500000000 : ℝ)^37 ≤ (46866113946111/100000000000000 : ℝ)^29 := by
    have hnat : (1380271709 : ℕ)^37*100000000000000^29 ≤ 46866113946111^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380271709 2500000000 46866113946111 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11049757/400000000 : ℝ)^37 ≤ (205274272173/20000000000000 : ℝ)^29 := by
    have hnat : (11049757 : ℕ)^37*20000000000000^29 ≤ 205274272173^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11049757 400000000 205274272173 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999722613/5000000000 : ℝ)^37 ≤ (13026878670943/25000000000000 : ℝ)^29 := by
    have hnat : (2999722613 : ℕ)^37*25000000000000^29 ≤ 13026878670943^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999722613 5000000000 13026878670943 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380271709/2500000000 : ℝ), (-11049757/400000000 : ℝ), (2999722613/5000000000 : ℝ)] ![(46866113946111/100000000000000 : ℝ), (205274272173/20000000000000 : ℝ), (13026878670943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380271709/2500000000 : ℝ)|^37 ≤ (46866113946111/100000000000000 : ℝ)^29
        have hw : |(1380271709/2500000000 : ℝ)|=(1380271709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11049757/400000000 : ℝ)|^37 ≤ (205274272173/20000000000000 : ℝ)^29
        have hw : |(-11049757/400000000 : ℝ)|=(11049757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999722613/5000000000 : ℝ)|^37 ≤ (13026878670943/25000000000000 : ℝ)^29
        have hw : |(2999722613/5000000000 : ℝ)|=(2999722613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1089851/15625000 : ℝ)*x 0 + (1873643137/2000000000 : ℝ)*x 1 + (-901746389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089851/15625000 : ℝ)^37 ≤ (418249687009/12500000000000 : ℝ)^29 := by
    have hnat : (1089851 : ℕ)^37*12500000000000^29 ≤ 418249687009^29*15625000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089851 15625000 418249687009 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873643137/2000000000 : ℝ)^37 ≤ (46005324022019/50000000000000 : ℝ)^29 := by
    have hnat : (1873643137 : ℕ)^37*50000000000000^29 ≤ 46005324022019^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873643137 2000000000 46005324022019 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901746389/10000000000 : ℝ)^37 ≤ (2321677220149/50000000000000 : ℝ)^29 := by
    have hnat : (901746389 : ℕ)^37*50000000000000^29 ≤ 2321677220149^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901746389 10000000000 2321677220149 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089851/15625000 : ℝ), (1873643137/2000000000 : ℝ), (-901746389/10000000000 : ℝ)] ![(418249687009/12500000000000 : ℝ), (46005324022019/50000000000000 : ℝ), (2321677220149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089851/15625000 : ℝ)|^37 ≤ (418249687009/12500000000000 : ℝ)^29
        have hw : |(1089851/15625000 : ℝ)|=(1089851/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1873643137/2000000000 : ℝ)|^37 ≤ (46005324022019/50000000000000 : ℝ)^29
        have hw : |(1873643137/2000000000 : ℝ)|=(1873643137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-901746389/10000000000 : ℝ)|^37 ≤ (2321677220149/50000000000000 : ℝ)^29
        have hw : |(-901746389/10000000000 : ℝ)|=(901746389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_12 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4140182267/10000000000 : ℝ)*x 0 + (4038353651/10000000000 : ℝ)*x 1 + (4498896227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4140182267/10000000000 : ℝ)^37 ≤ (32461580194361/100000000000000 : ℝ)^29 := by
    have hnat : (4140182267 : ℕ)^37*100000000000000^29 ≤ 32461580194361^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140182267 10000000000 32461580194361 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4038353651/10000000000 : ℝ)^37 ≤ (15723204753647/50000000000000 : ℝ)^29 := by
    have hnat : (4038353651 : ℕ)^37*50000000000000^29 ≤ 15723204753647^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038353651 10000000000 15723204753647 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498896227/10000000000 : ℝ)^37 ≤ (36092010284557/100000000000000 : ℝ)^29 := by
    have hnat : (4498896227 : ℕ)^37*100000000000000^29 ≤ 36092010284557^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498896227 10000000000 36092010284557 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4140182267/10000000000 : ℝ), (4038353651/10000000000 : ℝ), (4498896227/10000000000 : ℝ)] ![(32461580194361/100000000000000 : ℝ), (15723204753647/50000000000000 : ℝ), (36092010284557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4140182267/10000000000 : ℝ)|^37 ≤ (32461580194361/100000000000000 : ℝ)^29
        have hw : |(4140182267/10000000000 : ℝ)|=(4140182267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4038353651/10000000000 : ℝ)|^37 ≤ (15723204753647/50000000000000 : ℝ)^29
        have hw : |(4038353651/10000000000 : ℝ)|=(4038353651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498896227/10000000000 : ℝ)|^37 ≤ (36092010284557/100000000000000 : ℝ)^29
        have hw : |(4498896227/10000000000 : ℝ)|=(4498896227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4623131561/10000000000 : ℝ)*x 0 + (325641927/1250000000 : ℝ)*x 1 + (2657983613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4623131561/10000000000 : ℝ)^37 ≤ (18684215945541/50000000000000 : ℝ)^29 := by
    have hnat : (4623131561 : ℕ)^37*50000000000000^29 ≤ 18684215945541^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4623131561 10000000000 18684215945541 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325641927/1250000000 : ℝ)^37 ≤ (1123466324519/6250000000000 : ℝ)^29 := by
    have hnat : (325641927 : ℕ)^37*6250000000000^29 ≤ 1123466324519^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325641927 1250000000 1123466324519 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2657983613/5000000000 : ℝ)^37 ≤ (893122138121/2000000000000 : ℝ)^29 := by
    have hnat : (2657983613 : ℕ)^37*2000000000000^29 ≤ 893122138121^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2657983613 5000000000 893122138121 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4623131561/10000000000 : ℝ), (325641927/1250000000 : ℝ), (2657983613/5000000000 : ℝ)] ![(18684215945541/50000000000000 : ℝ), (1123466324519/6250000000000 : ℝ), (893122138121/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4623131561/10000000000 : ℝ)|^37 ≤ (18684215945541/50000000000000 : ℝ)^29
        have hw : |(-4623131561/10000000000 : ℝ)|=(4623131561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325641927/1250000000 : ℝ)|^37 ≤ (1123466324519/6250000000000 : ℝ)^29
        have hw : |(325641927/1250000000 : ℝ)|=(325641927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2657983613/5000000000 : ℝ)|^37 ≤ (893122138121/2000000000000 : ℝ)^29
        have hw : |(2657983613/5000000000 : ℝ)|=(2657983613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (888804981/1250000000 : ℝ)*x 0 + (-1244745737/10000000000 : ℝ)*x 1 + (3715414987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888804981/1250000000 : ℝ)^37 ≤ (32360134947343/50000000000000 : ℝ)^29 := by
    have hnat : (888804981 : ℕ)^37*50000000000000^29 ≤ 32360134947343^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888804981 1250000000 32360134947343 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1244745737/10000000000 : ℝ)^37 ≤ (7005638489859/100000000000000 : ℝ)^29 := by
    have hnat : (1244745737 : ℕ)^37*100000000000000^29 ≤ 7005638489859^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244745737 10000000000 7005638489859 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3715414987/10000000000 : ℝ)^37 ≤ (28274091597727/100000000000000 : ℝ)^29 := by
    have hnat : (3715414987 : ℕ)^37*100000000000000^29 ≤ 28274091597727^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715414987 10000000000 28274091597727 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(888804981/1250000000 : ℝ), (-1244745737/10000000000 : ℝ), (3715414987/10000000000 : ℝ)] ![(32360134947343/50000000000000 : ℝ), (7005638489859/100000000000000 : ℝ), (28274091597727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(888804981/1250000000 : ℝ)|^37 ≤ (32360134947343/50000000000000 : ℝ)^29
        have hw : |(888804981/1250000000 : ℝ)|=(888804981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1244745737/10000000000 : ℝ)|^37 ≤ (7005638489859/100000000000000 : ℝ)^29
        have hw : |(-1244745737/10000000000 : ℝ)|=(1244745737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3715414987/10000000000 : ℝ)|^37 ≤ (28274091597727/100000000000000 : ℝ)^29
        have hw : |(3715414987/10000000000 : ℝ)|=(3715414987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (165808749/1250000000 : ℝ)*x 0 + (7909410931/10000000000 : ℝ)*x 1 + (-2637788257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165808749/1250000000 : ℝ)^37 ≤ (3798856877803/50000000000000 : ℝ)^29 := by
    have hnat : (165808749 : ℕ)^37*50000000000000^29 ≤ 3798856877803^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165808749 1250000000 3798856877803 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7909410931/10000000000 : ℝ)^37 ≤ (7413887154487/10000000000000 : ℝ)^29 := by
    have hnat : (7909410931 : ℕ)^37*10000000000000^29 ≤ 7413887154487^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7909410931 10000000000 7413887154487 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637788257/10000000000 : ℝ)^37 ≤ (228292683613/1250000000000 : ℝ)^29 := by
    have hnat : (2637788257 : ℕ)^37*1250000000000^29 ≤ 228292683613^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637788257 10000000000 228292683613 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165808749/1250000000 : ℝ), (7909410931/10000000000 : ℝ), (-2637788257/10000000000 : ℝ)] ![(3798856877803/50000000000000 : ℝ), (7413887154487/10000000000000 : ℝ), (228292683613/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165808749/1250000000 : ℝ)|^37 ≤ (3798856877803/50000000000000 : ℝ)^29
        have hw : |(165808749/1250000000 : ℝ)|=(165808749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7909410931/10000000000 : ℝ)|^37 ≤ (7413887154487/10000000000000 : ℝ)^29
        have hw : |(7909410931/10000000000 : ℝ)|=(7909410931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2637788257/10000000000 : ℝ)|^37 ≤ (228292683613/1250000000000 : ℝ)^29
        have hw : |(-2637788257/10000000000 : ℝ)|=(2637788257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (711207233/2500000000 : ℝ)*x 0 + (1775975919/5000000000 : ℝ)*x 1 + (381065337/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (711207233/2500000000 : ℝ)^37 ≤ (20111800751301/100000000000000 : ℝ)^29 := by
    have hnat : (711207233 : ℕ)^37*100000000000000^29 ≤ 20111800751301^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711207233 2500000000 20111800751301 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1775975919/5000000000 : ℝ)^37 ≤ (13348362375391/50000000000000 : ℝ)^29 := by
    have hnat : (1775975919 : ℕ)^37*50000000000000^29 ≤ 13348362375391^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775975919 5000000000 13348362375391 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381065337/625000000 : ℝ)^37 ≤ (26595737240333/50000000000000 : ℝ)^29 := by
    have hnat : (381065337 : ℕ)^37*50000000000000^29 ≤ 26595737240333^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381065337 625000000 26595737240333 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(711207233/2500000000 : ℝ), (1775975919/5000000000 : ℝ), (381065337/625000000 : ℝ)] ![(20111800751301/100000000000000 : ℝ), (13348362375391/50000000000000 : ℝ), (26595737240333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(711207233/2500000000 : ℝ)|^37 ≤ (20111800751301/100000000000000 : ℝ)^29
        have hw : |(711207233/2500000000 : ℝ)|=(711207233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1775975919/5000000000 : ℝ)|^37 ≤ (13348362375391/50000000000000 : ℝ)^29
        have hw : |(1775975919/5000000000 : ℝ)|=(1775975919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(381065337/625000000 : ℝ)|^37 ≤ (26595737240333/50000000000000 : ℝ)^29
        have hw : |(381065337/625000000 : ℝ)|=(381065337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2993160611/10000000000 : ℝ)*x 0 + (760902163/2000000000 : ℝ)*x 1 + (2876800491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2993160611/10000000000 : ℝ)^37 ≤ (2682403939617/12500000000000 : ℝ)^29 := by
    have hnat : (2993160611 : ℕ)^37*12500000000000^29 ≤ 2682403939617^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2993160611 10000000000 2682403939617 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (760902163/2000000000 : ℝ)^37 ≤ (5828397773639/20000000000000 : ℝ)^29 := by
    have hnat : (760902163 : ℕ)^37*20000000000000^29 ≤ 5828397773639^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760902163 2000000000 5828397773639 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2876800491/5000000000 : ℝ)^37 ≤ (24699389800761/50000000000000 : ℝ)^29 := by
    have hnat : (2876800491 : ℕ)^37*50000000000000^29 ≤ 24699389800761^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876800491 5000000000 24699389800761 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2993160611/10000000000 : ℝ), (760902163/2000000000 : ℝ), (2876800491/5000000000 : ℝ)] ![(2682403939617/12500000000000 : ℝ), (5828397773639/20000000000000 : ℝ), (24699389800761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2993160611/10000000000 : ℝ)|^37 ≤ (2682403939617/12500000000000 : ℝ)^29
        have hw : |(-2993160611/10000000000 : ℝ)|=(2993160611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(760902163/2000000000 : ℝ)|^37 ≤ (5828397773639/20000000000000 : ℝ)^29
        have hw : |(760902163/2000000000 : ℝ)|=(760902163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2876800491/5000000000 : ℝ)|^37 ≤ (24699389800761/50000000000000 : ℝ)^29
        have hw : |(2876800491/5000000000 : ℝ)|=(2876800491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1928212889/2500000000 : ℝ)*x 0 + (-140342301/5000000000 : ℝ)*x 1 + (1799892299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928212889/2500000000 : ℝ)^37 ≤ (71796266664381/100000000000000 : ℝ)^29 := by
    have hnat : (1928212889 : ℕ)^37*100000000000000^29 ≤ 71796266664381^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928212889 2500000000 71796266664381 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140342301/5000000000 : ℝ)^37 ≤ (523734233309/50000000000000 : ℝ)^29 := by
    have hnat : (140342301 : ℕ)^37*50000000000000^29 ≤ 523734233309^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140342301 5000000000 523734233309 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799892299/5000000000 : ℝ)^37 ≤ (5431252970959/20000000000000 : ℝ)^29 := by
    have hnat : (1799892299 : ℕ)^37*20000000000000^29 ≤ 5431252970959^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799892299 5000000000 5431252970959 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1928212889/2500000000 : ℝ), (-140342301/5000000000 : ℝ), (1799892299/5000000000 : ℝ)] ![(71796266664381/100000000000000 : ℝ), (523734233309/50000000000000 : ℝ), (5431252970959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1928212889/2500000000 : ℝ)|^37 ≤ (71796266664381/100000000000000 : ℝ)^29
        have hw : |(1928212889/2500000000 : ℝ)|=(1928212889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140342301/5000000000 : ℝ)|^37 ≤ (523734233309/50000000000000 : ℝ)^29
        have hw : |(-140342301/5000000000 : ℝ)|=(140342301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1799892299/5000000000 : ℝ)|^37 ≤ (5431252970959/20000000000000 : ℝ)^29
        have hw : |(1799892299/5000000000 : ℝ)|=(1799892299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (699563941/10000000000 : ℝ)*x 0 + (1139982273/1250000000 : ℝ)*x 1 + (-672368159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (699563941/10000000000 : ℝ)^37 ≤ (1679303220691/50000000000000 : ℝ)^29 := by
    have hnat : (699563941 : ℕ)^37*50000000000000^29 ≤ 1679303220691^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699563941 10000000000 1679303220691 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139982273/1250000000 : ℝ)^37 ≤ (71127951701/80000000000 : ℝ)^29 := by
    have hnat : (1139982273 : ℕ)^37*80000000000^29 ≤ 71127951701^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139982273 1250000000 71127951701 80000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672368159/5000000000 : ℝ)^37 ≤ (7731453910827/100000000000000 : ℝ)^29 := by
    have hnat : (672368159 : ℕ)^37*100000000000000^29 ≤ 7731453910827^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672368159 5000000000 7731453910827 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(699563941/10000000000 : ℝ), (1139982273/1250000000 : ℝ), (-672368159/5000000000 : ℝ)] ![(1679303220691/50000000000000 : ℝ), (71127951701/80000000000 : ℝ), (7731453910827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(699563941/10000000000 : ℝ)|^37 ≤ (1679303220691/50000000000000 : ℝ)^29
        have hw : |(699563941/10000000000 : ℝ)|=(699563941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139982273/1250000000 : ℝ)|^37 ≤ (71127951701/80000000000 : ℝ)^29
        have hw : |(1139982273/1250000000 : ℝ)|=(1139982273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-672368159/5000000000 : ℝ)|^37 ≤ (7731453910827/100000000000000 : ℝ)^29
        have hw : |(-672368159/5000000000 : ℝ)|=(672368159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s0_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (839174727/1250000000 : ℝ)*x 0 + (1252875369/5000000000 : ℝ)*x 1 + (1566657019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839174727/1250000000 : ℝ)^37 ≤ (60145390739113/100000000000000 : ℝ)^29 := by
    have hnat : (839174727 : ℕ)^37*100000000000000^29 ≤ 60145390739113^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839174727 1250000000 60145390739113 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252875369/5000000000 : ℝ)^37 ≤ (2138147375219/12500000000000 : ℝ)^29 := by
    have hnat : (1252875369 : ℕ)^37*12500000000000^29 ≤ 2138147375219^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252875369 5000000000 2138147375219 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1566657019/5000000000 : ℝ)^37 ≤ (2274943024437/10000000000000 : ℝ)^29 := by
    have hnat : (1566657019 : ℕ)^37*10000000000000^29 ≤ 2274943024437^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566657019 5000000000 2274943024437 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839174727/1250000000 : ℝ), (1252875369/5000000000 : ℝ), (1566657019/5000000000 : ℝ)] ![(60145390739113/100000000000000 : ℝ), (2138147375219/12500000000000 : ℝ), (2274943024437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839174727/1250000000 : ℝ)|^37 ≤ (60145390739113/100000000000000 : ℝ)^29
        have hw : |(839174727/1250000000 : ℝ)|=(839174727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1252875369/5000000000 : ℝ)|^37 ≤ (2138147375219/12500000000000 : ℝ)^29
        have hw : |(1252875369/5000000000 : ℝ)|=(1252875369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1566657019/5000000000 : ℝ)|^37 ≤ (2274943024437/10000000000000 : ℝ)^29
        have hw : |(1566657019/5000000000 : ℝ)|=(1566657019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020912749/5000000000 : ℝ)*x 0 + (4188019841/10000000000 : ℝ)*x 1 + (1112155091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020912749/5000000000 : ℝ)^37 ≤ (31480906600881/100000000000000 : ℝ)^29 := by
    have hnat : (2020912749 : ℕ)^37*100000000000000^29 ≤ 31480906600881^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020912749 5000000000 31480906600881 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4188019841/10000000000 : ℝ)^37 ≤ (16470443030003/50000000000000 : ℝ)^29 := by
    have hnat : (4188019841 : ℕ)^37*50000000000000^29 ≤ 16470443030003^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188019841 10000000000 16470443030003 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112155091/2500000000 : ℝ)^37 ≤ (4447275915631/12500000000000 : ℝ)^29 := by
    have hnat : (1112155091 : ℕ)^37*12500000000000^29 ≤ 4447275915631^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112155091 2500000000 4447275915631 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020912749/5000000000 : ℝ), (4188019841/10000000000 : ℝ), (1112155091/2500000000 : ℝ)] ![(31480906600881/100000000000000 : ℝ), (16470443030003/50000000000000 : ℝ), (4447275915631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020912749/5000000000 : ℝ)|^37 ≤ (31480906600881/100000000000000 : ℝ)^29
        have hw : |(-2020912749/5000000000 : ℝ)|=(2020912749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4188019841/10000000000 : ℝ)|^37 ≤ (16470443030003/50000000000000 : ℝ)^29
        have hw : |(4188019841/10000000000 : ℝ)|=(4188019841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112155091/2500000000 : ℝ)|^37 ≤ (4447275915631/12500000000000 : ℝ)^29
        have hw : |(1112155091/2500000000 : ℝ)|=(1112155091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2673040687/5000000000 : ℝ)*x 0 + (-2322836669/10000000000 : ℝ)*x 1 + (4827857201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673040687/5000000000 : ℝ)^37 ≤ (22489556834451/50000000000000 : ℝ)^29 := by
    have hnat : (2673040687 : ℕ)^37*50000000000000^29 ≤ 22489556834451^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673040687 5000000000 22489556834451 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2322836669/10000000000 : ℝ)^37 ≤ (15528420138529/100000000000000 : ℝ)^29 := by
    have hnat : (2322836669 : ℕ)^37*100000000000000^29 ≤ 15528420138529^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322836669 10000000000 15528420138529 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4827857201/10000000000 : ℝ)^37 ≤ (39492466178761/100000000000000 : ℝ)^29 := by
    have hnat : (4827857201 : ℕ)^37*100000000000000^29 ≤ 39492466178761^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827857201 10000000000 39492466178761 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673040687/5000000000 : ℝ), (-2322836669/10000000000 : ℝ), (4827857201/10000000000 : ℝ)] ![(22489556834451/50000000000000 : ℝ), (15528420138529/100000000000000 : ℝ), (39492466178761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673040687/5000000000 : ℝ)|^37 ≤ (22489556834451/50000000000000 : ℝ)^29
        have hw : |(2673040687/5000000000 : ℝ)|=(2673040687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2322836669/10000000000 : ℝ)|^37 ≤ (15528420138529/100000000000000 : ℝ)^29
        have hw : |(-2322836669/10000000000 : ℝ)|=(2322836669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4827857201/10000000000 : ℝ)|^37 ≤ (39492466178761/100000000000000 : ℝ)^29
        have hw : |(4827857201/10000000000 : ℝ)|=(4827857201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1505045741/5000000000 : ℝ)*x 0 + (6165841889/10000000000 : ℝ)*x 1 + (-662609223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1505045741/5000000000 : ℝ)^37 ≤ (5403555534469/25000000000000 : ℝ)^29 := by
    have hnat : (1505045741 : ℕ)^37*25000000000000^29 ≤ 5403555534469^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505045741 5000000000 5403555534469 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6165841889/10000000000 : ℝ)^37 ≤ (26979211500983/50000000000000 : ℝ)^29 := by
    have hnat : (6165841889 : ℕ)^37*50000000000000^29 ≤ 26979211500983^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6165841889 10000000000 26979211500983 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662609223/2000000000 : ℝ)^37 ≤ (12213677421861/50000000000000 : ℝ)^29 := by
    have hnat : (662609223 : ℕ)^37*50000000000000^29 ≤ 12213677421861^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662609223 2000000000 12213677421861 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1505045741/5000000000 : ℝ), (6165841889/10000000000 : ℝ), (-662609223/2000000000 : ℝ)] ![(5403555534469/25000000000000 : ℝ), (26979211500983/50000000000000 : ℝ), (12213677421861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1505045741/5000000000 : ℝ)|^37 ≤ (5403555534469/25000000000000 : ℝ)^29
        have hw : |(1505045741/5000000000 : ℝ)|=(1505045741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6165841889/10000000000 : ℝ)|^37 ≤ (26979211500983/50000000000000 : ℝ)^29
        have hw : |(6165841889/10000000000 : ℝ)|=(6165841889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-662609223/2000000000 : ℝ)|^37 ≤ (12213677421861/50000000000000 : ℝ)^29
        have hw : |(-662609223/2000000000 : ℝ)|=(662609223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312029_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2294365557/5000000000 : ℝ)*x 0 + (1970730513/5000000000 : ℝ)*x 1 + (207196047/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2294365557/5000000000 : ℝ)^37 ≤ (18507017595993/50000000000000 : ℝ)^29 := by
    have hnat : (2294365557 : ℕ)^37*50000000000000^29 ≤ 18507017595993^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294365557 5000000000 18507017595993 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1970730513/5000000000 : ℝ)^37 ≤ (6097395991057/20000000000000 : ℝ)^29 := by
    have hnat : (1970730513 : ℕ)^37*20000000000000^29 ≤ 6097395991057^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970730513 5000000000 6097395991057 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207196047/500000000 : ℝ)^37 ≤ (32498984834609/100000000000000 : ℝ)^29 := by
    have hnat : (207196047 : ℕ)^37*100000000000000^29 ≤ 32498984834609^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207196047 500000000 32498984834609 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2294365557/5000000000 : ℝ), (1970730513/5000000000 : ℝ), (207196047/500000000 : ℝ)] ![(18507017595993/50000000000000 : ℝ), (6097395991057/20000000000000 : ℝ), (32498984834609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2294365557/5000000000 : ℝ)|^37 ≤ (18507017595993/50000000000000 : ℝ)^29
        have hw : |(2294365557/5000000000 : ℝ)|=(2294365557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1970730513/5000000000 : ℝ)|^37 ≤ (6097395991057/20000000000000 : ℝ)^29
        have hw : |(1970730513/5000000000 : ℝ)|=(1970730513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207196047/500000000 : ℝ)|^37 ≤ (32498984834609/100000000000000 : ℝ)^29
        have hw : |(207196047/500000000 : ℝ)|=(207196047/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312029 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1971723679/5000000000 : ℝ)*X 0 0+(238620731/625000000 : ℝ)*X 0 1+(4897447833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((608059461/1000000000 : ℝ)*X 1 0+(-1012341907/10000000000 : ℝ)*X 1 1+(1005913677/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((952466561/5000000000 : ℝ)*X 2 0+(7734021339/10000000000 : ℝ)*X 2 1+(-924131/3906250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2108362493/5000000000 : ℝ)*X 0 0+(2905148443/10000000000 : ℝ)*X 0 1+(5451456967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1380271709/2500000000 : ℝ)*X 1 0+(-11049757/400000000 : ℝ)*X 1 1+(2999722613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1089851/15625000 : ℝ)*X 2 0+(1873643137/2000000000 : ℝ)*X 2 1+(-901746389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((4140182267/10000000000 : ℝ)*X 0 0+(4038353651/10000000000 : ℝ)*X 0 1+(4498896227/10000000000 : ℝ)*X 0 2+(4140182267/10000000000 : ℝ)*X 1 0+(4038353651/10000000000 : ℝ)*X 1 1+(4498896227/10000000000 : ℝ)*X 1 2+(4140182267/10000000000 : ℝ)*X 2 0+(4038353651/10000000000 : ℝ)*X 2 1+(4498896227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-4623131561/10000000000 : ℝ)*X 0 0+(325641927/1250000000 : ℝ)*X 0 1+(2657983613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((888804981/1250000000 : ℝ)*X 1 0+(-1244745737/10000000000 : ℝ)*X 1 1+(3715414987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((165808749/1250000000 : ℝ)*X 2 0+(7909410931/10000000000 : ℝ)*X 2 1+(-2637788257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((711207233/2500000000 : ℝ)*X 0 0+(1775975919/5000000000 : ℝ)*X 0 1+(381065337/625000000 : ℝ)*X 0 2+(711207233/2500000000 : ℝ)*X 1 0+(1775975919/5000000000 : ℝ)*X 1 1+(381065337/625000000 : ℝ)*X 1 2+(711207233/2500000000 : ℝ)*X 2 0+(1775975919/5000000000 : ℝ)*X 2 1+(381065337/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-2993160611/10000000000 : ℝ)*X 0 0+(760902163/2000000000 : ℝ)*X 0 1+(2876800491/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1928212889/2500000000 : ℝ)*X 1 0+(-140342301/5000000000 : ℝ)*X 1 1+(1799892299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((699563941/10000000000 : ℝ)*X 2 0+(1139982273/1250000000 : ℝ)*X 2 1+(-672368159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((839174727/1250000000 : ℝ)*X 0 0+(1252875369/5000000000 : ℝ)*X 0 1+(1566657019/5000000000 : ℝ)*X 0 2+(839174727/1250000000 : ℝ)*X 1 0+(1252875369/5000000000 : ℝ)*X 1 1+(1566657019/5000000000 : ℝ)*X 1 2+(839174727/1250000000 : ℝ)*X 2 0+(1252875369/5000000000 : ℝ)*X 2 1+(1566657019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((37403/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37403/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28955728174117893515511/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235353265411/500000000000 : ℝ)*(base50) + (310845313311/500000000000 : ℝ)*(base59) + (644678281633/250000000000 : ℝ)*(major_s0_0) + (505840441213/100000000000 : ℝ)*(major_s0_1) + (644678281633/250000000000 : ℝ)*(major_s0_2) + (69879379/500000000000 : ℝ)*(sp_s0_0) + (1239845642799/500000000000 : ℝ)*(sp_s0_4) + (3612297291837/1000000000000 : ℝ)*(sp_s0_7) + (3612477944269/1000000000000 : ℝ)*(sp_s0_8) + (722447148167/200000000000 : ℝ)*(sp_s0_9) + (772465059057/500000000000 : ℝ)*(sp_s0_12) + (20446837/500000000000 : ℝ)*(sp_s0_13) + (1791239/125000000000 : ℝ)*(sp_s0_19) + (121101717/500000000000 : ℝ)*(sp_s0_22) + (61797777921/40000000000 : ℝ)*(f.failure) + (3612477944269/1000000000000 : ℝ)*(f.sum) + (1984495241371817/2500000000000000000000000000 : ℝ)*base62 + (392539164462883/2500000000000000000000000000 : ℝ)*base64 + (952793395652537/1000000000000000000000000000 : ℝ)*base66 + (622303187017961/1250000000000000000000000000 : ℝ)*base68 + (780663999761/500000000000000000000000000 : ℝ)*base70 + (1402224682787117/2500000000000000000000000000 : ℝ)*base72 + (455379516467179/500000000000000000000000000 : ℝ)*base74 + (451462186392961/1250000000000000000000000000 : ℝ)*base76 + (4244356283836919/5000000000000000000000000000 : ℝ)*base78 + (127/4000000000000000 : ℝ)*base86 + (127/4000000000000000 : ℝ)*base88 + (127/4000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7327/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(7327/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17736401967857627736591/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3515991/250000000000 : ℝ)*(base3) + (234927421151/500000000000 : ℝ)*(base40) + (4911881/500000000000 : ℝ)*(base50) + (507812727051/1000000000000 : ℝ)*(base59) + (2095528156553/1000000000000 : ℝ)*(major_s0_0) + (2095528156553/1000000000000 : ℝ)*(major_s0_1) + (2095528156553/1000000000000 : ℝ)*(major_s0_2) + (26269959/500000000000 : ℝ)*(sp_s0_1) + (2109883/100000000000 : ℝ)*(sp_s0_2) + (2935592626143/1000000000000 : ℝ)*(sp_s0_13) + (733883924119/250000000000 : ℝ)*(sp_s0_14) + (2935571527313/1000000000000 : ℝ)*(sp_s0_15) + (1255447258133/1000000000000 : ℝ)*(sp_s0_19) + (18453713/1000000000000 : ℝ)*(sp_s0_21) + (1255461322097/1000000000000 : ℝ)*(f.failure) + (2935592626143/1000000000000 : ℝ)*(f.sum) + (3746295267/10000000000000000000000 : ℝ)*base63 + (5807489949662197/10000000000000000000000000000 : ℝ)*base65 + (10744968654337803/10000000000000000000000000000 : ℝ)*base67 + (3685522116910399/5000000000000000000000000000 : ℝ)*base69 + (421248530503401/2000000000000000000000000000 : ℝ)*base70 + (11433667356337803/10000000000000000000000000000 : ℝ)*base73 + (3975982021089601/5000000000000000000000000000 : ℝ)*base75 + (1993501509410399/5000000000000000000000000000 : ℝ)*base77 + (4587340660837803/5000000000000000000000000000 : ℝ)*base79 + (123439/100000000000000000 : ℝ)*base86 + (123439/100000000000000000 : ℝ)*base88 + (123439/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9919/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9919/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2619992507385035682897/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (413050845221/500000000000 : ℝ)*(base40) + (68410886227/200000000000 : ℝ)*(base50) + (32723995767/50000000000 : ℝ)*(base59) + (395369962041/125000000000 : ℝ)*(major_s0_0) + (232459498163/31250000000 : ℝ)*(major_s0_1) + (395369962041/125000000000 : ℝ)*(major_s0_2) + (23172221/200000000000 : ℝ)*(sp_s0_0) + (534468030611/125000000000 : ℝ)*(sp_s0_4) + (42211831/500000000000 : ℝ)*(sp_s0_14) + (6564053/1000000000000 : ℝ)*(sp_s0_15) + (4430822897549/1000000000000 : ℝ)*(sp_s0_20) + (4430854334991/1000000000000 : ℝ)*(sp_s0_21) + (4430932194601/1000000000000 : ℝ)*(sp_s0_22) + (1894975044681/1000000000000 : ℝ)*(sp_s0_25) + (1894975044681/1000000000000 : ℝ)*(f.failure) + (2215469379327/500000000000 : ℝ)*(f.sum) + (1922395713713/625000000000000000000000000 : ℝ)*base62 + (250527433331709/1250000000000000000000000000 : ℝ)*base65 + (50563676414337/312500000000000000000000000 : ℝ)*base66 + (229140856699903/625000000000000000000000000 : ℝ)*base69 + (172432080821303/250000000000000000000000000 : ℝ)*base71 + (345567931206709/1250000000000000000000000000 : ℝ)*base72 + (14458134786077/78125000000000000000000000 : ℝ)*base74 + (7093579387403/625000000000000000000000000 : ℝ)*base77 + (448573110364057/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (39753/100000000000000000 : ℝ)*base87 + (39753/100000000000000000 : ℝ)*base89 + (39753/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (37403/100000 : ℝ) ^ (9/2 : ℝ) ≤ (149619769268545791/12500000000000000000 : ℝ) := by
    have hpowers : (37403/100000 : ℝ)^9 ≤ (149619769268545791/12500000000000000000 : ℝ)^2 := by
      have hnat : (37403 : ℕ)^9*12500000000000000000^2 ≤ 149619769268545791^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37403 100000 149619769268545791 12500000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37403/100000 : ℝ)) (X := (149619769268545791/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12649619769268545791/12500000000000000000 : ℝ) ≤ (5013238063370289/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (12649619769268545791/12500000000000000000 : ℝ)^2 ≤ (5013238063370289/5000000000000000 : ℝ)^9 := by
      have hnat : (12649619769268545791 : ℕ)^2*5000000000000000^9 ≤ 5013238063370289^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12649619769268545791 12500000000000000000 5013238063370289 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013238063370289/5000000000000000 : ℝ)) (X := (12649619769268545791/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6399619769268545791/6250000000000000000 : ℝ) ≤ (5026354896946161/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (6399619769268545791/6250000000000000000 : ℝ)^2 ≤ (5026354896946161/5000000000000000 : ℝ)^9 := by
      have hnat : (6399619769268545791 : ℕ)^2*5000000000000000^9 ≤ 5026354896946161^9*6250000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6399619769268545791 6250000000000000000 5026354896946161 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026354896946161/5000000000000000 : ℝ)) (X := (6399619769268545791/6250000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13238063370289/1870150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(204950524623/29221093750000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (37403/100000 : ℝ)) (alpha := (13238063370289/1870150000000000 : ℝ)) (beta := (204950524623/29221093750000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37403/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13238063370289/1870150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(204950524623/29221093750000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7327/50000 : ℝ) ^ (9/2 : ℝ) ≤ (8826181353537639/50000000000000000000 : ℝ) := by
    have hpowers : (7327/50000 : ℝ)^9 ≤ (8826181353537639/50000000000000000000 : ℝ)^2 := by
      have hnat : (7327 : ℕ)^9*50000000000000000000^2 ≤ 8826181353537639^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7327 50000 8826181353537639 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7327/50000 : ℝ)) (X := (8826181353537639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50008826181353537639/50000000000000000000 : ℝ) ≤ (2000078449560147/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50008826181353537639/50000000000000000000 : ℝ)^2 ≤ (2000078449560147/2000000000000000 : ℝ)^9 := by
      have hnat : (50008826181353537639 : ℕ)^2*2000000000000000^9 ≤ 2000078449560147^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008826181353537639 50000000000000000000 2000078449560147 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000078449560147/2000000000000000 : ℝ)) (X := (50008826181353537639/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25008826181353537639/25000000000000000000 : ℝ) ≤ (2000156888352111/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25008826181353537639/25000000000000000000 : ℝ)^2 ≤ (2000156888352111/2000000000000000 : ℝ)^9 := by
      have hnat : (25008826181353537639 : ℕ)^2*2000000000000000^9 ≤ 2000156888352111^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008826181353537639 25000000000000000000 2000156888352111 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000156888352111/2000000000000000 : ℝ)) (X := (25008826181353537639/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(78449560147/293080000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(19609697991/73270000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (7327/50000 : ℝ)) (alpha := (78449560147/293080000000000 : ℝ)) (beta := (19609697991/73270000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (7327/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(78449560147/293080000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(19609697991/73270000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9919/20000 : ℝ) ^ (9/2 : ℝ) ≤ (2130298835788217643/50000000000000000000 : ℝ) := by
    have hpowers : (9919/20000 : ℝ)^9 ≤ (2130298835788217643/50000000000000000000 : ℝ)^2 := by
      have hnat : (9919 : ℕ)^9*50000000000000000000^2 ≤ 2130298835788217643^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9919 20000 2130298835788217643 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9919/20000 : ℝ)) (X := (2130298835788217643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (52130298835788217643/50000000000000000000 : ℝ) ≤ (5046574834726773/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (52130298835788217643/50000000000000000000 : ℝ)^2 ≤ (5046574834726773/5000000000000000 : ℝ)^9 := by
      have hnat : (52130298835788217643 : ℕ)^2*5000000000000000^9 ≤ 5046574834726773^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52130298835788217643 50000000000000000000 5046574834726773 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046574834726773/5000000000000000 : ℝ)) (X := (52130298835788217643/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (27130298835788217643/25000000000000000000 : ℝ) ≤ (407335365379539/400000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (27130298835788217643/25000000000000000000 : ℝ)^2 ≤ (407335365379539/400000000000000 : ℝ)^9 := by
      have hnat : (27130298835788217643 : ℕ)^2*400000000000000^9 ≤ 407335365379539^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27130298835788217643 25000000000000000000 407335365379539 400000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (407335365379539/400000000000000 : ℝ)) (X := (27130298835788217643/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(46574834726773/2479750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(90234465034929/4959500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (9919/20000 : ℝ)) (alpha := (46574834726773/2479750000000000 : ℝ)) (beta := (90234465034929/4959500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9919/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(46574834726773/2479750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(90234465034929/4959500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2020912749/5000000000 : ℝ)*X 0 0+(4188019841/10000000000 : ℝ)*X 0 1+(1112155091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2673040687/5000000000 : ℝ)*X 1 0+(-2322836669/10000000000 : ℝ)*X 1 1+(4827857201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1505045741/5000000000 : ℝ)*X 2 0+(6165841889/10000000000 : ℝ)*X 2 1+(-662609223/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2294365557/5000000000 : ℝ)*X 0 0+(1970730513/5000000000 : ℝ)*X 0 1+(207196047/500000000 : ℝ)*X 0 2+(2294365557/5000000000 : ℝ)*X 1 0+(1970730513/5000000000 : ℝ)*X 1 1+(207196047/500000000 : ℝ)*X 1 2+(2294365557/5000000000 : ℝ)*X 2 0+(1970730513/5000000000 : ℝ)*X 2 1+(207196047/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312029_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-94697873618836435741496451552630399/13591598078695000000000000000000000 : ℝ) := by norm_num
    linear_combination (687/125000000000 : ℝ)*(base11) + (181/200000000000 : ℝ)*(base16) + (3221/500000000000 : ℝ)*(base39) + (145193777293/1000000000000 : ℝ)*(base40) + (288718218917/1000000000000 : ℝ)*(base49) + (5107280693/10000000000 : ℝ)*(base50) + (1387/500000000000 : ℝ)*(base53) + (271963981101/1000000000000 : ℝ)*(base59) + (166913/100000 : ℝ)*(major_s1_0) + (166913/100000 : ℝ)*(major_s1_1) + (834564998613/500000000000 : ℝ)*(major_s1_2) + (580615273821/250000000000 : ℝ)*(sp_s1_0) + (18579688799/8000000000 : ℝ)*(sp_s1_1) + (1161230551777/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1161230551777/500000000000 : ℝ)*(f.sum) + (772576354370483323/9084564125000000000000000000000 : ℝ)*base63 + (301983694619377/2479750000000000000000000000 : ℝ)*base64 + (1296655921503/4579375000000000000000000 : ℝ)*base67 + (71708408159487/619937500000000000000000000 : ℝ)*base69 + (21383210150930263339/23187522312500000000000000000000 : ℝ)*base70 + (970030798603/2992240000000000000000000 : ℝ)*base73 + (4228442841461/18317500000000000000000000 : ℝ)*base75 + (2410277522459/187015000000000000000000000 : ℝ)*base76 + (172966146326091651/274051781000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p012_b014 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=29 := by omega
  rcases hc with rfl
  · exact collision_c312029 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b014 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
