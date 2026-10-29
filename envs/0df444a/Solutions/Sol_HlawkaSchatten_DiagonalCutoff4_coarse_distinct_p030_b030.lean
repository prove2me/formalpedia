-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:32:47.30198+00:00
-- url     : https://prove2.me/submissions/a4e8056e-bbe3-4d7c-b124-9607cacdb82c

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
theorem collision_support_c330059_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (577729589/2000000000 : ℝ)*x 0 + (-144432391/500000000 : ℝ)*x 1 + (6070033657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577729589/2000000000 : ℝ)^6 ≤ (11266876727493/50000000000000 : ℝ)^5 := by
    have hnat : (577729589 : ℕ)^6*50000000000000^5 ≤ 11266876727493^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577729589 2000000000 11266876727493 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144432391/500000000 : ℝ)^6 ≤ (11266876142433/50000000000000 : ℝ)^5 := by
    have hnat : (144432391 : ℕ)^6*50000000000000^5 ≤ 11266876142433^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144432391 500000000 11266876142433 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6070033657/10000000000 : ℝ)^6 ≤ (2746624712829/5000000000000 : ℝ)^5 := by
    have hnat : (6070033657 : ℕ)^6*5000000000000^5 ≤ 2746624712829^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6070033657 10000000000 2746624712829 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(577729589/2000000000 : ℝ), (-144432391/500000000 : ℝ), (6070033657/10000000000 : ℝ)] ![(11266876727493/50000000000000 : ℝ), (11266876142433/50000000000000 : ℝ), (2746624712829/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(577729589/2000000000 : ℝ)|^6 ≤ (11266876727493/50000000000000 : ℝ)^5
        have hw : |(577729589/2000000000 : ℝ)|=(577729589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144432391/500000000 : ℝ)|^6 ≤ (11266876142433/50000000000000 : ℝ)^5
        have hw : |(-144432391/500000000 : ℝ)|=(144432391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6070033657/10000000000 : ℝ)|^6 ≤ (2746624712829/5000000000000 : ℝ)^5
        have hw : |(6070033657/10000000000 : ℝ)|=(6070033657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (359927863/1250000000 : ℝ)*x 0 + (6276779447/10000000000 : ℝ)*x 1 + (531056991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359927863/1250000000 : ℝ)^6 ≤ (22447425860487/100000000000000 : ℝ)^5 := by
    have hnat : (359927863 : ℕ)^6*100000000000000^5 ≤ 22447425860487^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359927863 1250000000 22447425860487 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6276779447/10000000000 : ℝ)^6 ≤ (57185278754473/100000000000000 : ℝ)^5 := by
    have hnat : (6276779447 : ℕ)^6*100000000000000^5 ≤ 57185278754473^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6276779447 10000000000 57185278754473 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531056991/2000000000 : ℝ)^6 ≤ (2545911921437/12500000000000 : ℝ)^5 := by
    have hnat : (531056991 : ℕ)^6*12500000000000^5 ≤ 2545911921437^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531056991 2000000000 2545911921437 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(359927863/1250000000 : ℝ), (6276779447/10000000000 : ℝ), (531056991/2000000000 : ℝ)] ![(22447425860487/100000000000000 : ℝ), (57185278754473/100000000000000 : ℝ), (2545911921437/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(359927863/1250000000 : ℝ)|^6 ≤ (22447425860487/100000000000000 : ℝ)^5
        have hw : |(359927863/1250000000 : ℝ)|=(359927863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6276779447/10000000000 : ℝ)|^6 ≤ (57185278754473/100000000000000 : ℝ)^5
        have hw : |(6276779447/10000000000 : ℝ)|=(6276779447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531056991/2000000000 : ℝ)|^6 ≤ (2545911921437/12500000000000 : ℝ)^5
        have hw : |(531056991/2000000000 : ℝ)|=(531056991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-583213559/2500000000 : ℝ)*x 0 + (763445621/10000000000 : ℝ)*x 1 + (8129727967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583213559/2500000000 : ℝ)^6 ≤ (17436733273677/100000000000000 : ℝ)^5 := by
    have hnat : (583213559 : ℕ)^6*100000000000000^5 ≤ 17436733273677^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583213559 2500000000 17436733273677 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (763445621/10000000000 : ℝ)^6 ≤ (4563874885073/100000000000000 : ℝ)^5 := by
    have hnat : (763445621 : ℕ)^6*100000000000000^5 ≤ 4563874885073^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763445621 10000000000 4563874885073 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8129727967/10000000000 : ℝ)^6 ≤ (38999695911681/50000000000000 : ℝ)^5 := by
    have hnat : (8129727967 : ℕ)^6*50000000000000^5 ≤ 38999695911681^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8129727967 10000000000 38999695911681 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-583213559/2500000000 : ℝ), (763445621/10000000000 : ℝ), (8129727967/10000000000 : ℝ)] ![(17436733273677/100000000000000 : ℝ), (4563874885073/100000000000000 : ℝ), (38999695911681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-583213559/2500000000 : ℝ)|^6 ≤ (17436733273677/100000000000000 : ℝ)^5
        have hw : |(-583213559/2500000000 : ℝ)|=(583213559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(763445621/10000000000 : ℝ)|^6 ≤ (4563874885073/100000000000000 : ℝ)^5
        have hw : |(763445621/10000000000 : ℝ)|=(763445621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8129727967/10000000000 : ℝ)|^6 ≤ (38999695911681/50000000000000 : ℝ)^5
        have hw : |(8129727967/10000000000 : ℝ)|=(8129727967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1993940381/10000000000 : ℝ)*x 0 + (-116231807/1000000000 : ℝ)*x 1 + (1016215949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993940381/10000000000 : ℝ)^6 ≤ (7221453295463/50000000000000 : ℝ)^5 := by
    have hnat : (1993940381 : ℕ)^6*50000000000000^5 ≤ 7221453295463^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993940381 10000000000 7221453295463 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116231807/1000000000 : ℝ)^6 ≤ (7557705895501/100000000000000 : ℝ)^5 := by
    have hnat : (116231807 : ℕ)^6*100000000000000^5 ≤ 7557705895501^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116231807 1000000000 7557705895501 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016215949/1250000000 : ℝ)^6 ≤ (19499846876477/25000000000000 : ℝ)^5 := by
    have hnat : (1016215949 : ℕ)^6*25000000000000^5 ≤ 19499846876477^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016215949 1250000000 19499846876477 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1993940381/10000000000 : ℝ), (-116231807/1000000000 : ℝ), (1016215949/1250000000 : ℝ)] ![(7221453295463/50000000000000 : ℝ), (7557705895501/100000000000000 : ℝ), (19499846876477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1993940381/10000000000 : ℝ)|^6 ≤ (7221453295463/50000000000000 : ℝ)^5
        have hw : |(1993940381/10000000000 : ℝ)|=(1993940381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116231807/1000000000 : ℝ)|^6 ≤ (7557705895501/100000000000000 : ℝ)^5
        have hw : |(-116231807/1000000000 : ℝ)|=(116231807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016215949/1250000000 : ℝ)|^6 ≤ (19499846876477/25000000000000 : ℝ)^5
        have hw : |(1016215949/1250000000 : ℝ)|=(1016215949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4182115321/10000000000 : ℝ)*x 0 + (6971461643/10000000000 : ℝ)*x 1 + (-4052027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182115321/10000000000 : ℝ)^6 ≤ (7025952360673/20000000000000 : ℝ)^5 := by
    have hnat : (4182115321 : ℕ)^6*20000000000000^5 ≤ 7025952360673^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182115321 10000000000 7025952360673 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6971461643/10000000000 : ℝ)^6 ≤ (2594469693563/4000000000000 : ℝ)^5 := by
    have hnat : (6971461643 : ℕ)^6*4000000000000^5 ≤ 2594469693563^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6971461643 10000000000 2594469693563 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052027/10000000000 : ℝ)^6 ≤ (849584923/10000000000000 : ℝ)^5 := by
    have hnat : (4052027 : ℕ)^6*10000000000000^5 ≤ 849584923^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052027 10000000000 849584923 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182115321/10000000000 : ℝ), (6971461643/10000000000 : ℝ), (-4052027/10000000000 : ℝ)] ![(7025952360673/20000000000000 : ℝ), (2594469693563/4000000000000 : ℝ), (849584923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182115321/10000000000 : ℝ)|^6 ≤ (7025952360673/20000000000000 : ℝ)^5
        have hw : |(4182115321/10000000000 : ℝ)|=(4182115321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6971461643/10000000000 : ℝ)|^6 ≤ (2594469693563/4000000000000 : ℝ)^5
        have hw : |(6971461643/10000000000 : ℝ)|=(6971461643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4052027/10000000000 : ℝ)|^6 ≤ (849584923/10000000000000 : ℝ)^5
        have hw : |(-4052027/10000000000 : ℝ)|=(4052027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (529003573/2500000000 : ℝ)*x 0 + (1591668603/2000000000 : ℝ)*x 1 + (1276760579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529003573/2500000000 : ℝ)^6 ≤ (15510375642459/100000000000000 : ℝ)^5 := by
    have hnat : (529003573 : ℕ)^6*100000000000000^5 ≤ 15510375642459^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529003573 2500000000 15510375642459 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1591668603/2000000000 : ℝ)^6 ≤ (76030384123221/100000000000000 : ℝ)^5 := by
    have hnat : (1591668603 : ℕ)^6*100000000000000^5 ≤ 76030384123221^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591668603 2000000000 76030384123221 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1276760579/10000000000 : ℝ)^6 ≤ (132175628463/1562500000000 : ℝ)^5 := by
    have hnat : (1276760579 : ℕ)^6*1562500000000^5 ≤ 132175628463^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276760579 10000000000 132175628463 1562500000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529003573/2500000000 : ℝ), (1591668603/2000000000 : ℝ), (1276760579/10000000000 : ℝ)] ![(15510375642459/100000000000000 : ℝ), (76030384123221/100000000000000 : ℝ), (132175628463/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529003573/2500000000 : ℝ)|^6 ≤ (15510375642459/100000000000000 : ℝ)^5
        have hw : |(529003573/2500000000 : ℝ)|=(529003573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1591668603/2000000000 : ℝ)|^6 ≤ (76030384123221/100000000000000 : ℝ)^5
        have hw : |(1591668603/2000000000 : ℝ)|=(1591668603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1276760579/10000000000 : ℝ)|^6 ≤ (132175628463/1562500000000 : ℝ)^5
        have hw : |(1276760579/10000000000 : ℝ)|=(1276760579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-136522301/1250000000 : ℝ)*x 0 + (543058991/2500000000 : ℝ)*x 1 + (8041090981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136522301/1250000000 : ℝ)^6 ≤ (3506891327463/50000000000000 : ℝ)^5 := by
    have hnat : (136522301 : ℕ)^6*50000000000000^5 ≤ 3506891327463^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136522301 1250000000 3506891327463 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543058991/2500000000 : ℝ)^6 ≤ (8003102956907/50000000000000 : ℝ)^5 := by
    have hnat : (543058991 : ℕ)^6*50000000000000^5 ≤ 8003102956907^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543058991 2500000000 8003102956907 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8041090981/10000000000 : ℝ)^6 ≤ (19245002854169/25000000000000 : ℝ)^5 := by
    have hnat : (8041090981 : ℕ)^6*25000000000000^5 ≤ 19245002854169^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8041090981 10000000000 19245002854169 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136522301/1250000000 : ℝ), (543058991/2500000000 : ℝ), (8041090981/10000000000 : ℝ)] ![(3506891327463/50000000000000 : ℝ), (8003102956907/50000000000000 : ℝ), (19245002854169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136522301/1250000000 : ℝ)|^6 ≤ (3506891327463/50000000000000 : ℝ)^5
        have hw : |(-136522301/1250000000 : ℝ)|=(136522301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543058991/2500000000 : ℝ)|^6 ≤ (8003102956907/50000000000000 : ℝ)^5
        have hw : |(543058991/2500000000 : ℝ)|=(543058991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8041090981/10000000000 : ℝ)|^6 ≤ (19245002854169/25000000000000 : ℝ)^5
        have hw : |(8041090981/10000000000 : ℝ)|=(8041090981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1015461021/10000000000 : ℝ)*x 0 + (-223841773/1000000000 : ℝ)*x 1 + (1005136393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015461021/10000000000 : ℝ)^6 ≤ (803352079003/12500000000000 : ℝ)^5 := by
    have hnat : (1015461021 : ℕ)^6*12500000000000^5 ≤ 803352079003^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015461021 10000000000 803352079003 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223841773/1000000000 : ℝ)^6 ≤ (16593170072409/100000000000000 : ℝ)^5 := by
    have hnat : (223841773 : ℕ)^6*100000000000000^5 ≤ 16593170072409^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223841773 1000000000 16593170072409 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005136393/1250000000 : ℝ)^6 ≤ (76980013289219/100000000000000 : ℝ)^5 := by
    have hnat : (1005136393 : ℕ)^6*100000000000000^5 ≤ 76980013289219^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005136393 1250000000 76980013289219 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1015461021/10000000000 : ℝ), (-223841773/1000000000 : ℝ), (1005136393/1250000000 : ℝ)] ![(803352079003/12500000000000 : ℝ), (16593170072409/100000000000000 : ℝ), (76980013289219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1015461021/10000000000 : ℝ)|^6 ≤ (803352079003/12500000000000 : ℝ)^5
        have hw : |(1015461021/10000000000 : ℝ)|=(1015461021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223841773/1000000000 : ℝ)|^6 ≤ (16593170072409/100000000000000 : ℝ)^5
        have hw : |(-223841773/1000000000 : ℝ)|=(223841773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005136393/1250000000 : ℝ)|^6 ≤ (76980013289219/100000000000000 : ℝ)^5
        have hw : |(1005136393/1250000000 : ℝ)|=(1005136393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4077265699/5000000000 : ℝ)*x 0 + (560144223/2000000000 : ℝ)*x 1 + (-217599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4077265699/5000000000 : ℝ)^6 ≤ (78285046002463/100000000000000 : ℝ)^5 := by
    have hnat : (4077265699 : ℕ)^6*100000000000000^5 ≤ 78285046002463^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077265699 5000000000 78285046002463 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560144223/2000000000 : ℝ)^6 ≤ (10856600151643/50000000000000 : ℝ)^5 := by
    have hnat : (560144223 : ℕ)^6*50000000000000^5 ≤ 10856600151643^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560144223 2000000000 10856600151643 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217599/2000000000 : ℝ)^6 ≤ (350737559/20000000000000 : ℝ)^5 := by
    have hnat : (217599 : ℕ)^6*20000000000000^5 ≤ 350737559^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217599 2000000000 350737559 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4077265699/5000000000 : ℝ), (560144223/2000000000 : ℝ), (-217599/2000000000 : ℝ)] ![(78285046002463/100000000000000 : ℝ), (10856600151643/50000000000000 : ℝ), (350737559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4077265699/5000000000 : ℝ)|^6 ≤ (78285046002463/100000000000000 : ℝ)^5
        have hw : |(4077265699/5000000000 : ℝ)|=(4077265699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560144223/2000000000 : ℝ)|^6 ≤ (10856600151643/50000000000000 : ℝ)^5
        have hw : |(560144223/2000000000 : ℝ)|=(560144223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217599/2000000000 : ℝ)|^6 ≤ (350737559/20000000000000 : ℝ)^5
        have hw : |(-217599/2000000000 : ℝ)|=(217599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (25439787/39062500 : ℝ)*x 0 + (3650895161/10000000000 : ℝ)*x 1 + (1514329283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25439787/39062500 : ℝ)^6 ≤ (59772871964327/100000000000000 : ℝ)^5 := by
    have hnat : (25439787 : ℕ)^6*100000000000000^5 ≤ 59772871964327^5*39062500^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25439787 39062500 59772871964327 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3650895161/10000000000 : ℝ)^6 ≤ (7461381448329/25000000000000 : ℝ)^5 := by
    have hnat : (3650895161 : ℕ)^6*25000000000000^5 ≤ 7461381448329^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650895161 10000000000 7461381448329 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514329283/10000000000 : ℝ)^6 ≤ (5190801111267/50000000000000 : ℝ)^5 := by
    have hnat : (1514329283 : ℕ)^6*50000000000000^5 ≤ 5190801111267^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514329283 10000000000 5190801111267 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25439787/39062500 : ℝ), (3650895161/10000000000 : ℝ), (1514329283/10000000000 : ℝ)] ![(59772871964327/100000000000000 : ℝ), (7461381448329/25000000000000 : ℝ), (5190801111267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25439787/39062500 : ℝ)|^6 ≤ (59772871964327/100000000000000 : ℝ)^5
        have hw : |(25439787/39062500 : ℝ)|=(25439787/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3650895161/10000000000 : ℝ)|^6 ≤ (7461381448329/25000000000000 : ℝ)^5
        have hw : |(3650895161/10000000000 : ℝ)|=(3650895161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1514329283/10000000000 : ℝ)|^6 ≤ (5190801111267/50000000000000 : ℝ)^5
        have hw : |(1514329283/10000000000 : ℝ)|=(1514329283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-4331884219/10000000000 : ℝ)*x 0 + (1200143849/5000000000 : ℝ)*x 1 + (5170235561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331884219/10000000000 : ℝ)^6 ≤ (18322393789469/50000000000000 : ℝ)^5 := by
    have hnat : (4331884219 : ℕ)^6*50000000000000^5 ≤ 18322393789469^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331884219 10000000000 18322393789469 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200143849/5000000000 : ℝ)^6 ≤ (3608659909293/20000000000000 : ℝ)^5 := by
    have hnat : (1200143849 : ℕ)^6*20000000000000^5 ≤ 3608659909293^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200143849 5000000000 3608659909293 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170235561/10000000000 : ℝ)^6 ≤ (9062382572751/20000000000000 : ℝ)^5 := by
    have hnat : (5170235561 : ℕ)^6*20000000000000^5 ≤ 9062382572751^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170235561 10000000000 9062382572751 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4331884219/10000000000 : ℝ), (1200143849/5000000000 : ℝ), (5170235561/10000000000 : ℝ)] ![(18322393789469/50000000000000 : ℝ), (3608659909293/20000000000000 : ℝ), (9062382572751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4331884219/10000000000 : ℝ)|^6 ≤ (18322393789469/50000000000000 : ℝ)^5
        have hw : |(-4331884219/10000000000 : ℝ)|=(4331884219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200143849/5000000000 : ℝ)|^6 ≤ (3608659909293/20000000000000 : ℝ)^5
        have hw : |(1200143849/5000000000 : ℝ)|=(1200143849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170235561/10000000000 : ℝ)|^6 ≤ (9062382572751/20000000000000 : ℝ)^5
        have hw : |(5170235561/10000000000 : ℝ)|=(5170235561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1011539057/5000000000 : ℝ)*x 0 + (-3456011867/10000000000 : ℝ)*x 1 + (6292697261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011539057/5000000000 : ℝ)^6 ≤ (14696542747291/100000000000000 : ℝ)^5 := by
    have hnat : (1011539057 : ℕ)^6*100000000000000^5 ≤ 14696542747291^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011539057 5000000000 14696542747291 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3456011867/10000000000 : ℝ)^6 ≤ (3493013652417/12500000000000 : ℝ)^5 := by
    have hnat : (3456011867 : ℕ)^6*12500000000000^5 ≤ 3493013652417^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3456011867 10000000000 3493013652417 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6292697261/10000000000 : ℝ)^6 ≤ (57359348018659/100000000000000 : ℝ)^5 := by
    have hnat : (6292697261 : ℕ)^6*100000000000000^5 ≤ 57359348018659^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6292697261 10000000000 57359348018659 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1011539057/5000000000 : ℝ), (-3456011867/10000000000 : ℝ), (6292697261/10000000000 : ℝ)] ![(14696542747291/100000000000000 : ℝ), (3493013652417/12500000000000 : ℝ), (57359348018659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1011539057/5000000000 : ℝ)|^6 ≤ (14696542747291/100000000000000 : ℝ)^5
        have hw : |(1011539057/5000000000 : ℝ)|=(1011539057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3456011867/10000000000 : ℝ)|^6 ≤ (3493013652417/12500000000000 : ℝ)^5
        have hw : |(-3456011867/10000000000 : ℝ)|=(3456011867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6292697261/10000000000 : ℝ)|^6 ≤ (57359348018659/100000000000000 : ℝ)^5
        have hw : |(6292697261/10000000000 : ℝ)|=(6292697261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (8212327767/10000000000 : ℝ)*x 0 + (2728893631/10000000000 : ℝ)*x 1 + (-238691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8212327767/10000000000 : ℝ)^6 ≤ (78951344335477/100000000000000 : ℝ)^5 := by
    have hnat : (8212327767 : ℕ)^6*100000000000000^5 ≤ 78951344335477^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8212327767 10000000000 78951344335477 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728893631/10000000000 : ℝ)^6 ≤ (21046696055329/100000000000000 : ℝ)^5 := by
    have hnat : (2728893631 : ℕ)^6*100000000000000^5 ≤ 21046696055329^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728893631 10000000000 21046696055329 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238691/2000000000 : ℝ)^6 ≤ (1959599221/100000000000000 : ℝ)^5 := by
    have hnat : (238691 : ℕ)^6*100000000000000^5 ≤ 1959599221^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238691 2000000000 1959599221 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8212327767/10000000000 : ℝ), (2728893631/10000000000 : ℝ), (-238691/2000000000 : ℝ)] ![(78951344335477/100000000000000 : ℝ), (21046696055329/100000000000000 : ℝ), (1959599221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8212327767/10000000000 : ℝ)|^6 ≤ (78951344335477/100000000000000 : ℝ)^5
        have hw : |(8212327767/10000000000 : ℝ)|=(8212327767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728893631/10000000000 : ℝ)|^6 ≤ (21046696055329/100000000000000 : ℝ)^5
        have hw : |(2728893631/10000000000 : ℝ)|=(2728893631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238691/2000000000 : ℝ)|^6 ≤ (1959599221/100000000000000 : ℝ)^5
        have hw : |(-238691/2000000000 : ℝ)|=(238691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (164281963/2000000000 : ℝ)*x 0 + (443817267/500000000 : ℝ)*x 1 + (63117379/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164281963/2000000000 : ℝ)^6 ≤ (1245695438581/25000000000000 : ℝ)^5 := by
    have hnat : (164281963 : ℕ)^6*25000000000000^5 ≤ 1245695438581^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164281963 2000000000 1245695438581 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443817267/500000000 : ℝ)^6 ≤ (3466897643879/4000000000000 : ℝ)^5 := by
    have hnat : (443817267 : ℕ)^6*4000000000000^5 ≤ 3466897643879^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443817267 500000000 3466897643879 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63117379/500000000 : ℝ)^6 ≤ (8344777130399/100000000000000 : ℝ)^5 := by
    have hnat : (63117379 : ℕ)^6*100000000000000^5 ≤ 8344777130399^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63117379 500000000 8344777130399 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164281963/2000000000 : ℝ), (443817267/500000000 : ℝ), (63117379/500000000 : ℝ)] ![(1245695438581/25000000000000 : ℝ), (3466897643879/4000000000000 : ℝ), (8344777130399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164281963/2000000000 : ℝ)|^6 ≤ (1245695438581/25000000000000 : ℝ)^5
        have hw : |(164281963/2000000000 : ℝ)|=(164281963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443817267/500000000 : ℝ)|^6 ≤ (3466897643879/4000000000000 : ℝ)^5
        have hw : |(443817267/500000000 : ℝ)|=(443817267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63117379/500000000 : ℝ)|^6 ≤ (8344777130399/100000000000000 : ℝ)^5
        have hw : |(63117379/500000000 : ℝ)|=(63117379/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-3200224117/10000000000 : ℝ)*x 0 + (159974269/500000000 : ℝ)*x 1 + (2761421567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3200224117/10000000000 : ℝ)^6 ≤ (5096200054491/20000000000000 : ℝ)^5 := by
    have hnat : (3200224117 : ℕ)^6*20000000000000^5 ≤ 5096200054491^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3200224117 10000000000 5096200054491 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159974269/500000000 : ℝ)^6 ≤ (25473942020611/100000000000000 : ℝ)^5 := by
    have hnat : (159974269 : ℕ)^6*100000000000000^5 ≤ 25473942020611^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159974269 500000000 25473942020611 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761421567/5000000000 : ℝ)^6 ≤ (24522528843791/50000000000000 : ℝ)^5 := by
    have hnat : (2761421567 : ℕ)^6*50000000000000^5 ≤ 24522528843791^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761421567 5000000000 24522528843791 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3200224117/10000000000 : ℝ), (159974269/500000000 : ℝ), (2761421567/5000000000 : ℝ)] ![(5096200054491/20000000000000 : ℝ), (25473942020611/100000000000000 : ℝ), (24522528843791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3200224117/10000000000 : ℝ)|^6 ≤ (5096200054491/20000000000000 : ℝ)^5
        have hw : |(-3200224117/10000000000 : ℝ)|=(3200224117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(159974269/500000000 : ℝ)|^6 ≤ (25473942020611/100000000000000 : ℝ)^5
        have hw : |(159974269/500000000 : ℝ)|=(159974269/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2761421567/5000000000 : ℝ)|^6 ≤ (24522528843791/50000000000000 : ℝ)^5
        have hw : |(2761421567/5000000000 : ℝ)|=(2761421567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3199458631/10000000000 : ℝ)*x 0 + (-639743607/2000000000 : ℝ)*x 1 + (5524217387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3199458631/10000000000 : ℝ)^6 ≤ (25473686453797/100000000000000 : ℝ)^5 := by
    have hnat : (3199458631 : ℕ)^6*100000000000000^5 ≤ 25473686453797^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3199458631 10000000000 25473686453797 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639743607/2000000000 : ℝ)^6 ≤ (636665269479/2500000000000 : ℝ)^5 := by
    have hnat : (639743607 : ℕ)^6*2500000000000^5 ≤ 636665269479^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639743607 2000000000 636665269479 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5524217387/10000000000 : ℝ)^6 ≤ (49059702752027/100000000000000 : ℝ)^5 := by
    have hnat : (5524217387 : ℕ)^6*100000000000000^5 ≤ 49059702752027^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524217387 10000000000 49059702752027 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3199458631/10000000000 : ℝ), (-639743607/2000000000 : ℝ), (5524217387/10000000000 : ℝ)] ![(25473686453797/100000000000000 : ℝ), (636665269479/2500000000000 : ℝ), (49059702752027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3199458631/10000000000 : ℝ)|^6 ≤ (25473686453797/100000000000000 : ℝ)^5
        have hw : |(3199458631/10000000000 : ℝ)|=(3199458631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639743607/2000000000 : ℝ)|^6 ≤ (636665269479/2500000000000 : ℝ)^5
        have hw : |(-639743607/2000000000 : ℝ)|=(639743607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5524217387/10000000000 : ℝ)|^6 ≤ (49059702752027/100000000000000 : ℝ)^5
        have hw : |(5524217387/10000000000 : ℝ)|=(5524217387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5368170007/10000000000 : ℝ)*x 0 + (5349299851/10000000000 : ℝ)*x 1 + (-877931557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368170007/10000000000 : ℝ)^6 ≤ (47401437627831/100000000000000 : ℝ)^5 := by
    have hnat : (5368170007 : ℕ)^6*100000000000000^5 ≤ 47401437627831^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368170007 10000000000 47401437627831 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5349299851/10000000000 : ℝ)^6 ≤ (23600778856511/50000000000000 : ℝ)^5 := by
    have hnat : (5349299851 : ℕ)^6*50000000000000^5 ≤ 23600778856511^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349299851 10000000000 23600778856511 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877931557/10000000000 : ℝ)^6 ≤ (5270512349/97656250000 : ℝ)^5 := by
    have hnat : (877931557 : ℕ)^6*97656250000^5 ≤ 5270512349^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877931557 10000000000 5270512349 97656250000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368170007/10000000000 : ℝ), (5349299851/10000000000 : ℝ), (-877931557/10000000000 : ℝ)] ![(47401437627831/100000000000000 : ℝ), (23600778856511/50000000000000 : ℝ), (5270512349/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368170007/10000000000 : ℝ)|^6 ≤ (47401437627831/100000000000000 : ℝ)^5
        have hw : |(5368170007/10000000000 : ℝ)|=(5368170007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5349299851/10000000000 : ℝ)|^6 ≤ (23600778856511/50000000000000 : ℝ)^5
        have hw : |(5349299851/10000000000 : ℝ)|=(5349299851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-877931557/10000000000 : ℝ)|^6 ≤ (5270512349/97656250000 : ℝ)^5
        have hw : |(-877931557/10000000000 : ℝ)|=(877931557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330059_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4161520873/10000000000 : ℝ)*x 0 + (4233092711/10000000000 : ℝ)*x 1 + (3608844173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161520873/10000000000 : ℝ)^6 ≤ (6984454433919/20000000000000 : ℝ)^5 := by
    have hnat : (4161520873 : ℕ)^6*20000000000000^5 ≤ 6984454433919^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161520873 10000000000 6984454433919 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233092711/10000000000 : ℝ)^6 ≤ (35644238122549/100000000000000 : ℝ)^5 := by
    have hnat : (4233092711 : ℕ)^6*100000000000000^5 ≤ 35644238122549^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233092711 10000000000 35644238122549 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3608844173/10000000000 : ℝ)^6 ≤ (29433489693219/100000000000000 : ℝ)^5 := by
    have hnat : (3608844173 : ℕ)^6*100000000000000^5 ≤ 29433489693219^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3608844173 10000000000 29433489693219 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161520873/10000000000 : ℝ), (4233092711/10000000000 : ℝ), (3608844173/10000000000 : ℝ)] ![(6984454433919/20000000000000 : ℝ), (35644238122549/100000000000000 : ℝ), (29433489693219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161520873/10000000000 : ℝ)|^6 ≤ (6984454433919/20000000000000 : ℝ)^5
        have hw : |(4161520873/10000000000 : ℝ)|=(4161520873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233092711/10000000000 : ℝ)|^6 ≤ (35644238122549/100000000000000 : ℝ)^5
        have hw : |(4233092711/10000000000 : ℝ)|=(4233092711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3608844173/10000000000 : ℝ)|^6 ≤ (29433489693219/100000000000000 : ℝ)^5
        have hw : |(3608844173/10000000000 : ℝ)|=(3608844173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330059 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
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
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((577729589/2000000000 : ℝ)*X 1 0+(-144432391/500000000 : ℝ)*X 1 1+(6070033657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((359927863/1250000000 : ℝ)*X 0 0+(6276779447/10000000000 : ℝ)*X 0 1+(531056991/2000000000 : ℝ)*X 0 2+(359927863/1250000000 : ℝ)*X 1 0+(6276779447/10000000000 : ℝ)*X 1 1+(531056991/2000000000 : ℝ)*X 1 2+(359927863/1250000000 : ℝ)*X 2 0+(6276779447/10000000000 : ℝ)*X 2 1+(531056991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-583213559/2500000000 : ℝ)*X 0 0+(763445621/10000000000 : ℝ)*X 0 1+(8129727967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1993940381/10000000000 : ℝ)*X 1 0+(-116231807/1000000000 : ℝ)*X 1 1+(1016215949/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4182115321/10000000000 : ℝ)*X 2 0+(6971461643/10000000000 : ℝ)*X 2 1+(-4052027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((529003573/2500000000 : ℝ)*X 0 0+(1591668603/2000000000 : ℝ)*X 0 1+(1276760579/10000000000 : ℝ)*X 0 2+(529003573/2500000000 : ℝ)*X 1 0+(1591668603/2000000000 : ℝ)*X 1 1+(1276760579/10000000000 : ℝ)*X 1 2+(529003573/2500000000 : ℝ)*X 2 0+(1591668603/2000000000 : ℝ)*X 2 1+(1276760579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-136522301/1250000000 : ℝ)*X 0 0+(543058991/2500000000 : ℝ)*X 0 1+(8041090981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1015461021/10000000000 : ℝ)*X 1 0+(-223841773/1000000000 : ℝ)*X 1 1+(1005136393/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4077265699/5000000000 : ℝ)*X 2 0+(560144223/2000000000 : ℝ)*X 2 1+(-217599/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((25439787/39062500 : ℝ)*X 0 0+(3650895161/10000000000 : ℝ)*X 0 1+(1514329283/10000000000 : ℝ)*X 0 2+(25439787/39062500 : ℝ)*X 1 0+(3650895161/10000000000 : ℝ)*X 1 1+(1514329283/10000000000 : ℝ)*X 1 2+(25439787/39062500 : ℝ)*X 2 0+(3650895161/10000000000 : ℝ)*X 2 1+(1514329283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4331884219/10000000000 : ℝ)*X 0 0+(1200143849/5000000000 : ℝ)*X 0 1+(5170235561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1011539057/5000000000 : ℝ)*X 1 0+(-3456011867/10000000000 : ℝ)*X 1 1+(6292697261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8212327767/10000000000 : ℝ)*X 2 0+(2728893631/10000000000 : ℝ)*X 2 1+(-238691/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((164281963/2000000000 : ℝ)*X 0 0+(443817267/500000000 : ℝ)*X 0 1+(63117379/500000000 : ℝ)*X 0 2+(164281963/2000000000 : ℝ)*X 1 0+(443817267/500000000 : ℝ)*X 1 1+(63117379/500000000 : ℝ)*X 1 2+(164281963/2000000000 : ℝ)*X 2 0+(443817267/500000000 : ℝ)*X 2 1+(63117379/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((11743/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11743/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13486973761181923433811/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1228623482433/1000000000000 : ℝ)*(base7) + (37187/500000000000 : ℝ)*(base50) + (191197/1000000000000 : ℝ)*(base53) + (17369/1000000000000 : ℝ)*(base60) + (151926160589/100000000000 : ℝ)*(major_s0_0) + (151926160589/100000000000 : ℝ)*(major_s0_1) + (1519261414693/1000000000000 : ℝ)*(major_s0_2) + (1380819/500000000000 : ℝ)*(sp_s0_6) + (171947104197/100000000000 : ℝ)*(sp_s0_7) + (107467919219/62500000000 : ℝ)*(sp_s0_8) + (859743449351/500000000000 : ℝ)*(sp_s0_9) + (947837765801/500000000000 : ℝ)*(sp_s0_13) + (7832767/500000000000 : ℝ)*(sp_s0_14) + (10653047/1000000000000 : ℝ)*(sp_s0_27) + (333532731927/500000000000 : ℝ)*(f.failure) + (859743449351/500000000000 : ℝ)*(f.sum) + (3445365073513603/10000000000000000000000000000 : ℝ)*base62 + (9587295558660413/10000000000000000000000000000 : ℝ)*base64 + (61215902181851/1000000000000000000000000000 : ℝ)*base67 + (7607687411143493/10000000000000000000000000000 : ℝ)*base68 + (6061591611030523/10000000000000000000000000000 : ℝ)*base70 + (240963249781851/1000000000000000000000000000 : ℝ)*base73 + (384595366137011/1000000000000000000000000000 : ℝ)*base74 + (777352406037011/1000000000000000000000000000 : ℝ)*base76 + (112725760318149/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (70031/50000000000000000 : ℝ)*base87 + (70031/50000000000000000 : ℝ)*base89 + (70031/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58481/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29438961020066598286089/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136694357407/500000000000 : ℝ)*(base5) + (247102237173/200000000000 : ℝ)*(base7) + (283627/500000000000 : ℝ)*(base13) + (5996972687/50000000000 : ℝ)*(base60) + (787504871643/500000000000 : ℝ)*(major_s0_0) + (787504871643/500000000000 : ℝ)*(major_s0_1) + (787504871643/500000000000 : ℝ)*(major_s0_2) + (141881/100000000000 : ℝ)*(sp_s0_1) + (20386029/500000000000 : ℝ)*(sp_s0_8) + (1802848064787/1000000000000 : ℝ)*(sp_s0_14) + (450701610293/250000000000 : ℝ)*(sp_s0_15) + (103796083441/50000000000 : ℝ)*(sp_s0_16) + (1653665389601/1000000000000 : ℝ)*(sp_s0_20) + (63135607/200000000000 : ℝ)*(sp_s0_23) + (13830858371/20000000000 : ℝ)*(f.failure) + (1802848632041/1000000000000 : ℝ)*(f.sum) + (31755303/1250000000000000000000 : ℝ)*base63 + (602906770404637/5000000000000000000000000000 : ℝ)*base65 + (823769080095363/5000000000000000000000000000 : ℝ)*base66 + (1378959460279557/5000000000000000000000000000 : ℝ)*base69 + (21068709046873/125000000000000000000000000 : ℝ)*base70 + (3358777306404637/5000000000000000000000000000 : ℝ)*base73 + (498971685220443/5000000000000000000000000000 : ℝ)*base75 + (1180339050720443/5000000000000000000000000000 : ℝ)*base77 + (199689670404637/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1637/2000000000000000 : ℝ)*base86 + (1637/2000000000000000 : ℝ)*base88 + (1637/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(19417/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(19417/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57559337697944016212481/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (691911849069/1000000000000 : ℝ)*(base7) + (9989961/1000000000000 : ℝ)*(base8) + (71711/25000000000 : ℝ)*(base11) + (227041322907/1000000000000 : ℝ)*(base44) + (52322373729/500000000000 : ℝ)*(base50) + (1750802516969/1000000000000 : ℝ)*(major_s0_0) + (761880597031/500000000000 : ℝ)*(major_s0_1) + (1750802516969/1000000000000 : ℝ)*(major_s0_2) + (23247263/1000000000000 : ℝ)*(sp_s0_1) + (15710713/500000000000 : ℝ)*(sp_s0_13) + (2365696685409/1000000000000 : ℝ)*(sp_s0_21) + (2138644973641/1000000000000 : ℝ)*(sp_s0_22) + (236570954381/100000000000 : ℝ)*(sp_s0_23) + (1233567734861/1000000000000 : ℝ)*(sp_s0_27) + (6149829041/8000000000 : ℝ)*(f.failure) + (236570954381/100000000000 : ℝ)*(f.sum) + (3653411623245893/10000000000000000000000000000 : ℝ)*base63 + (3282527186490271/10000000000000000000000000000 : ℝ)*base65 + (529701231664271/5000000000000000000000000000 : ℝ)*base66 + (270963479927369/10000000000000000000000000000 : ℝ)*base68 + (64912620985441/250000000000000000000000000 : ℝ)*base71 + (3096117327509729/10000000000000000000000000000 : ℝ)*base72 + (2981921773086631/5000000000000000000000000000 : ℝ)*base75 + (985253523927369/10000000000000000000000000000 : ℝ)*base77 + (2207346665838271/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (327/800000000000000 : ℝ)*base86 + (327/800000000000000 : ℝ)*base88 + (327/800000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (11743/20000 : ℝ) ^ (95/16 : ℝ) ≤ (423591829648463429/10000000000000000000 : ℝ) := by
    have hpowers : (11743/20000 : ℝ)^95 ≤ (423591829648463429/10000000000000000000 : ℝ)^16 := by
      have hnat : (11743 : ℕ)^95*10000000000000000000^16 ≤ 423591829648463429^16*20000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11743 20000 423591829648463429 10000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11743/20000 : ℝ)) (X := (423591829648463429/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10423591829648463429/10000000000000000000 : ℝ) ≤ (1258764603220173/1250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (10423591829648463429/10000000000000000000 : ℝ)^16 ≤ (1258764603220173/1250000000000000 : ℝ)^95 := by
      have hnat : (10423591829648463429 : ℕ)^16*1250000000000000^95 ≤ 1258764603220173^95*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10423591829648463429 10000000000000000000 1258764603220173 1250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258764603220173/1250000000000000 : ℝ)) (X := (10423591829648463429/10000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5423591829648463429/5000000000000000000 : ℝ) ≤ (10137902852097869/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (5423591829648463429/5000000000000000000 : ℝ)^16 ≤ (10137902852097869/10000000000000000 : ℝ)^95 := by
      have hnat : (5423591829648463429 : ℕ)^16*10000000000000000^95 ≤ 10137902852097869^95*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5423591829648463429 5000000000000000000 10137902852097869 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10137902852097869/10000000000000000 : ℝ)) (X := (5423591829648463429/5000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8764603220173/733937500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(13557205267297/1174300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (11743/20000 : ℝ)) (alpha := (8764603220173/733937500000000 : ℝ)) (beta := (13557205267297/1174300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11743/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8764603220173/733937500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(13557205267297/1174300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (58481/100000 : ℝ) ^ (95/16 : ℝ) ≤ (4136664670266824723/100000000000000000000 : ℝ) := by
    have hpowers : (58481/100000 : ℝ)^95 ≤ (4136664670266824723/100000000000000000000 : ℝ)^16 := by
      have hnat : (58481 : ℕ)^95*100000000000000000000^16 ≤ 4136664670266824723^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58481 100000 4136664670266824723 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58481/100000 : ℝ)) (X := (4136664670266824723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (104136664670266824723/100000000000000000000 : ℝ) ≤ (2517125308265507/2500000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (104136664670266824723/100000000000000000000 : ℝ)^16 ≤ (2517125308265507/2500000000000000 : ℝ)^95 := by
      have hnat : (104136664670266824723 : ℕ)^16*2500000000000000^95 ≤ 2517125308265507^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104136664670266824723 100000000000000000000 2517125308265507 2500000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517125308265507/2500000000000000 : ℝ)) (X := (104136664670266824723/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (54136664670266824723/50000000000000000000 : ℝ) ≤ (9897241995893/9765625000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (54136664670266824723/50000000000000000000 : ℝ)^16 ≤ (9897241995893/9765625000000 : ℝ)^95 := by
      have hnat : (54136664670266824723 : ℕ)^16*9765625000000^95 ≤ 9897241995893^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54136664670266824723 50000000000000000000 9897241995893 9765625000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9897241995893/9765625000000 : ℝ)) (X := (54136664670266824723/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(17125308265507/1462025000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16568642683101/1462025000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (58481/100000 : ℝ)) (alpha := (17125308265507/1462025000000000 : ℝ)) (beta := (16568642683101/1462025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (58481/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(17125308265507/1462025000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16568642683101/1462025000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (19417/50000 : ℝ) ^ (95/16 : ℝ) ≤ (181935313772165507/50000000000000000000 : ℝ) := by
    have hpowers : (19417/50000 : ℝ)^95 ≤ (181935313772165507/50000000000000000000 : ℝ)^16 := by
      have hnat : (19417 : ℕ)^95*50000000000000000000^16 ≤ 181935313772165507^16*50000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19417 50000 181935313772165507 50000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19417/50000 : ℝ)) (X := (181935313772165507/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50181935313772165507/50000000000000000000 : ℝ) ≤ (10006119096159909/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (50181935313772165507/50000000000000000000 : ℝ)^16 ≤ (10006119096159909/10000000000000000 : ℝ)^95 := by
      have hnat : (50181935313772165507 : ℕ)^16*10000000000000000^95 ≤ 10006119096159909^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50181935313772165507 50000000000000000000 10006119096159909 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006119096159909/10000000000000000 : ℝ)) (X := (50181935313772165507/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25181935313772165507/25000000000000000000 : ℝ) ≤ (5006109885787339/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (25181935313772165507/25000000000000000000 : ℝ)^16 ≤ (5006109885787339/5000000000000000 : ℝ)^95 := by
      have hnat : (25181935313772165507 : ℕ)^16*5000000000000000^95 ≤ 5006109885787339^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25181935313772165507 25000000000000000000 5006109885787339 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006109885787339/5000000000000000 : ℝ)) (X := (25181935313772165507/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6119096159909/3883400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(6100675414769/3883400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (19417/50000 : ℝ)) (alpha := (6119096159909/3883400000000000 : ℝ)) (beta := (6100675414769/3883400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (19417/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6119096159909/3883400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(6100675414769/3883400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3200224117/10000000000 : ℝ)*X 0 0+(159974269/500000000 : ℝ)*X 0 1+(2761421567/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3199458631/10000000000 : ℝ)*X 1 0+(-639743607/2000000000 : ℝ)*X 1 1+(5524217387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5368170007/10000000000 : ℝ)*X 2 0+(5349299851/10000000000 : ℝ)*X 2 1+(-877931557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4161520873/10000000000 : ℝ)*X 0 0+(4233092711/10000000000 : ℝ)*X 0 1+(3608844173/10000000000 : ℝ)*X 0 2+(4161520873/10000000000 : ℝ)*X 1 0+(4233092711/10000000000 : ℝ)*X 1 1+(3608844173/10000000000 : ℝ)*X 1 2+(4161520873/10000000000 : ℝ)*X 2 0+(4233092711/10000000000 : ℝ)*X 2 1+(3608844173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-1406973010059706554897307133536142097/133344768507110000000000000000000000 : ℝ) := by norm_num
    linear_combination (8657/25000000000 : ℝ)*(base5) + (104733/1000000000000 : ℝ)*(base8) + (93961/1000000000000 : ℝ)*(base11) + (5897/500000000000 : ℝ)*(base29) + (67233/1000000000000 : ℝ)*(base40) + (2097/100000000000 : ℝ)*(base49) + (14673/125000000000 : ℝ)*(base50) + (146499573691/200000000000 : ℝ)*(base60) + (227753/100000 : ℝ)*(major_s1_0) + (227753/100000 : ℝ)*(major_s1_1) + (227753/100000 : ℝ)*(major_s1_2) + (351713068393/100000000000 : ℝ)*(sp_s1_0) + (54955170041/15625000000 : ℝ)*(sp_s1_1) + (439641403613/125000000000 : ℝ)*(sp_s1_2) + (999999641927/1000000000000 : ℝ)*(sp_s1_6) + (54955170041/15625000000 : ℝ)*(f.sum) + (5047982332281355003/11355255770000000000000000000000 : ℝ)*base63 + (19524157220751/194170000000000000000000000 : ℝ)*base65 + (22744586008329/584810000000000000000000000 : ℝ)*base67 + (3983692663749/38834000000000000000000000 : ℝ)*base69 + (626218116113124567/2280138310000000000000000000000 : ℝ)*base70 + (12925619119237/117430000000000000000000000 : ℝ)*base72 + (310891731274119/584810000000000000000000000 : ℝ)*base74 + (111001617049943/117430000000000000000000000 : ℝ)*base76 + (2968374749953760131/6867423830000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b030 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c330059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
