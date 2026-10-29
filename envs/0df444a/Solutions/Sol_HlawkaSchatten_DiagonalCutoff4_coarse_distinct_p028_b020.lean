-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b020
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:21:20.51371+00:00
-- url     : https://prove2.me/submissions/66f9c208-febd-4c84-b949-06daf5acb793

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
theorem collision_support_c328047_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-224332601/10000000000 : ℝ)*x 0 + (-1499284491/2500000000 : ℝ)*x 1 + (5167838413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224332601/10000000000 : ℝ)^93 ≤ (1019109103207/100000000000000 : ℝ)^77 := by
    have hnat : (224332601 : ℕ)^93*100000000000000^77 ≤ 1019109103207^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224332601 10000000000 1019109103207 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499284491/2500000000 : ℝ)^93 ≤ (5392653818979/10000000000000 : ℝ)^77 := by
    have hnat : (1499284491 : ℕ)^93*10000000000000^77 ≤ 5392653818979^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499284491 2500000000 5392653818979 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167838413/10000000000 : ℝ)^93 ≤ (5631794087093/12500000000000 : ℝ)^77 := by
    have hnat : (5167838413 : ℕ)^93*12500000000000^77 ≤ 5631794087093^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167838413 10000000000 5631794087093 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224332601/10000000000 : ℝ), (-1499284491/2500000000 : ℝ), (5167838413/10000000000 : ℝ)] ![(1019109103207/100000000000000 : ℝ), (5392653818979/10000000000000 : ℝ), (5631794087093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224332601/10000000000 : ℝ)|^93 ≤ (1019109103207/100000000000000 : ℝ)^77
        have hw : |(-224332601/10000000000 : ℝ)|=(224332601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1499284491/2500000000 : ℝ)|^93 ≤ (5392653818979/10000000000000 : ℝ)^77
        have hw : |(-1499284491/2500000000 : ℝ)|=(1499284491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167838413/10000000000 : ℝ)|^93 ≤ (5631794087093/12500000000000 : ℝ)^77
        have hw : |(5167838413/10000000000 : ℝ)|=(5167838413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5123130159/10000000000 : ℝ)*x 0 + (143115387/400000000 : ℝ)*x 1 + (3332049189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5123130159/10000000000 : ℝ)^93 ≤ (11146001978023/25000000000000 : ℝ)^77 := by
    have hnat : (5123130159 : ℕ)^93*25000000000000^77 ≤ 11146001978023^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123130159 10000000000 11146001978023 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143115387/400000000 : ℝ)^93 ≤ (7224592865433/25000000000000 : ℝ)^77 := by
    have hnat : (143115387 : ℕ)^93*25000000000000^77 ≤ 7224592865433^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143115387 400000000 7224592865433 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3332049189/10000000000 : ℝ)^93 ≤ (1657351288359/6250000000000 : ℝ)^77 := by
    have hnat : (3332049189 : ℕ)^93*6250000000000^77 ≤ 1657351288359^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3332049189 10000000000 1657351288359 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5123130159/10000000000 : ℝ), (143115387/400000000 : ℝ), (3332049189/10000000000 : ℝ)] ![(11146001978023/25000000000000 : ℝ), (7224592865433/25000000000000 : ℝ), (1657351288359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5123130159/10000000000 : ℝ)|^93 ≤ (11146001978023/25000000000000 : ℝ)^77
        have hw : |(5123130159/10000000000 : ℝ)|=(5123130159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(143115387/400000000 : ℝ)|^93 ≤ (7224592865433/25000000000000 : ℝ)^77
        have hw : |(143115387/400000000 : ℝ)|=(143115387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3332049189/10000000000 : ℝ)|^93 ≤ (1657351288359/6250000000000 : ℝ)^77
        have hw : |(3332049189/10000000000 : ℝ)|=(3332049189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5470935043/10000000000 : ℝ)*x 0 + (-3511638869/10000000000 : ℝ)*x 1 + (-188308173/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5470935043/10000000000 : ℝ)^93 ≤ (48265053429789/100000000000000 : ℝ)^77 := by
    have hnat : (5470935043 : ℕ)^93*100000000000000^77 ≤ 48265053429789^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470935043 10000000000 48265053429789 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3511638869/10000000000 : ℝ)^93 ≤ (28253375091143/100000000000000 : ℝ)^77 := by
    have hnat : (3511638869 : ℕ)^93*100000000000000^77 ≤ 28253375091143^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3511638869 10000000000 28253375091143 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188308173/625000000 : ℝ)^93 ≤ (5870392868461/25000000000000 : ℝ)^77 := by
    have hnat : (188308173 : ℕ)^93*25000000000000^77 ≤ 5870392868461^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188308173 625000000 5870392868461 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5470935043/10000000000 : ℝ), (-3511638869/10000000000 : ℝ), (-188308173/625000000 : ℝ)] ![(48265053429789/100000000000000 : ℝ), (28253375091143/100000000000000 : ℝ), (5870392868461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5470935043/10000000000 : ℝ)|^93 ≤ (48265053429789/100000000000000 : ℝ)^77
        have hw : |(5470935043/10000000000 : ℝ)|=(5470935043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3511638869/10000000000 : ℝ)|^93 ≤ (28253375091143/100000000000000 : ℝ)^77
        have hw : |(-3511638869/10000000000 : ℝ)|=(3511638869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188308173/625000000 : ℝ)|^93 ≤ (5870392868461/25000000000000 : ℝ)^77
        have hw : |(-188308173/625000000 : ℝ)|=(188308173/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-103986061/2500000000 : ℝ)*x 0 + (-7405959271/10000000000 : ℝ)*x 1 + (1756791191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103986061/2500000000 : ℝ)^93 ≤ (429646593549/20000000000000 : ℝ)^77 := by
    have hnat : (103986061 : ℕ)^93*20000000000000^77 ≤ 429646593549^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103986061 2500000000 429646593549 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7405959271/10000000000 : ℝ)^93 ≤ (69579504831111/100000000000000 : ℝ)^77 := by
    have hnat : (7405959271 : ℕ)^93*100000000000000^77 ≤ 69579504831111^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7405959271 10000000000 69579504831111 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1756791191/5000000000 : ℝ)^93 ≤ (5654452436919/20000000000000 : ℝ)^77 := by
    have hnat : (1756791191 : ℕ)^93*20000000000000^77 ≤ 5654452436919^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756791191 5000000000 5654452436919 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103986061/2500000000 : ℝ), (-7405959271/10000000000 : ℝ), (1756791191/5000000000 : ℝ)] ![(429646593549/20000000000000 : ℝ), (69579504831111/100000000000000 : ℝ), (5654452436919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103986061/2500000000 : ℝ)|^93 ≤ (429646593549/20000000000000 : ℝ)^77
        have hw : |(-103986061/2500000000 : ℝ)|=(103986061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7405959271/10000000000 : ℝ)|^93 ≤ (69579504831111/100000000000000 : ℝ)^77
        have hw : |(-7405959271/10000000000 : ℝ)|=(7405959271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1756791191/5000000000 : ℝ)|^93 ≤ (5654452436919/20000000000000 : ℝ)^77
        have hw : |(1756791191/5000000000 : ℝ)|=(1756791191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1656160613/5000000000 : ℝ)*x 0 + (4742598249/10000000000 : ℝ)*x 1 + (62485733/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656160613/5000000000 : ℝ)^93 ≤ (26328111558641/100000000000000 : ℝ)^77 := by
    have hnat : (1656160613 : ℕ)^93*100000000000000^77 ≤ 26328111558641^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656160613 5000000000 26328111558641 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4742598249/10000000000 : ℝ)^93 ≤ (40615804121113/100000000000000 : ℝ)^77 := by
    have hnat : (4742598249 : ℕ)^93*100000000000000^77 ≤ 40615804121113^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742598249 10000000000 40615804121113 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62485733/156250000 : ℝ)^93 ≤ (33056084306313/100000000000000 : ℝ)^77 := by
    have hnat : (62485733 : ℕ)^93*100000000000000^77 ≤ 33056084306313^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62485733 156250000 33056084306313 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1656160613/5000000000 : ℝ), (4742598249/10000000000 : ℝ), (62485733/156250000 : ℝ)] ![(26328111558641/100000000000000 : ℝ), (40615804121113/100000000000000 : ℝ), (33056084306313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1656160613/5000000000 : ℝ)|^93 ≤ (26328111558641/100000000000000 : ℝ)^77
        have hw : |(1656160613/5000000000 : ℝ)|=(1656160613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4742598249/10000000000 : ℝ)|^93 ≤ (40615804121113/100000000000000 : ℝ)^77
        have hw : |(4742598249/10000000000 : ℝ)|=(4742598249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62485733/156250000 : ℝ)|^93 ≤ (33056084306313/100000000000000 : ℝ)^77
        have hw : |(62485733/156250000 : ℝ)|=(62485733/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4797683803/10000000000 : ℝ)*x 0 + (-3363605497/10000000000 : ℝ)*x 1 + (-3892253029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4797683803/10000000000 : ℝ)^93 ≤ (41186271532507/100000000000000 : ℝ)^77 := by
    have hnat : (4797683803 : ℕ)^93*100000000000000^77 ≤ 41186271532507^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797683803 10000000000 41186271532507 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3363605497/10000000000 : ℝ)^93 ≤ (26821238680307/100000000000000 : ℝ)^77 := by
    have hnat : (3363605497 : ℕ)^93*100000000000000^77 ≤ 26821238680307^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3363605497 10000000000 26821238680307 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3892253029/10000000000 : ℝ)^93 ≤ (31992489780559/100000000000000 : ℝ)^77 := by
    have hnat : (3892253029 : ℕ)^93*100000000000000^77 ≤ 31992489780559^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892253029 10000000000 31992489780559 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4797683803/10000000000 : ℝ), (-3363605497/10000000000 : ℝ), (-3892253029/10000000000 : ℝ)] ![(41186271532507/100000000000000 : ℝ), (26821238680307/100000000000000 : ℝ), (31992489780559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4797683803/10000000000 : ℝ)|^93 ≤ (41186271532507/100000000000000 : ℝ)^77
        have hw : |(4797683803/10000000000 : ℝ)|=(4797683803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3363605497/10000000000 : ℝ)|^93 ≤ (26821238680307/100000000000000 : ℝ)^77
        have hw : |(-3363605497/10000000000 : ℝ)|=(3363605497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3892253029/10000000000 : ℝ)|^93 ≤ (31992489780559/100000000000000 : ℝ)^77
        have hw : |(-3892253029/10000000000 : ℝ)|=(3892253029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5145397429/10000000000 : ℝ)*x 0 + (2809/156250000 : ℝ)*x 1 + (95507429/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5145397429/10000000000 : ℝ)^93 ≤ (11204540098307/25000000000000 : ℝ)^77 := by
    have hnat : (5145397429 : ℕ)^93*25000000000000^77 ≤ 11204540098307^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145397429 10000000000 11204540098307 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2809/156250000 : ℝ)^93 ≤ (185652987/100000000000000 : ℝ)^77 := by
    have hnat : (2809 : ℕ)^93*100000000000000^77 ≤ 185652987^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809 156250000 185652987 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95507429/156250000 : ℝ)^93 ≤ (55181653949569/100000000000000 : ℝ)^77 := by
    have hnat : (95507429 : ℕ)^93*100000000000000^77 ≤ 55181653949569^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95507429 156250000 55181653949569 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5145397429/10000000000 : ℝ), (2809/156250000 : ℝ), (95507429/156250000 : ℝ)] ![(11204540098307/25000000000000 : ℝ), (185652987/100000000000000 : ℝ), (55181653949569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5145397429/10000000000 : ℝ)|^93 ≤ (11204540098307/25000000000000 : ℝ)^77
        have hw : |(5145397429/10000000000 : ℝ)|=(5145397429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2809/156250000 : ℝ)|^93 ≤ (185652987/100000000000000 : ℝ)^77
        have hw : |(2809/156250000 : ℝ)|=(2809/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95507429/156250000 : ℝ)|^93 ≤ (55181653949569/100000000000000 : ℝ)^77
        have hw : |(95507429/156250000 : ℝ)|=(95507429/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-48567/5000000000 : ℝ)*x 0 + (-604882441/1250000000 : ℝ)*x 1 + (3202380503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48567/5000000000 : ℝ)^93 ≤ (11033063/12500000000000 : ℝ)^77 := by
    have hnat : (48567 : ℕ)^93*12500000000000^77 ≤ 11033063^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48567 5000000000 11033063 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604882441/1250000000 : ℝ)^93 ≤ (41615656437651/100000000000000 : ℝ)^77 := by
    have hnat : (604882441 : ℕ)^93*100000000000000^77 ≤ 41615656437651^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604882441 1250000000 41615656437651 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3202380503/5000000000 : ℝ)^93 ≤ (58384255289061/100000000000000 : ℝ)^77 := by
    have hnat : (3202380503 : ℕ)^93*100000000000000^77 ≤ 58384255289061^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3202380503 5000000000 58384255289061 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48567/5000000000 : ℝ), (-604882441/1250000000 : ℝ), (3202380503/5000000000 : ℝ)] ![(11033063/12500000000000 : ℝ), (41615656437651/100000000000000 : ℝ), (58384255289061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48567/5000000000 : ℝ)|^93 ≤ (11033063/12500000000000 : ℝ)^77
        have hw : |(-48567/5000000000 : ℝ)|=(48567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-604882441/1250000000 : ℝ)|^93 ≤ (41615656437651/100000000000000 : ℝ)^77
        have hw : |(-604882441/1250000000 : ℝ)|=(604882441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3202380503/5000000000 : ℝ)|^93 ≤ (58384255289061/100000000000000 : ℝ)^77
        have hw : |(3202380503/5000000000 : ℝ)|=(3202380503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3450204261/10000000000 : ℝ)*x 0 + (177655231/400000000 : ℝ)*x 1 + (835024311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3450204261/10000000000 : ℝ)^93 ≤ (5531495392721/20000000000000 : ℝ)^77 := by
    have hnat : (3450204261 : ℕ)^93*20000000000000^77 ≤ 5531495392721^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3450204261 10000000000 5531495392721 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177655231/400000000 : ℝ)^93 ≤ (7504210238289/20000000000000 : ℝ)^77 := by
    have hnat : (177655231 : ℕ)^93*20000000000000^77 ≤ 7504210238289^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177655231 400000000 7504210238289 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835024311/2000000000 : ℝ)^93 ≤ (4352683979169/12500000000000 : ℝ)^77 := by
    have hnat : (835024311 : ℕ)^93*12500000000000^77 ≤ 4352683979169^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835024311 2000000000 4352683979169 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3450204261/10000000000 : ℝ), (177655231/400000000 : ℝ), (835024311/2000000000 : ℝ)] ![(5531495392721/20000000000000 : ℝ), (7504210238289/20000000000000 : ℝ), (4352683979169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3450204261/10000000000 : ℝ)|^93 ≤ (5531495392721/20000000000000 : ℝ)^77
        have hw : |(3450204261/10000000000 : ℝ)|=(3450204261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177655231/400000000 : ℝ)|^93 ≤ (7504210238289/20000000000000 : ℝ)^77
        have hw : |(177655231/400000000 : ℝ)|=(177655231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(835024311/2000000000 : ℝ)|^93 ≤ (4352683979169/12500000000000 : ℝ)^77
        have hw : |(835024311/2000000000 : ℝ)|=(835024311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6428479723/10000000000 : ℝ)*x 0 + (-2828316609/10000000000 : ℝ)*x 1 + (-2594231143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6428479723/10000000000 : ℝ)^93 ≤ (14661374342737/25000000000000 : ℝ)^77 := by
    have hnat : (6428479723 : ℕ)^93*25000000000000^77 ≤ 14661374342737^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6428479723 10000000000 14661374342737 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2828316609/10000000000 : ℝ)^93 ≤ (10877518369613/50000000000000 : ℝ)^77 := by
    have hnat : (2828316609 : ℕ)^93*50000000000000^77 ≤ 10877518369613^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2828316609 10000000000 10877518369613 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594231143/10000000000 : ℝ)^93 ≤ (9799732937399/50000000000000 : ℝ)^77 := by
    have hnat : (2594231143 : ℕ)^93*50000000000000^77 ≤ 9799732937399^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594231143 10000000000 9799732937399 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6428479723/10000000000 : ℝ), (-2828316609/10000000000 : ℝ), (-2594231143/10000000000 : ℝ)] ![(14661374342737/25000000000000 : ℝ), (10877518369613/50000000000000 : ℝ), (9799732937399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6428479723/10000000000 : ℝ)|^93 ≤ (14661374342737/25000000000000 : ℝ)^77
        have hw : |(6428479723/10000000000 : ℝ)|=(6428479723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2828316609/10000000000 : ℝ)|^93 ≤ (10877518369613/50000000000000 : ℝ)^77
        have hw : |(-2828316609/10000000000 : ℝ)|=(2828316609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2594231143/10000000000 : ℝ)|^93 ≤ (9799732937399/50000000000000 : ℝ)^77
        have hw : |(-2594231143/10000000000 : ℝ)|=(2594231143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1028566241/1250000000 : ℝ)*x 0 + (-65833229/5000000000 : ℝ)*x 1 + (1343353757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028566241/1250000000 : ℝ)^93 ≤ (79018153538611/100000000000000 : ℝ)^77 := by
    have hnat : (1028566241 : ℕ)^93*100000000000000^77 ≤ 79018153538611^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028566241 1250000000 79018153538611 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65833229/5000000000 : ℝ)^93 ≤ (535447312103/100000000000000 : ℝ)^77 := by
    have hnat : (65833229 : ℕ)^93*100000000000000^77 ≤ 535447312103^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65833229 5000000000 535447312103 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343353757/5000000000 : ℝ)^93 ≤ (5111599785709/25000000000000 : ℝ)^77 := by
    have hnat : (1343353757 : ℕ)^93*25000000000000^77 ≤ 5111599785709^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343353757 5000000000 5111599785709 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1028566241/1250000000 : ℝ), (-65833229/5000000000 : ℝ), (1343353757/5000000000 : ℝ)] ![(79018153538611/100000000000000 : ℝ), (535447312103/100000000000000 : ℝ), (5111599785709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1028566241/1250000000 : ℝ)|^93 ≤ (79018153538611/100000000000000 : ℝ)^77
        have hw : |(1028566241/1250000000 : ℝ)|=(1028566241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65833229/5000000000 : ℝ)|^93 ≤ (535447312103/100000000000000 : ℝ)^77
        have hw : |(-65833229/5000000000 : ℝ)|=(65833229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343353757/5000000000 : ℝ)|^93 ≤ (5111599785709/25000000000000 : ℝ)^77
        have hw : |(1343353757/5000000000 : ℝ)|=(1343353757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-209277441/5000000000 : ℝ)*x 0 + (-7706148589/10000000000 : ℝ)*x 1 + (1578030789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209277441/5000000000 : ℝ)^93 ≤ (270566058879/12500000000000 : ℝ)^77 := by
    have hnat : (209277441 : ℕ)^93*12500000000000^77 ≤ 270566058879^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209277441 5000000000 270566058879 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7706148589/10000000000 : ℝ)^93 ≤ (9125004364941/12500000000000 : ℝ)^77 := by
    have hnat : (7706148589 : ℕ)^93*12500000000000^77 ≤ 9125004364941^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7706148589 10000000000 9125004364941 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578030789/5000000000 : ℝ)^93 ≤ (12417718300631/50000000000000 : ℝ)^77 := by
    have hnat : (1578030789 : ℕ)^93*50000000000000^77 ≤ 12417718300631^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578030789 5000000000 12417718300631 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209277441/5000000000 : ℝ), (-7706148589/10000000000 : ℝ), (1578030789/5000000000 : ℝ)] ![(270566058879/12500000000000 : ℝ), (9125004364941/12500000000000 : ℝ), (12417718300631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209277441/5000000000 : ℝ)|^93 ≤ (270566058879/12500000000000 : ℝ)^77
        have hw : |(-209277441/5000000000 : ℝ)|=(209277441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7706148589/10000000000 : ℝ)|^93 ≤ (9125004364941/12500000000000 : ℝ)^77
        have hw : |(-7706148589/10000000000 : ℝ)|=(7706148589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1578030789/5000000000 : ℝ)|^93 ≤ (12417718300631/50000000000000 : ℝ)^77
        have hw : |(1578030789/5000000000 : ℝ)|=(1578030789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10000621/15625000 : ℝ)*x 0 + (386233781/1250000000 : ℝ)*x 1 + (235702539/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10000621/15625000 : ℝ)^93 ≤ (29168108040409/50000000000000 : ℝ)^77 := by
    have hnat : (10000621 : ℕ)^93*50000000000000^77 ≤ 29168108040409^77*15625000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10000621 15625000 29168108040409 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386233781/1250000000 : ℝ)^93 ≤ (6051928775093/25000000000000 : ℝ)^77 := by
    have hnat : (386233781 : ℕ)^93*25000000000000^77 ≤ 6051928775093^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386233781 1250000000 6051928775093 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235702539/1000000000 : ℝ)^93 ≤ (17456068796409/100000000000000 : ℝ)^77 := by
    have hnat : (235702539 : ℕ)^93*100000000000000^77 ≤ 17456068796409^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235702539 1000000000 17456068796409 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10000621/15625000 : ℝ), (386233781/1250000000 : ℝ), (235702539/1000000000 : ℝ)] ![(29168108040409/50000000000000 : ℝ), (6051928775093/25000000000000 : ℝ), (17456068796409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10000621/15625000 : ℝ)|^93 ≤ (29168108040409/50000000000000 : ℝ)^77
        have hw : |(10000621/15625000 : ℝ)|=(10000621/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386233781/1250000000 : ℝ)|^93 ≤ (6051928775093/25000000000000 : ℝ)^77
        have hw : |(386233781/1250000000 : ℝ)|=(386233781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235702539/1000000000 : ℝ)|^93 ≤ (17456068796409/100000000000000 : ℝ)^77
        have hw : |(235702539/1000000000 : ℝ)|=(235702539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (518214523/2000000000 : ℝ)*x 0 + (-6019914029/10000000000 : ℝ)*x 1 + (-660948173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518214523/2000000000 : ℝ)^93 ≤ (9785324145503/50000000000000 : ℝ)^77 := by
    have hnat : (518214523 : ℕ)^93*50000000000000^77 ≤ 9785324145503^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518214523 2000000000 9785324145503 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6019914029/10000000000 : ℝ)^93 ≤ (54173995664637/100000000000000 : ℝ)^77 := by
    have hnat : (6019914029 : ℕ)^93*100000000000000^77 ≤ 54173995664637^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019914029 10000000000 54173995664637 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660948173/2000000000 : ℝ)^93 ≤ (26255356023923/100000000000000 : ℝ)^77 := by
    have hnat : (660948173 : ℕ)^93*100000000000000^77 ≤ 26255356023923^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660948173 2000000000 26255356023923 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518214523/2000000000 : ℝ), (-6019914029/10000000000 : ℝ), (-660948173/2000000000 : ℝ)] ![(9785324145503/50000000000000 : ℝ), (54173995664637/100000000000000 : ℝ), (26255356023923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518214523/2000000000 : ℝ)|^93 ≤ (9785324145503/50000000000000 : ℝ)^77
        have hw : |(518214523/2000000000 : ℝ)|=(518214523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6019914029/10000000000 : ℝ)|^93 ≤ (54173995664637/100000000000000 : ℝ)^77
        have hw : |(-6019914029/10000000000 : ℝ)|=(6019914029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660948173/2000000000 : ℝ)|^93 ≤ (26255356023923/100000000000000 : ℝ)^77
        have hw : |(-660948173/2000000000 : ℝ)|=(660948173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s0_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7927922677/10000000000 : ℝ)*x 0 + (-343/2000000000 : ℝ)*x 1 + (1557992151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7927922677/10000000000 : ℝ)^93 ≤ (37772481775389/50000000000000 : ℝ)^77 := by
    have hnat : (7927922677 : ℕ)^93*50000000000000^77 ≤ 37772481775389^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7927922677 10000000000 37772481775389 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343/2000000000 : ℝ)^93 ≤ (673593/100000000000000 : ℝ)^77 := by
    have hnat : (343 : ℕ)^93*100000000000000^77 ≤ 673593^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343 2000000000 673593 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557992151/5000000000 : ℝ)^93 ≤ (24455035766923/100000000000000 : ℝ)^77 := by
    have hnat : (1557992151 : ℕ)^93*100000000000000^77 ≤ 24455035766923^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557992151 5000000000 24455035766923 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7927922677/10000000000 : ℝ), (-343/2000000000 : ℝ), (1557992151/5000000000 : ℝ)] ![(37772481775389/50000000000000 : ℝ), (673593/100000000000000 : ℝ), (24455035766923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7927922677/10000000000 : ℝ)|^93 ≤ (37772481775389/50000000000000 : ℝ)^77
        have hw : |(7927922677/10000000000 : ℝ)|=(7927922677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343/2000000000 : ℝ)|^93 ≤ (673593/100000000000000 : ℝ)^77
        have hw : |(-343/2000000000 : ℝ)|=(343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1557992151/5000000000 : ℝ)|^93 ≤ (24455035766923/100000000000000 : ℝ)^77
        have hw : |(1557992151/5000000000 : ℝ)|=(1557992151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1695403131/10000000000 : ℝ)*x 0 + (-2408745063/5000000000 : ℝ)*x 1 + (5340908861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1695403131/10000000000 : ℝ)^93 ≤ (5862622308909/50000000000000 : ℝ)^77 := by
    have hnat : (1695403131 : ℕ)^93*50000000000000^77 ≤ 5862622308909^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695403131 10000000000 5862622308909 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2408745063/5000000000 : ℝ)^93 ≤ (1034793000757/2500000000000 : ℝ)^77 := by
    have hnat : (2408745063 : ℕ)^93*2500000000000^77 ≤ 1034793000757^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408745063 5000000000 1034793000757 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5340908861/10000000000 : ℝ)^93 ≤ (46883035331439/100000000000000 : ℝ)^77 := by
    have hnat : (5340908861 : ℕ)^93*100000000000000^77 ≤ 46883035331439^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340908861 10000000000 46883035331439 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1695403131/10000000000 : ℝ), (-2408745063/5000000000 : ℝ), (5340908861/10000000000 : ℝ)] ![(5862622308909/50000000000000 : ℝ), (1034793000757/2500000000000 : ℝ), (46883035331439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1695403131/10000000000 : ℝ)|^93 ≤ (5862622308909/50000000000000 : ℝ)^77
        have hw : |(-1695403131/10000000000 : ℝ)|=(1695403131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2408745063/5000000000 : ℝ)|^93 ≤ (1034793000757/2500000000000 : ℝ)^77
        have hw : |(-2408745063/5000000000 : ℝ)|=(2408745063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5340908861/10000000000 : ℝ)|^93 ≤ (46883035331439/100000000000000 : ℝ)^77
        have hw : |(5340908861/10000000000 : ℝ)|=(5340908861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4871651857/10000000000 : ℝ)*x 0 + (3894763867/10000000000 : ℝ)*x 1 + (3281045529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4871651857/10000000000 : ℝ)^93 ≤ (41954427779371/100000000000000 : ℝ)^77 := by
    have hnat : (4871651857 : ℕ)^93*100000000000000^77 ≤ 41954427779371^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871651857 10000000000 41954427779371 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3894763867/10000000000 : ℝ)^93 ≤ (32017417755081/100000000000000 : ℝ)^77 := by
    have hnat : (3894763867 : ℕ)^93*100000000000000^77 ≤ 32017417755081^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894763867 10000000000 32017417755081 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3281045529/10000000000 : ℝ)^93 ≤ (26028154450703/100000000000000 : ℝ)^77 := by
    have hnat : (3281045529 : ℕ)^93*100000000000000^77 ≤ 26028154450703^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3281045529 10000000000 26028154450703 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4871651857/10000000000 : ℝ), (3894763867/10000000000 : ℝ), (3281045529/10000000000 : ℝ)] ![(41954427779371/100000000000000 : ℝ), (32017417755081/100000000000000 : ℝ), (26028154450703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4871651857/10000000000 : ℝ)|^93 ≤ (41954427779371/100000000000000 : ℝ)^77
        have hw : |(4871651857/10000000000 : ℝ)|=(4871651857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3894763867/10000000000 : ℝ)|^93 ≤ (32017417755081/100000000000000 : ℝ)^77
        have hw : |(3894763867/10000000000 : ℝ)|=(3894763867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3281045529/10000000000 : ℝ)|^93 ≤ (26028154450703/100000000000000 : ℝ)^77
        have hw : |(3281045529/10000000000 : ℝ)|=(3281045529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4798690513/10000000000 : ℝ)*x 0 + (-495749479/1250000000 : ℝ)*x 1 + (-1643086287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4798690513/10000000000 : ℝ)^93 ≤ (41196709764137/100000000000000 : ℝ)^77 := by
    have hnat : (4798690513 : ℕ)^93*100000000000000^77 ≤ 41196709764137^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798690513 10000000000 41196709764137 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495749479/1250000000 : ℝ)^93 ≤ (4090750521777/12500000000000 : ℝ)^77 := by
    have hnat : (495749479 : ℕ)^93*12500000000000^77 ≤ 4090750521777^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495749479 1250000000 4090750521777 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1643086287/5000000000 : ℝ)^93 ≤ (26077286054859/100000000000000 : ℝ)^77 := by
    have hnat : (1643086287 : ℕ)^93*100000000000000^77 ≤ 26077286054859^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643086287 5000000000 26077286054859 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4798690513/10000000000 : ℝ), (-495749479/1250000000 : ℝ), (-1643086287/5000000000 : ℝ)] ![(41196709764137/100000000000000 : ℝ), (4090750521777/12500000000000 : ℝ), (26077286054859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4798690513/10000000000 : ℝ)|^93 ≤ (41196709764137/100000000000000 : ℝ)^77
        have hw : |(4798690513/10000000000 : ℝ)|=(4798690513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495749479/1250000000 : ℝ)|^93 ≤ (4090750521777/12500000000000 : ℝ)^77
        have hw : |(-495749479/1250000000 : ℝ)|=(495749479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1643086287/5000000000 : ℝ)|^93 ≤ (26077286054859/100000000000000 : ℝ)^77
        have hw : |(-1643086287/5000000000 : ℝ)|=(1643086287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328047_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (597405901/1000000000 : ℝ)*x 0 + (-1652723169/10000000000 : ℝ)*x 1 + (523538331/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (597405901/1000000000 : ℝ)^93 ≤ (53675989005699/100000000000000 : ℝ)^77 := by
    have hnat : (597405901 : ℕ)^93*100000000000000^77 ≤ 53675989005699^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597405901 1000000000 53675989005699 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1652723169/10000000000 : ℝ)^93 ≤ (11369678682253/100000000000000 : ℝ)^77 := by
    have hnat : (1652723169 : ℕ)^93*100000000000000^77 ≤ 11369678682253^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652723169 10000000000 11369678682253 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523538331/1250000000 : ℝ)^93 ≤ (8738583074959/25000000000000 : ℝ)^77 := by
    have hnat : (523538331 : ℕ)^93*25000000000000^77 ≤ 8738583074959^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523538331 1250000000 8738583074959 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(597405901/1000000000 : ℝ), (-1652723169/10000000000 : ℝ), (523538331/1250000000 : ℝ)] ![(53675989005699/100000000000000 : ℝ), (11369678682253/100000000000000 : ℝ), (8738583074959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(597405901/1000000000 : ℝ)|^93 ≤ (53675989005699/100000000000000 : ℝ)^77
        have hw : |(597405901/1000000000 : ℝ)|=(597405901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1652723169/10000000000 : ℝ)|^93 ≤ (11369678682253/100000000000000 : ℝ)^77
        have hw : |(-1652723169/10000000000 : ℝ)|=(1652723169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523538331/1250000000 : ℝ)|^93 ≤ (8738583074959/25000000000000 : ℝ)^77
        have hw : |(523538331/1250000000 : ℝ)|=(523538331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328047 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-224332601/10000000000 : ℝ)*X 0 0+(-1499284491/2500000000 : ℝ)*X 0 1+(5167838413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5123130159/10000000000 : ℝ)*X 1 0+(143115387/400000000 : ℝ)*X 1 1+(3332049189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5470935043/10000000000 : ℝ)*X 2 0+(-3511638869/10000000000 : ℝ)*X 2 1+(-188308173/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-103986061/2500000000 : ℝ)*X 0 0+(-7405959271/10000000000 : ℝ)*X 0 1+(1756791191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1656160613/5000000000 : ℝ)*X 1 0+(4742598249/10000000000 : ℝ)*X 1 1+(62485733/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4797683803/10000000000 : ℝ)*X 2 0+(-3363605497/10000000000 : ℝ)*X 2 1+(-3892253029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((5145397429/10000000000 : ℝ)*X 0 0+(2809/156250000 : ℝ)*X 0 1+(95507429/156250000 : ℝ)*X 0 2+(5145397429/10000000000 : ℝ)*X 1 0+(2809/156250000 : ℝ)*X 1 1+(95507429/156250000 : ℝ)*X 1 2+(5145397429/10000000000 : ℝ)*X 2 0+(2809/156250000 : ℝ)*X 2 1+(95507429/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-48567/5000000000 : ℝ)*X 0 0+(-604882441/1250000000 : ℝ)*X 0 1+(3202380503/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3450204261/10000000000 : ℝ)*X 1 0+(177655231/400000000 : ℝ)*X 1 1+(835024311/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6428479723/10000000000 : ℝ)*X 2 0+(-2828316609/10000000000 : ℝ)*X 2 1+(-2594231143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1028566241/1250000000 : ℝ)*X 0 0+(-65833229/5000000000 : ℝ)*X 0 1+(1343353757/5000000000 : ℝ)*X 0 2+(1028566241/1250000000 : ℝ)*X 1 0+(-65833229/5000000000 : ℝ)*X 1 1+(1343353757/5000000000 : ℝ)*X 1 2+(1028566241/1250000000 : ℝ)*X 2 0+(-65833229/5000000000 : ℝ)*X 2 1+(1343353757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-209277441/5000000000 : ℝ)*X 0 0+(-7706148589/10000000000 : ℝ)*X 0 1+(1578030789/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((10000621/15625000 : ℝ)*X 1 0+(386233781/1250000000 : ℝ)*X 1 1+(235702539/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((518214523/2000000000 : ℝ)*X 2 0+(-6019914029/10000000000 : ℝ)*X 2 1+(-660948173/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7927922677/10000000000 : ℝ)*X 0 0+(-343/2000000000 : ℝ)*X 0 1+(1557992151/5000000000 : ℝ)*X 0 2+(7927922677/10000000000 : ℝ)*X 1 0+(-343/2000000000 : ℝ)*X 1 1+(1557992151/5000000000 : ℝ)*X 1 2+(7927922677/10000000000 : ℝ)*X 2 0+(-343/2000000000 : ℝ)*X 2 1+(1557992151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((24791/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(24791/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (289774181914195739049/15625000000000000000000000 : ℝ) := by norm_num
    linear_combination (93165511947/250000000000 : ℝ)*(base3) + (1234224715429/1000000000000 : ℝ)*(base7) + (2445593/500000000000 : ℝ)*(base40) + (140671483341/500000000000 : ℝ)*(base50) + (13762654739/6250000000 : ℝ)*(major_s0_0) + (13762654739/6250000000 : ℝ)*(major_s0_1) + (13762654739/6250000000 : ℝ)*(major_s0_2) + (21133727/1000000000000 : ℝ)*(sp_s0_0) + (340644889289/125000000000 : ℝ)*(sp_s0_7) + (619545234021/200000000000 : ℝ)*(sp_s0_8) + (136257683069/50000000000 : ℝ)*(sp_s0_9) + (375287508363/200000000000 : ℝ)*(sp_s0_13) + (58062861/500000000000 : ℝ)*(sp_s0_15) + (26586659/1000000000000 : ℝ)*(sp_s0_23) + (507437437087/500000000000 : ℝ)*(f.failure) + (2725180248039/1000000000000 : ℝ)*(f.sum) + (21361305938109/31250000000000000000000000 : ℝ)*base63 + (532739008637/1250000000000000000000000 : ℝ)*base64 + (38350186843/78125000000000000000000 : ℝ)*base67 + (50078030831859/62500000000000000000000000 : ℝ)*base69 + (19842640024991/62500000000000000000000000 : ℝ)*base70 + (1584153360113/1250000000000000000000000 : ℝ)*base73 + (64467898000609/62500000000000000000000000 : ℝ)*base75 + (57791623305641/62500000000000000000000000 : ℝ)*base76 + (665086674601/1250000000000000000000000 : ℝ)*base79 + (1927/2000000000000000 : ℝ)*base86 + (1927/2000000000000000 : ℝ)*base88 + (1927/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-43393/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-43393/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32376455957385207670491/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34144545673/40000000000 : ℝ)*(base7) + (374321727487/500000000000 : ℝ)*(base40) + (3856991/500000000000 : ℝ)*(base49) + (93959048829/500000000000 : ℝ)*(base59) + (2479945822787/1000000000000 : ℝ)*(major_s0_0) + (2479945822787/1000000000000 : ℝ)*(major_s0_1) + (2479945822787/1000000000000 : ℝ)*(major_s0_2) + (11048857/1000000000000 : ℝ)*(sp_s0_0) + (86566331/1000000000000 : ℝ)*(sp_s0_1) + (20985533491/6250000000 : ℝ)*(sp_s0_14) + (3357609841087/1000000000000 : ℝ)*(sp_s0_15) + (3357696407417/1000000000000 : ℝ)*(sp_s0_16) + (249540421911/125000000000 : ℝ)*(sp_s0_20) + (317651/1250000000 : ℝ)*(sp_s0_27) + (1142963854263/1000000000000 : ℝ)*(f.failure) + (3357696407417/1000000000000 : ℝ)*(f.sum) + (537747248026503/5000000000000000000000000000 : ℝ)*base62 + (1046600736279/200000000000000000000000000 : ℝ)*base65 + (34844992563721/200000000000000000000000000 : ℝ)*base66 + (7912223064526503/10000000000000000000000000000 : ℝ)*base68 + (5859190505712553/10000000000000000000000000000 : ℝ)*base70 + (147263603423721/200000000000000000000000000 : ℝ)*base72 + (3043180219526503/10000000000000000000000000000 : ℝ)*base74 + (3113876992473497/10000000000000000000000000000 : ℝ)*base77 + (3175946086279/100000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (577/4000000000000000 : ℝ)*base87 + (577/4000000000000000 : ℝ)*base89 + (577/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59037/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59037/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5474159315951199768753/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1268736256681/1000000000000 : ℝ)*(base7) + (970969/125000000000 : ℝ)*(base22) + (150664795733/500000000000 : ℝ)*(base40) + (28968888831/250000000000 : ℝ)*(base50) + (487862677979/250000000000 : ℝ)*(major_s0_0) + (487862677979/250000000000 : ℝ)*(major_s0_1) + (487862677979/250000000000 : ℝ)*(major_s0_2) + (1714173/100000000000 : ℝ)*(sp_s0_2) + (449871/12500000000 : ℝ)*(sp_s0_7) + (16977/7812500000 : ℝ)*(sp_s0_20) + (92836783373/40000000000 : ℝ)*(sp_s0_21) + (464191114801/200000000000 : ℝ)*(sp_s0_22) + (2320930664523/1000000000000 : ℝ)*(sp_s0_23) + (2168123742303/1000000000000 : ℝ)*(sp_s0_27) + (449694829339/500000000000 : ℝ)*(f.failure) + (464191114801/200000000000 : ℝ)*(f.sum) + (416455586313049/1250000000000000000000000000 : ℝ)*base63 + (11014869813057/50000000000000000000000000 : ℝ)*base64 + (13997114303057/50000000000000000000000000 : ℝ)*base66 + (174824827688049/2500000000000000000000000000 : ℝ)*base69 + (1103824074464801/2500000000000000000000000000 : ℝ)*base70 + (34184863996943/50000000000000000000000000 : ℝ)*base73 + (1344966118938049/2500000000000000000000000000 : ℝ)*base75 + (1781056640061951/2500000000000000000000000000 : ℝ)*base76 + (1714072940557/25000000000000000000000000 : ℝ)*base78 + (1181/2000000000000000 : ℝ)*base87 + (1181/2000000000000000 : ℝ)*base89 + (1181/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (24791/50000 : ℝ) ^ (91/16 : ℝ) ≤ (1849930800618341921/100000000000000000000 : ℝ) := by
    have hpowers : (24791/50000 : ℝ)^91 ≤ (1849930800618341921/100000000000000000000 : ℝ)^16 := by
      have hnat : (24791 : ℕ)^91*100000000000000000000^16 ≤ 1849930800618341921^16*50000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24791 50000 1849930800618341921 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24791/50000 : ℝ)) (X := (1849930800618341921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (101849930800618341921/100000000000000000000 : ℝ) ≤ (5016140525185093/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (101849930800618341921/100000000000000000000 : ℝ)^16 ≤ (5016140525185093/5000000000000000 : ℝ)^91 := by
      have hnat : (101849930800618341921 : ℕ)^16*5000000000000000^91 ≤ 5016140525185093^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101849930800618341921 100000000000000000000 5016140525185093 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016140525185093/5000000000000000 : ℝ)) (X := (101849930800618341921/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (51849930800618341921/50000000000000000000 : ℝ) ≤ (10064082423447077/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (51849930800618341921/50000000000000000000 : ℝ)^16 ≤ (10064082423447077/10000000000000000 : ℝ)^91 := by
      have hnat : (51849930800618341921 : ℕ)^16*10000000000000000^91 ≤ 10064082423447077^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51849930800618341921 50000000000000000000 10064082423447077 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064082423447077/10000000000000000 : ℝ)) (X := (51849930800618341921/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16140525185093/2479100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(31801373076891/4958200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (24791/50000 : ℝ)) (alpha := (16140525185093/2479100000000000 : ℝ)) (beta := (31801373076891/4958200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (24791/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16140525185093/2479100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(31801373076891/4958200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (43393/100000 : ℝ) ^ (91/16 : ℝ) ≤ (866611423122461721/100000000000000000000 : ℝ) := by
    have hpowers : (43393/100000 : ℝ)^91 ≤ (866611423122461721/100000000000000000000 : ℝ)^16 := by
      have hnat : (43393 : ℕ)^91*100000000000000000000^16 ≤ 866611423122461721^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43393 100000 866611423122461721 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43393/100000 : ℝ)) (X := (866611423122461721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100866611423122461721/100000000000000000000 : ℝ) ≤ (10015182994088401/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (100866611423122461721/100000000000000000000 : ℝ)^16 ≤ (10015182994088401/10000000000000000 : ℝ)^91 := by
      have hnat : (100866611423122461721 : ℕ)^16*10000000000000000^91 ≤ 10015182994088401^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100866611423122461721 100000000000000000000 10015182994088401 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015182994088401/10000000000000000 : ℝ)) (X := (100866611423122461721/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50866611423122461721/50000000000000000000 : ℝ) ≤ (5015129427365909/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (50866611423122461721/50000000000000000000 : ℝ)^16 ≤ (5015129427365909/5000000000000000 : ℝ)^91 := by
      have hnat : (50866611423122461721 : ℕ)^16*5000000000000000^91 ≤ 5015129427365909^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50866611423122461721 50000000000000000000 5015129427365909 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015129427365909/5000000000000000 : ℝ)) (X := (50866611423122461721/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(15182994088401/4339300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2153694377631/619900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (43393/100000 : ℝ)) (alpha := (15182994088401/4339300000000000 : ℝ)) (beta := (2153694377631/619900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (43393/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(15182994088401/4339300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2153694377631/619900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (59037/100000 : ℝ) ^ (91/16 : ℝ) ≤ (2495969932614396921/50000000000000000000 : ℝ) := by
    have hpowers : (59037/100000 : ℝ)^91 ≤ (2495969932614396921/50000000000000000000 : ℝ)^16 := by
      have hnat : (59037 : ℕ)^91*50000000000000000000^16 ≤ 2495969932614396921^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59037 100000 2495969932614396921 50000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59037/100000 : ℝ)) (X := (2495969932614396921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (52495969932614396921/50000000000000000000 : ℝ) ≤ (5043008887793839/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (52495969932614396921/50000000000000000000 : ℝ)^16 ≤ (5043008887793839/5000000000000000 : ℝ)^91 := by
      have hnat : (52495969932614396921 : ℕ)^16*5000000000000000^91 ≤ 5043008887793839^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52495969932614396921 50000000000000000000 5043008887793839 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043008887793839/5000000000000000 : ℝ)) (X := (52495969932614396921/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (27495969932614396921/25000000000000000000 : ℝ) ≤ (5084364151316773/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (27495969932614396921/25000000000000000000 : ℝ)^16 ≤ (5084364151316773/5000000000000000 : ℝ)^91 := by
      have hnat : (27495969932614396921 : ℕ)^16*5000000000000000^91 ≤ 5084364151316773^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27495969932614396921 25000000000000000000 5084364151316773 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5084364151316773/5000000000000000 : ℝ)) (X := (27495969932614396921/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3909898890349/268350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6892543920489/491975000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (59037/100000 : ℝ)) (alpha := (3909898890349/268350000000000 : ℝ)) (beta := (6892543920489/491975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (59037/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3909898890349/268350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6892543920489/491975000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1695403131/10000000000 : ℝ)*X 0 0+(-2408745063/5000000000 : ℝ)*X 0 1+(5340908861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4871651857/10000000000 : ℝ)*X 1 0+(3894763867/10000000000 : ℝ)*X 1 1+(3281045529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4798690513/10000000000 : ℝ)*X 2 0+(-495749479/1250000000 : ℝ)*X 2 1+(-1643086287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((597405901/1000000000 : ℝ)*X 0 0+(-1652723169/10000000000 : ℝ)*X 0 1+(523538331/1250000000 : ℝ)*X 0 2+(597405901/1000000000 : ℝ)*X 1 0+(-1652723169/10000000000 : ℝ)*X 1 1+(523538331/1250000000 : ℝ)*X 1 2+(597405901/1000000000 : ℝ)*X 2 0+(-1652723169/10000000000 : ℝ)*X 2 1+(523538331/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-7589684690083461436639304299167/768397045000000000000000000000 : ℝ) := by norm_num
    linear_combination (56859/1000000000000 : ℝ)*(base1) + (7043/500000000000 : ℝ)*(base3) + (167189/1000000000000 : ℝ)*(base5) + (27341/50000000000 : ℝ)*(base10) + (684574101701/1000000000000 : ℝ)*(base40) + (6777/50000000000 : ℝ)*(base50) + (12123559327/31250000000 : ℝ)*(base59) + (44791/125000000000 : ℝ)*(base60) + (8679/4000 : ℝ)*(major_s1_0) + (8679/4000 : ℝ)*(major_s1_1) + (8679/4000 : ℝ)*(major_s1_2) + (1646215675001/500000000000 : ℝ)*(sp_s1_0) + (102888495439/31250000000 : ℝ)*(sp_s1_1) + (3292432007151/1000000000000 : ℝ)*(sp_s1_2) + (999999761867/1000000000000 : ℝ)*(sp_s1_6) + (1646215919981/500000000000 : ℝ)*(f.sum) + (20446038932942099/48518798125000000000000000000 : ℝ)*base63 + (321302910019/715600000000000000000000 : ℝ)*base65 + (24140158488031/30995000000000000000000000 : ℝ)*base66 + (2426081261967/8945000000000000000000000 : ℝ)*base68 + (207886516940865207/443510990000000000000000000000 : ℝ)*base70 + (4730166696191/30988750000000000000000000 : ℝ)*base72 + (16106969361269/433930000000000000000000000 : ℝ)*base74 + (3022938304721/49582000000000000000000000 : ℝ)*base77 + (208130379112605539/768397045000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_b020 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 := by omega
  rcases hc with rfl
  · exact collision_c328047 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b020 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
