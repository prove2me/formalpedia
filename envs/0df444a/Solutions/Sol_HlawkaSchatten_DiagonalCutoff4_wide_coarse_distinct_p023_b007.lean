-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:07.501719+00:00
-- url     : https://prove2.me/submissions/645ccd59-3274-4543-b7ee-d89eefb85d06

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
theorem collision_support_c323017_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-104339953/200000000 : ℝ)*x 0 + (3365008189/10000000000 : ℝ)*x 1 + (732118881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104339953/200000000 : ℝ)^85 ≤ (44863690164027/100000000000000 : ℝ)^69 := by
    have hnat : (104339953 : ℕ)^85*100000000000000^69 ≤ 44863690164027^69*200000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104339953 200000000 44863690164027 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3365008189/10000000000 : ℝ)^85 ≤ (26139769203953/100000000000000 : ℝ)^69 := by
    have hnat : (3365008189 : ℕ)^85*100000000000000^69 ≤ 26139769203953^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3365008189 10000000000 26139769203953 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732118881/2000000000 : ℝ)^85 ≤ (144982703071/500000000000 : ℝ)^69 := by
    have hnat : (732118881 : ℕ)^85*500000000000^69 ≤ 144982703071^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732118881 2000000000 144982703071 500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104339953/200000000 : ℝ), (3365008189/10000000000 : ℝ), (732118881/2000000000 : ℝ)] ![(44863690164027/100000000000000 : ℝ), (26139769203953/100000000000000 : ℝ), (144982703071/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104339953/200000000 : ℝ)|^85 ≤ (44863690164027/100000000000000 : ℝ)^69
        have hw : |(-104339953/200000000 : ℝ)|=(104339953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3365008189/10000000000 : ℝ)|^85 ≤ (26139769203953/100000000000000 : ℝ)^69
        have hw : |(3365008189/10000000000 : ℝ)|=(3365008189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(732118881/2000000000 : ℝ)|^85 ≤ (144982703071/500000000000 : ℝ)^69
        have hw : |(732118881/2000000000 : ℝ)|=(732118881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323017_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (237584711/625000000 : ℝ)*x 0 + (-306488349/1250000000 : ℝ)*x 1 + (1468568171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237584711/625000000 : ℝ)^85 ≤ (7594040505219/25000000000000 : ℝ)^69 := by
    have hnat : (237584711 : ℕ)^85*25000000000000^69 ≤ 7594040505219^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237584711 625000000 7594040505219 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306488349/1250000000 : ℝ)^85 ≤ (17698630268793/100000000000000 : ℝ)^69 := by
    have hnat : (306488349 : ℕ)^85*100000000000000^69 ≤ 17698630268793^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306488349 1250000000 17698630268793 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468568171/2500000000 : ℝ)^85 ≤ (10385041539551/20000000000000 : ℝ)^69 := by
    have hnat : (1468568171 : ℕ)^85*20000000000000^69 ≤ 10385041539551^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468568171 2500000000 10385041539551 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(237584711/625000000 : ℝ), (-306488349/1250000000 : ℝ), (1468568171/2500000000 : ℝ)] ![(7594040505219/25000000000000 : ℝ), (17698630268793/100000000000000 : ℝ), (10385041539551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(237584711/625000000 : ℝ)|^85 ≤ (7594040505219/25000000000000 : ℝ)^69
        have hw : |(237584711/625000000 : ℝ)|=(237584711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306488349/1250000000 : ℝ)|^85 ≤ (17698630268793/100000000000000 : ℝ)^69
        have hw : |(-306488349/1250000000 : ℝ)|=(306488349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1468568171/2500000000 : ℝ)|^85 ≤ (10385041539551/20000000000000 : ℝ)^69
        have hw : |(1468568171/2500000000 : ℝ)|=(1468568171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323017_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (889286721/2500000000 : ℝ)*x 0 + (6056688533/10000000000 : ℝ)*x 1 + (-499186423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889286721/2500000000 : ℝ)^85 ≤ (27990423031337/100000000000000 : ℝ)^69 := by
    have hnat : (889286721 : ℕ)^85*100000000000000^69 ≤ 27990423031337^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889286721 2500000000 27990423031337 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6056688533/10000000000 : ℝ)^85 ≤ (53918656764147/100000000000000 : ℝ)^69 := by
    have hnat : (6056688533 : ℕ)^85*100000000000000^69 ≤ 53918656764147^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6056688533 10000000000 53918656764147 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499186423/2000000000 : ℝ)^85 ≤ (18090920186301/100000000000000 : ℝ)^69 := by
    have hnat : (499186423 : ℕ)^85*100000000000000^69 ≤ 18090920186301^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499186423 2000000000 18090920186301 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(889286721/2500000000 : ℝ), (6056688533/10000000000 : ℝ), (-499186423/2000000000 : ℝ)] ![(27990423031337/100000000000000 : ℝ), (53918656764147/100000000000000 : ℝ), (18090920186301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(889286721/2500000000 : ℝ)|^85 ≤ (27990423031337/100000000000000 : ℝ)^69
        have hw : |(889286721/2500000000 : ℝ)|=(889286721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6056688533/10000000000 : ℝ)|^85 ≤ (53918656764147/100000000000000 : ℝ)^69
        have hw : |(6056688533/10000000000 : ℝ)|=(6056688533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499186423/2000000000 : ℝ)|^85 ≤ (18090920186301/100000000000000 : ℝ)^69
        have hw : |(-499186423/2000000000 : ℝ)|=(499186423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323017_s0_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (35989739/125000000 : ℝ)*x 0 + (4902325299/10000000000 : ℝ)*x 1 + (1112306111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35989739/125000000 : ℝ)^85 ≤ (4314313579743/20000000000000 : ℝ)^69 := by
    have hnat : (35989739 : ℕ)^85*20000000000000^69 ≤ 4314313579743^69*125000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35989739 125000000 4314313579743 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4902325299/10000000000 : ℝ)^85 ≤ (2536246001/6103515625 : ℝ)^69 := by
    have hnat : (4902325299 : ℕ)^85*6103515625^69 ≤ 2536246001^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902325299 10000000000 2536246001 6103515625 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112306111/2500000000 : ℝ)^85 ≤ (9218644400521/25000000000000 : ℝ)^69 := by
    have hnat : (1112306111 : ℕ)^85*25000000000000^69 ≤ 9218644400521^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112306111 2500000000 9218644400521 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35989739/125000000 : ℝ), (4902325299/10000000000 : ℝ), (1112306111/2500000000 : ℝ)] ![(4314313579743/20000000000000 : ℝ), (2536246001/6103515625 : ℝ), (9218644400521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35989739/125000000 : ℝ)|^85 ≤ (4314313579743/20000000000000 : ℝ)^69
        have hw : |(35989739/125000000 : ℝ)|=(35989739/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4902325299/10000000000 : ℝ)|^85 ≤ (2536246001/6103515625 : ℝ)^69
        have hw : |(4902325299/10000000000 : ℝ)|=(4902325299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112306111/2500000000 : ℝ)|^85 ≤ (9218644400521/25000000000000 : ℝ)^69
        have hw : |(1112306111/2500000000 : ℝ)|=(1112306111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323017 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-104339953/200000000 : ℝ)*X 0 0+(3365008189/10000000000 : ℝ)*X 0 1+(732118881/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323017_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((237584711/625000000 : ℝ)*X 1 0+(-306488349/1250000000 : ℝ)*X 1 1+(1468568171/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323017_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((889286721/2500000000 : ℝ)*X 2 0+(6056688533/10000000000 : ℝ)*X 2 1+(-499186423/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323017_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((35989739/125000000 : ℝ)*X 0 0+(4902325299/10000000000 : ℝ)*X 0 1+(1112306111/2500000000 : ℝ)*X 0 2+(35989739/125000000 : ℝ)*X 1 0+(4902325299/10000000000 : ℝ)*X 1 1+(1112306111/2500000000 : ℝ)*X 1 2+(35989739/125000000 : ℝ)*X 2 0+(4902325299/10000000000 : ℝ)*X 2 1+(1112306111/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323017_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-10808999990266666904202777003/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (911/250000000000 : ℝ)*(base8) + (321/1000000000000 : ℝ)*(base39) + (159485667621/250000000000 : ℝ)*(base49) + (363437642763/1000000000000 : ℝ)*(base50) + (24297668001/40000000000 : ℝ)*(base59) + (293046987169/1000000000000 : ℝ)*(base60) + (489085000217/250000000000 : ℝ)*(major_s0_0) + (97817/50000 : ℝ)*(major_s0_1) + (97817/50000 : ℝ)*(major_s0_2) + (57647999821/20000000000 : ℝ)*(sp_s0_0) + (2882399995613/1000000000000 : ℝ)*(sp_s0_1) + (1441199997781/500000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (1441199997347/500000000000 : ℝ)*(f.sum) + (87174257/100000000000000000000 : ℝ)*base62 + (816465553/1000000000000000000000 : ℝ)*base65 + (526128873/1000000000000000000000 : ℝ)*base67 + (128537048647/2500000000000000000000 : ℝ)*base68 + (419347845497491/500000000000000000000000000 : ℝ)*base71 + (109278061759001/2500000000000000000000000000 : ℝ)*base73 + (819089477/2500000000000000000000 : ℝ)*base74 + (22780055602509/500000000000000000000000000 : ℝ)*base76 + (1399371287259001/2500000000000000000000000000 : ℝ)*base79 + (919/1000000000000 : ℝ)*base83 + (217/250000000000 : ℝ)*base85 + (217/250000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c323018_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4775142317/10000000000 : ℝ)*x 0 + (-250782027/1250000000 : ℝ)*x 1 + (-2659493461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4775142317/10000000000 : ℝ)^85 ≤ (2011492275723/5000000000000 : ℝ)^69 := by
    have hnat : (4775142317 : ℕ)^85*5000000000000^69 ≤ 2011492275723^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775142317 10000000000 2011492275723 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250782027/1250000000 : ℝ)^85 ≤ (13823592463309/100000000000000 : ℝ)^69 := by
    have hnat : (250782027 : ℕ)^85*100000000000000^69 ≤ 13823592463309^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250782027 1250000000 13823592463309 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2659493461/5000000000 : ℝ)^85 ≤ (11486640502183/25000000000000 : ℝ)^69 := by
    have hnat : (2659493461 : ℕ)^85*25000000000000^69 ≤ 11486640502183^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659493461 5000000000 11486640502183 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4775142317/10000000000 : ℝ), (-250782027/1250000000 : ℝ), (-2659493461/5000000000 : ℝ)] ![(2011492275723/5000000000000 : ℝ), (13823592463309/100000000000000 : ℝ), (11486640502183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4775142317/10000000000 : ℝ)|^85 ≤ (2011492275723/5000000000000 : ℝ)^69
        have hw : |(4775142317/10000000000 : ℝ)|=(4775142317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250782027/1250000000 : ℝ)|^85 ≤ (13823592463309/100000000000000 : ℝ)^69
        have hw : |(-250782027/1250000000 : ℝ)|=(250782027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2659493461/5000000000 : ℝ)|^85 ≤ (11486640502183/25000000000000 : ℝ)^69
        have hw : |(-2659493461/5000000000 : ℝ)|=(2659493461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1937456697/5000000000 : ℝ)*x 0 + (2687792233/5000000000 : ℝ)*x 1 + (370385251/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1937456697/5000000000 : ℝ)^85 ≤ (31101871454911/100000000000000 : ℝ)^69 := by
    have hnat : (1937456697 : ℕ)^85*100000000000000^69 ≤ 31101871454911^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937456697 5000000000 31101871454911 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687792233/5000000000 : ℝ)^85 ≤ (11637393353531/25000000000000 : ℝ)^69 := by
    have hnat : (2687792233 : ℕ)^85*25000000000000^69 ≤ 11637393353531^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687792233 5000000000 11637393353531 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370385251/1250000000 : ℝ)^85 ≤ (22348555118683/100000000000000 : ℝ)^69 := by
    have hnat : (370385251 : ℕ)^85*100000000000000^69 ≤ 22348555118683^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370385251 1250000000 22348555118683 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1937456697/5000000000 : ℝ), (2687792233/5000000000 : ℝ), (370385251/1250000000 : ℝ)] ![(31101871454911/100000000000000 : ℝ), (11637393353531/25000000000000 : ℝ), (22348555118683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1937456697/5000000000 : ℝ)|^85 ≤ (31101871454911/100000000000000 : ℝ)^69
        have hw : |(1937456697/5000000000 : ℝ)|=(1937456697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687792233/5000000000 : ℝ)|^85 ≤ (11637393353531/25000000000000 : ℝ)^69
        have hw : |(2687792233/5000000000 : ℝ)|=(2687792233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370385251/1250000000 : ℝ)|^85 ≤ (22348555118683/100000000000000 : ℝ)^69
        have hw : |(370385251/1250000000 : ℝ)|=(370385251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-461140243/1000000000 : ℝ)*x 0 + (545307603/2000000000 : ℝ)*x 1 + (-487715353/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461140243/1000000000 : ℝ)^85 ≤ (19268649010827/50000000000000 : ℝ)^69 := by
    have hnat : (461140243 : ℕ)^85*50000000000000^69 ≤ 19268649010827^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461140243 1000000000 19268649010827 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545307603/2000000000 : ℝ)^85 ≤ (20171531598117/100000000000000 : ℝ)^69 := by
    have hnat : (545307603 : ℕ)^85*100000000000000^69 ≤ 20171531598117^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545307603 2000000000 20171531598117 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487715353/1000000000 : ℝ)^85 ≤ (41291170373279/100000000000000 : ℝ)^69 := by
    have hnat : (487715353 : ℕ)^85*100000000000000^69 ≤ 41291170373279^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487715353 1000000000 41291170373279 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-461140243/1000000000 : ℝ), (545307603/2000000000 : ℝ), (-487715353/1000000000 : ℝ)] ![(19268649010827/50000000000000 : ℝ), (20171531598117/100000000000000 : ℝ), (41291170373279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-461140243/1000000000 : ℝ)|^85 ≤ (19268649010827/50000000000000 : ℝ)^69
        have hw : |(-461140243/1000000000 : ℝ)|=(461140243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545307603/2000000000 : ℝ)|^85 ≤ (20171531598117/100000000000000 : ℝ)^69
        have hw : |(545307603/2000000000 : ℝ)|=(545307603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487715353/1000000000 : ℝ)|^85 ≤ (41291170373279/100000000000000 : ℝ)^69
        have hw : |(-487715353/1000000000 : ℝ)|=(487715353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5064313889/10000000000 : ℝ)*x 0 + (-960030279/10000000000 : ℝ)*x 1 + (-5805065649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5064313889/10000000000 : ℝ)^85 ≤ (21625873651307/50000000000000 : ℝ)^69 := by
    have hnat : (5064313889 : ℕ)^85*50000000000000^69 ≤ 21625873651307^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064313889 10000000000 21625873651307 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960030279/10000000000 : ℝ)^85 ≤ (5575618245901/100000000000000 : ℝ)^69 := by
    have hnat : (960030279 : ℕ)^85*100000000000000^69 ≤ 5575618245901^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960030279 10000000000 5575618245901 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5805065649/10000000000 : ℝ)^85 ≤ (25586317218433/50000000000000 : ℝ)^69 := by
    have hnat : (5805065649 : ℕ)^85*50000000000000^69 ≤ 25586317218433^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5805065649 10000000000 25586317218433 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5064313889/10000000000 : ℝ), (-960030279/10000000000 : ℝ), (-5805065649/10000000000 : ℝ)] ![(21625873651307/50000000000000 : ℝ), (5575618245901/100000000000000 : ℝ), (25586317218433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5064313889/10000000000 : ℝ)|^85 ≤ (21625873651307/50000000000000 : ℝ)^69
        have hw : |(5064313889/10000000000 : ℝ)|=(5064313889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960030279/10000000000 : ℝ)|^85 ≤ (5575618245901/100000000000000 : ℝ)^69
        have hw : |(-960030279/10000000000 : ℝ)|=(960030279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5805065649/10000000000 : ℝ)|^85 ≤ (25586317218433/50000000000000 : ℝ)^69
        have hw : |(-5805065649/10000000000 : ℝ)|=(5805065649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (182928167/625000000 : ℝ)*x 0 + (37268567/62500000 : ℝ)*x 1 + (3255398513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182928167/625000000 : ℝ)^85 ≤ (5503099581891/25000000000000 : ℝ)^69 := by
    have hnat : (182928167 : ℕ)^85*25000000000000^69 ≤ 5503099581891^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182928167 625000000 5503099581891 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37268567/62500000 : ℝ)^85 ≤ (52892738274687/100000000000000 : ℝ)^69 := by
    have hnat : (37268567 : ℕ)^85*100000000000000^69 ≤ 52892738274687^69*62500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37268567 62500000 52892738274687 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3255398513/10000000000 : ℝ)^85 ≤ (12547431691949/50000000000000 : ℝ)^69 := by
    have hnat : (3255398513 : ℕ)^85*50000000000000^69 ≤ 12547431691949^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3255398513 10000000000 12547431691949 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(182928167/625000000 : ℝ), (37268567/62500000 : ℝ), (3255398513/10000000000 : ℝ)] ![(5503099581891/25000000000000 : ℝ), (52892738274687/100000000000000 : ℝ), (12547431691949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(182928167/625000000 : ℝ)|^85 ≤ (5503099581891/25000000000000 : ℝ)^69
        have hw : |(182928167/625000000 : ℝ)|=(182928167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37268567/62500000 : ℝ)|^85 ≤ (52892738274687/100000000000000 : ℝ)^69
        have hw : |(37268567/62500000 : ℝ)|=(37268567/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3255398513/10000000000 : ℝ)|^85 ≤ (12547431691949/50000000000000 : ℝ)^69
        have hw : |(3255398513/10000000000 : ℝ)|=(3255398513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-167053/5000000000 : ℝ)*x 0 + (9111967879/10000000000 : ℝ)*x 1 + (-328986033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167053/5000000000 : ℝ)^85 ≤ (38269643/12500000000000 : ℝ)^69 := by
    have hnat : (167053 : ℕ)^85*12500000000000^69 ≤ 38269643^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167053 5000000000 38269643 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9111967879/10000000000 : ℝ)^85 ≤ (22293943555299/25000000000000 : ℝ)^69 := by
    have hnat : (9111967879 : ℕ)^85*25000000000000^69 ≤ 22293943555299^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9111967879 10000000000 22293943555299 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328986033/2000000000 : ℝ)^85 ≤ (1352989951467/12500000000000 : ℝ)^69 := by
    have hnat : (328986033 : ℕ)^85*12500000000000^69 ≤ 1352989951467^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328986033 2000000000 1352989951467 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167053/5000000000 : ℝ), (9111967879/10000000000 : ℝ), (-328986033/2000000000 : ℝ)] ![(38269643/12500000000000 : ℝ), (22293943555299/25000000000000 : ℝ), (1352989951467/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167053/5000000000 : ℝ)|^85 ≤ (38269643/12500000000000 : ℝ)^69
        have hw : |(-167053/5000000000 : ℝ)|=(167053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9111967879/10000000000 : ℝ)|^85 ≤ (22293943555299/25000000000000 : ℝ)^69
        have hw : |(9111967879/10000000000 : ℝ)|=(9111967879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-328986033/2000000000 : ℝ)|^85 ≤ (1352989951467/12500000000000 : ℝ)^69
        have hw : |(-328986033/2000000000 : ℝ)|=(328986033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1229735771/2500000000 : ℝ)*x 0 + (2460844069/10000000000 : ℝ)*x 1 + (-24003097/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1229735771/2500000000 : ℝ)^85 ≤ (41727443665059/100000000000000 : ℝ)^69 := by
    have hnat : (1229735771 : ℕ)^85*100000000000000^69 ≤ 41727443665059^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229735771 2500000000 41727443665059 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2460844069/10000000000 : ℝ)^85 ≤ (17778135202929/100000000000000 : ℝ)^69 := by
    have hnat : (2460844069 : ℕ)^85*100000000000000^69 ≤ 17778135202929^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460844069 10000000000 17778135202929 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24003097/50000000 : ℝ)^85 ≤ (40494421111107/100000000000000 : ℝ)^69 := by
    have hnat : (24003097 : ℕ)^85*100000000000000^69 ≤ 40494421111107^69*50000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24003097 50000000 40494421111107 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1229735771/2500000000 : ℝ), (2460844069/10000000000 : ℝ), (-24003097/50000000 : ℝ)] ![(41727443665059/100000000000000 : ℝ), (17778135202929/100000000000000 : ℝ), (40494421111107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1229735771/2500000000 : ℝ)|^85 ≤ (41727443665059/100000000000000 : ℝ)^69
        have hw : |(-1229735771/2500000000 : ℝ)|=(1229735771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2460844069/10000000000 : ℝ)|^85 ≤ (17778135202929/100000000000000 : ℝ)^69
        have hw : |(2460844069/10000000000 : ℝ)|=(2460844069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24003097/50000000 : ℝ)|^85 ≤ (40494421111107/100000000000000 : ℝ)^69
        have hw : |(-24003097/50000000 : ℝ)|=(24003097/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5882885147/10000000000 : ℝ)*x 0 + (-729511661/10000000000 : ℝ)*x 1 + (-5135843637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5882885147/10000000000 : ℝ)^85 ≤ (52019006033771/100000000000000 : ℝ)^69 := by
    have hnat : (5882885147 : ℕ)^85*100000000000000^69 ≤ 52019006033771^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5882885147 10000000000 52019006033771 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729511661/10000000000 : ℝ)^85 ≤ (496932673829/12500000000000 : ℝ)^69 := by
    have hnat : (729511661 : ℕ)^85*12500000000000^69 ≤ 496932673829^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729511661 10000000000 496932673829 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135843637/10000000000 : ℝ)^85 ≤ (22002766278089/50000000000000 : ℝ)^69 := by
    have hnat : (5135843637 : ℕ)^85*50000000000000^69 ≤ 22002766278089^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135843637 10000000000 22002766278089 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5882885147/10000000000 : ℝ), (-729511661/10000000000 : ℝ), (-5135843637/10000000000 : ℝ)] ![(52019006033771/100000000000000 : ℝ), (496932673829/12500000000000 : ℝ), (22002766278089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5882885147/10000000000 : ℝ)|^85 ≤ (52019006033771/100000000000000 : ℝ)^69
        have hw : |(5882885147/10000000000 : ℝ)|=(5882885147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-729511661/10000000000 : ℝ)|^85 ≤ (496932673829/12500000000000 : ℝ)^69
        have hw : |(-729511661/10000000000 : ℝ)|=(729511661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5135843637/10000000000 : ℝ)|^85 ≤ (22002766278089/50000000000000 : ℝ)^69
        have hw : |(-5135843637/10000000000 : ℝ)|=(5135843637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2704158407/10000000000 : ℝ)*x 0 + (6527561831/10000000000 : ℝ)*x 1 + (2806640069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704158407/10000000000 : ℝ)^85 ≤ (19967763938333/100000000000000 : ℝ)^69 := by
    have hnat : (2704158407 : ℕ)^85*100000000000000^69 ≤ 19967763938333^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704158407 10000000000 19967763938333 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6527561831/10000000000 : ℝ)^85 ≤ (59128206103973/100000000000000 : ℝ)^69 := by
    have hnat : (6527561831 : ℕ)^85*100000000000000^69 ≤ 59128206103973^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6527561831 10000000000 59128206103973 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806640069/10000000000 : ℝ)^85 ≤ (10452014970811/50000000000000 : ℝ)^69 := by
    have hnat : (2806640069 : ℕ)^85*50000000000000^69 ≤ 10452014970811^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806640069 10000000000 10452014970811 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704158407/10000000000 : ℝ), (6527561831/10000000000 : ℝ), (2806640069/10000000000 : ℝ)] ![(19967763938333/100000000000000 : ℝ), (59128206103973/100000000000000 : ℝ), (10452014970811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704158407/10000000000 : ℝ)|^85 ≤ (19967763938333/100000000000000 : ℝ)^69
        have hw : |(2704158407/10000000000 : ℝ)|=(2704158407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6527561831/10000000000 : ℝ)|^85 ≤ (59128206103973/100000000000000 : ℝ)^69
        have hw : |(6527561831/10000000000 : ℝ)|=(6527561831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806640069/10000000000 : ℝ)|^85 ≤ (10452014970811/50000000000000 : ℝ)^69
        have hw : |(2806640069/10000000000 : ℝ)|=(2806640069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5402413/5000000000 : ℝ)*x 0 + (1311875163/2000000000 : ℝ)*x 1 + (-24003097/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402413/5000000000 : ℝ)^85 ≤ (11084880983/50000000000000 : ℝ)^69 := by
    have hnat : (5402413 : ℕ)^85*50000000000000^69 ≤ 11084880983^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402413 5000000000 11084880983 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311875163/2000000000 : ℝ)^85 ≤ (2974170455701/5000000000000 : ℝ)^69 := by
    have hnat : (1311875163 : ℕ)^85*5000000000000^69 ≤ 2974170455701^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311875163 2000000000 2974170455701 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24003097/50000000 : ℝ)^85 ≤ (40494421111107/100000000000000 : ℝ)^69 := by
    have hnat : (24003097 : ℕ)^85*100000000000000^69 ≤ 40494421111107^69*50000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24003097 50000000 40494421111107 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5402413/5000000000 : ℝ), (1311875163/2000000000 : ℝ), (-24003097/50000000 : ℝ)] ![(11084880983/50000000000000 : ℝ), (2974170455701/5000000000000 : ℝ), (40494421111107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5402413/5000000000 : ℝ)|^85 ≤ (11084880983/50000000000000 : ℝ)^69
        have hw : |(-5402413/5000000000 : ℝ)|=(5402413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311875163/2000000000 : ℝ)|^85 ≤ (2974170455701/5000000000000 : ℝ)^69
        have hw : |(1311875163/2000000000 : ℝ)|=(1311875163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24003097/50000000 : ℝ)|^85 ≤ (40494421111107/100000000000000 : ℝ)^69
        have hw : |(-24003097/50000000 : ℝ)|=(24003097/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5382589039/10000000000 : ℝ)*x 0 + (1558232173/5000000000 : ℝ)*x 1 + (-1860830377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382589039/10000000000 : ℝ)^85 ≤ (9324861099881/20000000000000 : ℝ)^69 := by
    have hnat : (5382589039 : ℕ)^85*20000000000000^69 ≤ 9324861099881^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382589039 10000000000 9324861099881 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558232173/5000000000 : ℝ)^85 ≤ (11891057922739/50000000000000 : ℝ)^69 := by
    have hnat : (1558232173 : ℕ)^85*50000000000000^69 ≤ 11891057922739^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558232173 5000000000 11891057922739 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1860830377/5000000000 : ℝ)^85 ≤ (14796789320811/50000000000000 : ℝ)^69 := by
    have hnat : (1860830377 : ℕ)^85*50000000000000^69 ≤ 14796789320811^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860830377 5000000000 14796789320811 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5382589039/10000000000 : ℝ), (1558232173/5000000000 : ℝ), (-1860830377/5000000000 : ℝ)] ![(9324861099881/20000000000000 : ℝ), (11891057922739/50000000000000 : ℝ), (14796789320811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5382589039/10000000000 : ℝ)|^85 ≤ (9324861099881/20000000000000 : ℝ)^69
        have hw : |(-5382589039/10000000000 : ℝ)|=(5382589039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558232173/5000000000 : ℝ)|^85 ≤ (11891057922739/50000000000000 : ℝ)^69
        have hw : |(1558232173/5000000000 : ℝ)|=(1558232173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1860830377/5000000000 : ℝ)|^85 ≤ (14796789320811/50000000000000 : ℝ)^69
        have hw : |(-1860830377/5000000000 : ℝ)|=(1860830377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4444597967/10000000000 : ℝ)*x 0 + (-643033689/2500000000 : ℝ)*x 1 + (-5173083549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444597967/10000000000 : ℝ)^85 ≤ (3682734840027/10000000000000 : ℝ)^69 := by
    have hnat : (4444597967 : ℕ)^85*10000000000000^69 ≤ 3682734840027^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444597967 10000000000 3682734840027 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643033689/2500000000 : ℝ)^85 ≤ (1877371549677/10000000000000 : ℝ)^69 := by
    have hnat : (643033689 : ℕ)^85*10000000000000^69 ≤ 1877371549677^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643033689 2500000000 1877371549677 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173083549/10000000000 : ℝ)^85 ≤ (1109973402083/2500000000000 : ℝ)^69 := by
    have hnat : (5173083549 : ℕ)^85*2500000000000^69 ≤ 1109973402083^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173083549 10000000000 1109973402083 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444597967/10000000000 : ℝ), (-643033689/2500000000 : ℝ), (-5173083549/10000000000 : ℝ)] ![(3682734840027/10000000000000 : ℝ), (1877371549677/10000000000000 : ℝ), (1109973402083/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444597967/10000000000 : ℝ)|^85 ≤ (3682734840027/10000000000000 : ℝ)^69
        have hw : |(4444597967/10000000000 : ℝ)|=(4444597967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-643033689/2500000000 : ℝ)|^85 ≤ (1877371549677/10000000000000 : ℝ)^69
        have hw : |(-643033689/2500000000 : ℝ)|=(643033689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5173083549/10000000000 : ℝ)|^85 ≤ (1109973402083/2500000000000 : ℝ)^69
        have hw : |(-5173083549/10000000000 : ℝ)|=(5173083549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (84002093/156250000 : ℝ)*x 0 + (1065457913/2500000000 : ℝ)*x 1 + (507744881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84002093/156250000 : ℝ)^85 ≤ (23277717543843/50000000000000 : ℝ)^69 := by
    have hnat : (84002093 : ℕ)^85*50000000000000^69 ≤ 23277717543843^69*156250000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84002093 156250000 23277717543843 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065457913/2500000000 : ℝ)^85 ≤ (3497080062989/10000000000000 : ℝ)^69 := by
    have hnat : (1065457913 : ℕ)^85*10000000000000^69 ≤ 3497080062989^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065457913 2500000000 3497080062989 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507744881/2000000000 : ℝ)^85 ≤ (18473764264121/100000000000000 : ℝ)^69 := by
    have hnat : (507744881 : ℕ)^85*100000000000000^69 ≤ 18473764264121^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507744881 2000000000 18473764264121 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84002093/156250000 : ℝ), (1065457913/2500000000 : ℝ), (507744881/2000000000 : ℝ)] ![(23277717543843/50000000000000 : ℝ), (3497080062989/10000000000000 : ℝ), (18473764264121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84002093/156250000 : ℝ)|^85 ≤ (23277717543843/50000000000000 : ℝ)^69
        have hw : |(84002093/156250000 : ℝ)|=(84002093/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065457913/2500000000 : ℝ)|^85 ≤ (3497080062989/10000000000000 : ℝ)^69
        have hw : |(1065457913/2500000000 : ℝ)|=(1065457913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507744881/2000000000 : ℝ)|^85 ≤ (18473764264121/100000000000000 : ℝ)^69
        have hw : |(507744881/2000000000 : ℝ)|=(507744881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s0_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-7084267/10000000000 : ℝ)*x 0 + (9058061647/10000000000 : ℝ)*x 1 + (-861518269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7084267/10000000000 : ℝ)^85 ≤ (13180398041/100000000000000 : ℝ)^69 := by
    have hnat : (7084267 : ℕ)^85*100000000000000^69 ≤ 13180398041^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7084267 10000000000 13180398041 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9058061647/10000000000 : ℝ)^85 ≤ (44263162592033/50000000000000 : ℝ)^69 := by
    have hnat : (9058061647 : ℕ)^85*50000000000000^69 ≤ 44263162592033^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9058061647 10000000000 44263162592033 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861518269/5000000000 : ℝ)^85 ≤ (11460494407563/100000000000000 : ℝ)^69 := by
    have hnat : (861518269 : ℕ)^85*100000000000000^69 ≤ 11460494407563^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861518269 5000000000 11460494407563 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7084267/10000000000 : ℝ), (9058061647/10000000000 : ℝ), (-861518269/5000000000 : ℝ)] ![(13180398041/100000000000000 : ℝ), (44263162592033/50000000000000 : ℝ), (11460494407563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7084267/10000000000 : ℝ)|^85 ≤ (13180398041/100000000000000 : ℝ)^69
        have hw : |(-7084267/10000000000 : ℝ)|=(7084267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9058061647/10000000000 : ℝ)|^85 ≤ (44263162592033/50000000000000 : ℝ)^69
        have hw : |(9058061647/10000000000 : ℝ)|=(9058061647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-861518269/5000000000 : ℝ)|^85 ≤ (11460494407563/100000000000000 : ℝ)^69
        have hw : |(-861518269/5000000000 : ℝ)|=(861518269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4558350373/10000000000 : ℝ)*x 0 + (3561217207/10000000000 : ℝ)*x 1 + (-1040843689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4558350373/10000000000 : ℝ)^85 ≤ (37991868164109/100000000000000 : ℝ)^69 := by
    have hnat : (4558350373 : ℕ)^85*100000000000000^69 ≤ 37991868164109^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558350373 10000000000 37991868164109 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3561217207/10000000000 : ℝ)^85 ≤ (28029883657189/100000000000000 : ℝ)^69 := by
    have hnat : (3561217207 : ℕ)^85*100000000000000^69 ≤ 28029883657189^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3561217207 10000000000 28029883657189 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040843689/2500000000 : ℝ)^85 ≤ (1359129926527/4000000000000 : ℝ)^69 := by
    have hnat : (1040843689 : ℕ)^85*4000000000000^69 ≤ 1359129926527^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040843689 2500000000 1359129926527 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4558350373/10000000000 : ℝ), (3561217207/10000000000 : ℝ), (-1040843689/2500000000 : ℝ)] ![(37991868164109/100000000000000 : ℝ), (28029883657189/100000000000000 : ℝ), (1359129926527/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4558350373/10000000000 : ℝ)|^85 ≤ (37991868164109/100000000000000 : ℝ)^69
        have hw : |(-4558350373/10000000000 : ℝ)|=(4558350373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3561217207/10000000000 : ℝ)|^85 ≤ (28029883657189/100000000000000 : ℝ)^69
        have hw : |(3561217207/10000000000 : ℝ)|=(3561217207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040843689/2500000000 : ℝ)|^85 ≤ (1359129926527/4000000000000 : ℝ)^69
        have hw : |(-1040843689/2500000000 : ℝ)|=(1040843689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (42143959/100000000 : ℝ)*x 0 + (-324884523/1000000000 : ℝ)*x 1 + (-2399395769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42143959/100000000 : ℝ)^85 ≤ (34491925267883/100000000000000 : ℝ)^69 := by
    have hnat : (42143959 : ℕ)^85*100000000000000^69 ≤ 34491925267883^69*100000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42143959 100000000 34491925267883 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324884523/1000000000 : ℝ)^85 ≤ (1001305861433/4000000000000 : ℝ)^69 := by
    have hnat : (324884523 : ℕ)^85*4000000000000^69 ≤ 1001305861433^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324884523 1000000000 1001305861433 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399395769/5000000000 : ℝ)^85 ≤ (101188570451/250000000000 : ℝ)^69 := by
    have hnat : (2399395769 : ℕ)^85*250000000000^69 ≤ 101188570451^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399395769 5000000000 101188570451 250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42143959/100000000 : ℝ), (-324884523/1000000000 : ℝ), (-2399395769/5000000000 : ℝ)] ![(34491925267883/100000000000000 : ℝ), (1001305861433/4000000000000 : ℝ), (101188570451/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42143959/100000000 : ℝ)|^85 ≤ (34491925267883/100000000000000 : ℝ)^69
        have hw : |(42143959/100000000 : ℝ)|=(42143959/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-324884523/1000000000 : ℝ)|^85 ≤ (1001305861433/4000000000000 : ℝ)^69
        have hw : |(-324884523/1000000000 : ℝ)|=(324884523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2399395769/5000000000 : ℝ)|^85 ≤ (101188570451/250000000000 : ℝ)^69
        have hw : |(-2399395769/5000000000 : ℝ)|=(2399395769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (241764459/625000000 : ℝ)*x 0 + (2434546703/5000000000 : ℝ)*x 1 + (883263429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241764459/625000000 : ℝ)^85 ≤ (15517907352639/50000000000000 : ℝ)^69 := by
    have hnat : (241764459 : ℕ)^85*50000000000000^69 ≤ 15517907352639^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241764459 625000000 15517907352639 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434546703/5000000000 : ℝ)^85 ≤ (20603561991471/50000000000000 : ℝ)^69 := by
    have hnat : (2434546703 : ℕ)^85*50000000000000^69 ≤ 20603561991471^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434546703 5000000000 20603561991471 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883263429/2500000000 : ℝ)^85 ≤ (111028245217/400000000000 : ℝ)^69 := by
    have hnat : (883263429 : ℕ)^85*400000000000^69 ≤ 111028245217^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883263429 2500000000 111028245217 400000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(241764459/625000000 : ℝ), (2434546703/5000000000 : ℝ), (883263429/2500000000 : ℝ)] ![(15517907352639/50000000000000 : ℝ), (20603561991471/50000000000000 : ℝ), (111028245217/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(241764459/625000000 : ℝ)|^85 ≤ (15517907352639/50000000000000 : ℝ)^69
        have hw : |(241764459/625000000 : ℝ)|=(241764459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2434546703/5000000000 : ℝ)|^85 ≤ (20603561991471/50000000000000 : ℝ)^69
        have hw : |(2434546703/5000000000 : ℝ)|=(2434546703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(883263429/2500000000 : ℝ)|^85 ≤ (111028245217/400000000000 : ℝ)^69
        have hw : |(883263429/2500000000 : ℝ)|=(883263429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323018_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (600771941/2000000000 : ℝ)*x 0 + (5752385901/10000000000 : ℝ)*x 1 + (-684078899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600771941/2000000000 : ℝ)^85 ≤ (4545606917983/20000000000000 : ℝ)^69 := by
    have hnat : (600771941 : ℕ)^85*20000000000000^69 ≤ 4545606917983^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600771941 2000000000 4545606917983 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5752385901/10000000000 : ℝ)^85 ≤ (10120234867201/20000000000000 : ℝ)^69 := by
    have hnat : (5752385901 : ℕ)^85*20000000000000^69 ≤ 10120234867201^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5752385901 10000000000 10120234867201 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684078899/2000000000 : ℝ)^85 ≤ (26670791055331/100000000000000 : ℝ)^69 := by
    have hnat : (684078899 : ℕ)^85*100000000000000^69 ≤ 26670791055331^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684078899 2000000000 26670791055331 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(600771941/2000000000 : ℝ), (5752385901/10000000000 : ℝ), (-684078899/2000000000 : ℝ)] ![(4545606917983/20000000000000 : ℝ), (10120234867201/20000000000000 : ℝ), (26670791055331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(600771941/2000000000 : ℝ)|^85 ≤ (4545606917983/20000000000000 : ℝ)^69
        have hw : |(600771941/2000000000 : ℝ)|=(600771941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5752385901/10000000000 : ℝ)|^85 ≤ (10120234867201/20000000000000 : ℝ)^69
        have hw : |(5752385901/10000000000 : ℝ)|=(5752385901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-684078899/2000000000 : ℝ)|^85 ≤ (26670791055331/100000000000000 : ℝ)^69
        have hw : |(-684078899/2000000000 : ℝ)|=(684078899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323018 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4775142317/10000000000 : ℝ)*X 1 0+(-250782027/1250000000 : ℝ)*X 1 1+(-2659493461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1937456697/5000000000 : ℝ)*X 2 0+(2687792233/5000000000 : ℝ)*X 2 1+(370385251/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-461140243/1000000000 : ℝ)*X 0 0+(545307603/2000000000 : ℝ)*X 0 1+(-487715353/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5064313889/10000000000 : ℝ)*X 1 0+(-960030279/10000000000 : ℝ)*X 1 1+(-5805065649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((182928167/625000000 : ℝ)*X 2 0+(37268567/62500000 : ℝ)*X 2 1+(3255398513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-167053/5000000000 : ℝ)*X 0 0+(9111967879/10000000000 : ℝ)*X 0 1+(-328986033/2000000000 : ℝ)*X 0 2+(-167053/5000000000 : ℝ)*X 1 0+(9111967879/10000000000 : ℝ)*X 1 1+(-328986033/2000000000 : ℝ)*X 1 2+(-167053/5000000000 : ℝ)*X 2 0+(9111967879/10000000000 : ℝ)*X 2 1+(-328986033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1229735771/2500000000 : ℝ)*X 0 0+(2460844069/10000000000 : ℝ)*X 0 1+(-24003097/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5882885147/10000000000 : ℝ)*X 1 0+(-729511661/10000000000 : ℝ)*X 1 1+(-5135843637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2704158407/10000000000 : ℝ)*X 2 0+(6527561831/10000000000 : ℝ)*X 2 1+(2806640069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5402413/5000000000 : ℝ)*X 0 0+(1311875163/2000000000 : ℝ)*X 0 1+(-24003097/50000000 : ℝ)*X 0 2+(-5402413/5000000000 : ℝ)*X 1 0+(1311875163/2000000000 : ℝ)*X 1 1+(-24003097/50000000 : ℝ)*X 1 2+(-5402413/5000000000 : ℝ)*X 2 0+(1311875163/2000000000 : ℝ)*X 2 1+(-24003097/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5382589039/10000000000 : ℝ)*X 0 0+(1558232173/5000000000 : ℝ)*X 0 1+(-1860830377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4444597967/10000000000 : ℝ)*X 1 0+(-643033689/2500000000 : ℝ)*X 1 1+(-5173083549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((84002093/156250000 : ℝ)*X 2 0+(1065457913/2500000000 : ℝ)*X 2 1+(507744881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-7084267/10000000000 : ℝ)*X 0 0+(9058061647/10000000000 : ℝ)*X 0 1+(-861518269/5000000000 : ℝ)*X 0 2+(-7084267/10000000000 : ℝ)*X 1 0+(9058061647/10000000000 : ℝ)*X 1 1+(-861518269/5000000000 : ℝ)*X 1 2+(-7084267/10000000000 : ℝ)*X 2 0+(9058061647/10000000000 : ℝ)*X 2 1+(-861518269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((8473/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8473/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17580559780297444962273/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (847149/500000000000 : ℝ)*(base1) + (45040073943/62500000000 : ℝ)*(base7) + (858765568091/1000000000000 : ℝ)*(base50) + (544937/100000000000 : ℝ)*(base53) + (16102110083/250000000000 : ℝ)*(base60) + (691351677079/250000000000 : ℝ)*(major_s0_0) + (691351677079/250000000000 : ℝ)*(major_s0_1) + (1382700629473/500000000000 : ℝ)*(major_s0_2) + (54975403/1000000000000 : ℝ)*(sp_s0_1) + (74327496941/20000000000 : ℝ)*(sp_s0_7) + (3716318177349/1000000000000 : ℝ)*(sp_s0_8) + (3716378602123/1000000000000 : ℝ)*(sp_s0_9) + (66683265311/31250000000 : ℝ)*(sp_s0_13) + (336398347/1000000000000 : ℝ)*(sp_s0_27) + (1413561399509/1000000000000 : ℝ)*(f.failure) + (3716378602123/1000000000000 : ℝ)*(f.sum) + (482104424051013/1000000000000000000000000000 : ℝ)*base62 + (4493830131189569/5000000000000000000000000000 : ℝ)*base65 + (555458748917687/2500000000000000000000000000 : ℝ)*base66 + (848897477389621/1000000000000000000000000000 : ℝ)*base69 + (1637375478892739/5000000000000000000000000000 : ℝ)*base71 + (1731526226332313/2500000000000000000000000000 : ℝ)*base72 + (32922331070317/500000000000000000000000000 : ℝ)*base74 + (256384582470317/500000000000000000000000000 : ℝ)*base77 + (1355161667/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (28147/50000000000000000 : ℝ)*base86 + (28147/50000000000000000 : ℝ)*base88 + (28147/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(601/1250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(601/1250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12567164808920278517079/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (339365976763/200000000000 : ℝ)*(base1) + (227339622531/200000000000 : ℝ)*(base7) + (405920844041/1000000000000 : ℝ)*(base39) + (3547419/500000000000 : ℝ)*(base50) + (10564407217/31250000000 : ℝ)*(base60) + (1823405656217/1000000000000 : ℝ)*(major_s0_0) + (1823405656217/1000000000000 : ℝ)*(major_s0_1) + (1823405656217/1000000000000 : ℝ)*(major_s0_2) + (7019961/200000000000 : ℝ)*(sp_s0_2) + (42566371/500000000000 : ℝ)*(sp_s0_9) + (1889636983317/500000000000 : ℝ)*(sp_s0_14) + (2082444082819/1000000000000 : ℝ)*(sp_s0_15) + (65072620321/31250000000 : ℝ)*(sp_s0_16) + (185958848417/500000000000 : ℝ)*(sp_s0_20) + (186409893599/200000000000 : ℝ)*(f.failure) + (2082444082819/1000000000000 : ℝ)*(f.sum) + (449910672785491/1000000000000000000000000000 : ℝ)*base62 + (7160208503527001/10000000000000000000000000000 : ℝ)*base65 + (5232592759527001/10000000000000000000000000000 : ℝ)*base66 + (1268597611414509/2000000000000000000000000000 : ℝ)*base69 + (223674755306807/1250000000000000000000000000 : ℝ)*base71 + (3134175737472999/10000000000000000000000000000 : ℝ)*base72 + (596949990414509/2000000000000000000000000000 : ℝ)*base75 + (1210272464385491/2000000000000000000000000000 : ℝ)*base77 + (2236504873/5000000000000000000000 : ℝ)*base79 + (3383/10000000000000000 : ℝ)*base87 + (3383/10000000000000000 : ℝ)*base89 + (3383/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-2429/4000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-2429/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64701191302519921262313/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (850996700407/1000000000000 : ℝ)*(base1) + (657635827021/500000000000 : ℝ)*(base7) + (3378143/1000000000000 : ℝ)*(base39) + (60672985577/250000000000 : ℝ)*(base44) + (593258641889/1000000000000 : ℝ)*(base50) + (4364647/1000000000000 : ℝ)*(base60) + (579327064693/200000000000 : ℝ)*(major_s0_0) + (2653943381157/1000000000000 : ℝ)*(major_s0_1) + (579327064693/200000000000 : ℝ)*(major_s0_2) + (11754651/50000000000 : ℝ)*(sp_s0_1) + (553997104657/125000000000 : ℝ)*(sp_s0_21) + (41725663769/12500000000 : ℝ)*(sp_s0_22) + (3580980136849/1000000000000 : ℝ)*(sp_s0_23) + (340444608999/200000000000 : ℝ)*(sp_s0_27) + (370160008417/250000000000 : ℝ)*(f.failure) + (3580980136849/1000000000000 : ℝ)*(f.sum) + (113471103569347/1000000000000000000000000000 : ℝ)*base63 + (621164459093771/2000000000000000000000000000 : ℝ)*base64 + (7563877959601179/10000000000000000000000000000 : ℝ)*base67 + (126879126829561/400000000000000000000000000 : ℝ)*base69 + (49500699130197/250000000000000000000000000 : ℝ)*base70 + (840573055106229/2000000000000000000000000000 : ℝ)*base73 + (1471448976409111/2000000000000000000000000000 : ℝ)*base74 + (242754919949561/400000000000000000000000000 : ℝ)*base76 + (1973746534033081/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (13189/12500000000000000 : ℝ)*base87 + (13189/12500000000000000 : ℝ)*base89 + (13189/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (8473/20000 : ℝ) ^ (83/16 : ℝ) ≤ (580857912943922663/50000000000000000000 : ℝ) := by
    have hpowers : (8473/20000 : ℝ)^83 ≤ (580857912943922663/50000000000000000000 : ℝ)^16 := by
      have hnat : (8473 : ℕ)^83*50000000000000000000^16 ≤ 580857912943922663^16*20000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8473 20000 580857912943922663 50000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8473/20000 : ℝ)) (X := (580857912943922663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50580857912943922663/50000000000000000000 : ℝ) ≤ (10022290246236551/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (50580857912943922663/50000000000000000000 : ℝ)^16 ≤ (10022290246236551/10000000000000000 : ℝ)^83 := by
      have hnat : (50580857912943922663 : ℕ)^16*10000000000000000^83 ≤ 10022290246236551^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50580857912943922663 50000000000000000000 10022290246236551 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022290246236551/10000000000000000 : ℝ)) (X := (50580857912943922663/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25580857912943922663/25000000000000000000 : ℝ) ≤ (1004437481002677/1000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (25580857912943922663/25000000000000000000 : ℝ)^16 ≤ (1004437481002677/1000000000000000 : ℝ)^83 := by
      have hnat : (25580857912943922663 : ℕ)^16*1000000000000000^83 ≤ 1004437481002677^83*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25580857912943922663 25000000000000000000 1004437481002677 1000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004437481002677/1000000000000000 : ℝ)) (X := (25580857912943922663/25000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(22290246236551/4236500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(22084563790219/4236500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (8473/20000 : ℝ)) (alpha := (22290246236551/4236500000000000 : ℝ)) (beta := (22084563790219/4236500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8473/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(22290246236551/4236500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(22084563790219/4236500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (601/1250 : ℝ) ^ (83/16 : ℝ) ≤ (223970402788210341/10000000000000000000 : ℝ) := by
    have hpowers : (601/1250 : ℝ)^83 ≤ (223970402788210341/10000000000000000000 : ℝ)^16 := by
      have hnat : (601 : ℕ)^83*10000000000000000000^16 ≤ 223970402788210341^16*1250^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        601 1250 223970402788210341 10000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (601/1250 : ℝ)) (X := (223970402788210341/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10223970402788210341/10000000000000000000 : ℝ) ≤ (5021394954861123/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (10223970402788210341/10000000000000000000 : ℝ)^16 ≤ (5021394954861123/5000000000000000 : ℝ)^83 := by
      have hnat : (10223970402788210341 : ℕ)^16*5000000000000000^83 ≤ 5021394954861123^83*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10223970402788210341 10000000000000000000 5021394954861123 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021394954861123/5000000000000000 : ℝ)) (X := (10223970402788210341/10000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5223970402788210341/5000000000000000000 : ℝ) ≤ (10084829712472417/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (5223970402788210341/5000000000000000000 : ℝ)^16 ≤ (10084829712472417/10000000000000000 : ℝ)^83 := by
      have hnat : (5223970402788210341 : ℕ)^16*10000000000000000^83 ≤ 10084829712472417^83*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5223970402788210341 5000000000000000000 10084829712472417 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10084829712472417/10000000000000000 : ℝ)) (X := (5223970402788210341/5000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(21394954861123/2404000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(42039802750171/4808000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (601/1250 : ℝ)) (alpha := (21394954861123/2404000000000000 : ℝ)) (beta := (42039802750171/4808000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (601/1250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(21394954861123/2404000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(42039802750171/4808000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2429/4000 : ℝ) ^ (83/16 : ℝ) ≤ (1504004112236171503/20000000000000000000 : ℝ) := by
    have hpowers : (2429/4000 : ℝ)^83 ≤ (1504004112236171503/20000000000000000000 : ℝ)^16 := by
      have hnat : (2429 : ℕ)^83*20000000000000000000^16 ≤ 1504004112236171503^16*4000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2429 4000 1504004112236171503 20000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2429/4000 : ℝ)) (X := (1504004112236171503/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (21504004112236171503/20000000000000000000 : ℝ) ≤ (5070376842258859/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (21504004112236171503/20000000000000000000 : ℝ)^16 ≤ (5070376842258859/5000000000000000 : ℝ)^83 := by
      have hnat : (21504004112236171503 : ℕ)^16*5000000000000000^83 ≤ 5070376842258859^83*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21504004112236171503 20000000000000000000 5070376842258859 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5070376842258859/5000000000000000 : ℝ)) (X := (21504004112236171503/20000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (11504004112236171503/10000000000000000000 : ℝ) ≤ (1284221528739129/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (11504004112236171503/10000000000000000000 : ℝ)^16 ≤ (1284221528739129/1250000000000000 : ℝ)^83 := by
      have hnat : (11504004112236171503 : ℕ)^16*1250000000000000^83 ≤ 1284221528739129^83*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11504004112236171503 10000000000000000000 1284221528739129 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1284221528739129/1250000000000000 : ℝ)) (X := (11504004112236171503/10000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(70376842258859/3036250000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(66509272697657/3036250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (2429/4000 : ℝ)) (alpha := (70376842258859/3036250000000000 : ℝ)) (beta := (66509272697657/3036250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (2429/4000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(70376842258859/3036250000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(66509272697657/3036250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4558350373/10000000000 : ℝ)*X 0 0+(3561217207/10000000000 : ℝ)*X 0 1+(-1040843689/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((42143959/100000000 : ℝ)*X 1 0+(-324884523/1000000000 : ℝ)*X 1 1+(-2399395769/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((241764459/625000000 : ℝ)*X 2 0+(2434546703/5000000000 : ℝ)*X 2 1+(883263429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((600771941/2000000000 : ℝ)*X 0 0+(5752385901/10000000000 : ℝ)*X 0 1+(-684078899/2000000000 : ℝ)*X 0 2+(600771941/2000000000 : ℝ)*X 1 0+(5752385901/10000000000 : ℝ)*X 1 1+(-684078899/2000000000 : ℝ)*X 1 2+(600771941/2000000000 : ℝ)*X 2 0+(5752385901/10000000000 : ℝ)*X 2 1+(-684078899/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323018_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-106038299895184251254609040881121/12369131117000000000000000000000 : ℝ) := by norm_num
    linear_combination (1416033/1000000000000 : ℝ)*(base8) + (239619/1000000000000 : ℝ)*(base18) + (585813/1000000000000 : ℝ)*(base21) + (12331/500000000000 : ℝ)*(base29) + (232796757373/1000000000000 : ℝ)*(base39) + (357329261/3906250000 : ℝ)*(base49) + (533154771037/1000000000000 : ℝ)*(base50) + (101575050233/250000000000 : ℝ)*(base60) + (97817/50000 : ℝ)*(major_s1_0) + (97817/50000 : ℝ)*(major_s1_1) + (97817/50000 : ℝ)*(major_s1_2) + (2857604314771/1000000000000 : ℝ)*(sp_s1_0) + (571521098237/200000000000 : ℝ)*(sp_s1_1) + (2857605144991/1000000000000 : ℝ)*(sp_s1_2) + (499999987669/500000000000 : ℝ)*(sp_s1_6) + (714401432701/250000000000 : ℝ)*(f.sum) + (11707582267684103/14598290000000000000000000000 : ℝ)*base62 + (1148159546783/4858000000000000000000000 : ℝ)*base64 + (2783871860893/3005000000000000000000000 : ℝ)*base67 + (992326158291/2429000000000000000000000 : ℝ)*base68 + (8974627016778249/51452292500000000000000000000 : ℝ)*base70 + (1036491332633/2118250000000000000000000 : ℝ)*base73 + (884869609797/3005000000000000000000000 : ℝ)*base74 + (1026245408967/21182500000000000000000000 : ℝ)*base77 + (29494617315334921/25461365000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p023_b007 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=17 ∨ c=18 := by omega
  rcases hc with rfl|rfl
  · exact collision_c323017 p hpa (by linarith only [hpb]) X hX
  · exact collision_c323018 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 17 ≤ c.val) (hhi : c.val < 19)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b007 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
