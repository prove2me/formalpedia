-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:18.160069+00:00
-- url     : https://prove2.me/submissions/3f3ea3fd-b046-4822-bbe8-86bf87138e99

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
theorem collision_support_c322030_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1720642281/2500000000 : ℝ)*x 0 + (-16582559/156250000 : ℝ)*x 1 + (-768987451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1720642281/2500000000 : ℝ)^21 ≤ (6303391012793/10000000000000 : ℝ)^17 := by
    have hnat : (1720642281 : ℕ)^21*10000000000000^17 ≤ 6303391012793^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720642281 2500000000 6303391012793 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16582559/156250000 : ℝ)^21 ≤ (6260592165791/100000000000000 : ℝ)^17 := by
    have hnat : (16582559 : ℕ)^21*100000000000000^17 ≤ 6260592165791^17*156250000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16582559 156250000 6260592165791 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (768987451/2000000000 : ℝ)^21 ≤ (6141099537547/20000000000000 : ℝ)^17 := by
    have hnat : (768987451 : ℕ)^21*20000000000000^17 ≤ 6141099537547^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768987451 2000000000 6141099537547 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1720642281/2500000000 : ℝ), (-16582559/156250000 : ℝ), (-768987451/2000000000 : ℝ)] ![(6303391012793/10000000000000 : ℝ), (6260592165791/100000000000000 : ℝ), (6141099537547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1720642281/2500000000 : ℝ)|^21 ≤ (6303391012793/10000000000000 : ℝ)^17
        have hw : |(1720642281/2500000000 : ℝ)|=(1720642281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16582559/156250000 : ℝ)|^21 ≤ (6260592165791/100000000000000 : ℝ)^17
        have hw : |(-16582559/156250000 : ℝ)|=(16582559/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-768987451/2000000000 : ℝ)|^21 ≤ (6141099537547/20000000000000 : ℝ)^17
        have hw : |(-768987451/2000000000 : ℝ)|=(768987451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (632426049/2500000000 : ℝ)*x 0 + (136215191/250000000 : ℝ)*x 1 + (844282899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (632426049/2500000000 : ℝ)^21 ≤ (915346587717/5000000000000 : ℝ)^17 := by
    have hnat : (632426049 : ℕ)^21*5000000000000^17 ≤ 915346587717^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632426049 2500000000 915346587717 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136215191/250000000 : ℝ)^21 ≤ (2951991414233/6250000000000 : ℝ)^17 := by
    have hnat : (136215191 : ℕ)^21*6250000000000^17 ≤ 2951991414233^17*250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136215191 250000000 2951991414233 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844282899/2000000000 : ℝ)^21 ≤ (17230602803077/50000000000000 : ℝ)^17 := by
    have hnat : (844282899 : ℕ)^21*50000000000000^17 ≤ 17230602803077^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844282899 2000000000 17230602803077 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(632426049/2500000000 : ℝ), (136215191/250000000 : ℝ), (844282899/2000000000 : ℝ)] ![(915346587717/5000000000000 : ℝ), (2951991414233/6250000000000 : ℝ), (17230602803077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(632426049/2500000000 : ℝ)|^21 ≤ (915346587717/5000000000000 : ℝ)^17
        have hw : |(632426049/2500000000 : ℝ)|=(632426049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136215191/250000000 : ℝ)|^21 ≤ (2951991414233/6250000000000 : ℝ)^17
        have hw : |(136215191/250000000 : ℝ)|=(136215191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844282899/2000000000 : ℝ)|^21 ≤ (17230602803077/50000000000000 : ℝ)^17
        have hw : |(844282899/2000000000 : ℝ)|=(844282899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3546864111/10000000000 : ℝ)*x 0 + (3247077491/5000000000 : ℝ)*x 1 + (-1981450489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3546864111/10000000000 : ℝ)^21 ≤ (13896186202209/50000000000000 : ℝ)^17 := by
    have hnat : (3546864111 : ℕ)^21*50000000000000^17 ≤ 13896186202209^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3546864111 10000000000 13896186202209 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3247077491/5000000000 : ℝ)^21 ≤ (11733844445459/20000000000000 : ℝ)^17 := by
    have hnat : (3247077491 : ℕ)^21*20000000000000^17 ≤ 11733844445459^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3247077491 5000000000 11733844445459 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981450489/10000000000 : ℝ)^21 ≤ (6769202677391/50000000000000 : ℝ)^17 := by
    have hnat : (1981450489 : ℕ)^21*50000000000000^17 ≤ 6769202677391^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981450489 10000000000 6769202677391 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3546864111/10000000000 : ℝ), (3247077491/5000000000 : ℝ), (-1981450489/10000000000 : ℝ)] ![(13896186202209/50000000000000 : ℝ), (11733844445459/20000000000000 : ℝ), (6769202677391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3546864111/10000000000 : ℝ)|^21 ≤ (13896186202209/50000000000000 : ℝ)^17
        have hw : |(3546864111/10000000000 : ℝ)|=(3546864111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3247077491/5000000000 : ℝ)|^21 ≤ (11733844445459/20000000000000 : ℝ)^17
        have hw : |(3247077491/5000000000 : ℝ)|=(3247077491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981450489/10000000000 : ℝ)|^21 ≤ (6769202677391/50000000000000 : ℝ)^17
        have hw : |(-1981450489/10000000000 : ℝ)|=(1981450489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2820694873/10000000000 : ℝ)*x 0 + (430428707/1000000000 : ℝ)*x 1 + (-5121922287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2820694873/10000000000 : ℝ)^21 ≤ (20942481227937/100000000000000 : ℝ)^17 := by
    have hnat : (2820694873 : ℕ)^21*100000000000000^17 ≤ 20942481227937^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820694873 10000000000 20942481227937 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430428707/1000000000 : ℝ)^21 ≤ (17649416232911/50000000000000 : ℝ)^17 := by
    have hnat : (430428707 : ℕ)^21*50000000000000^17 ≤ 17649416232911^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430428707 1000000000 17649416232911 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121922287/10000000000 : ℝ)^21 ≤ (8751737259447/20000000000000 : ℝ)^17 := by
    have hnat : (5121922287 : ℕ)^21*20000000000000^17 ≤ 8751737259447^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121922287 10000000000 8751737259447 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2820694873/10000000000 : ℝ), (430428707/1000000000 : ℝ), (-5121922287/10000000000 : ℝ)] ![(20942481227937/100000000000000 : ℝ), (17649416232911/50000000000000 : ℝ), (8751737259447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2820694873/10000000000 : ℝ)|^21 ≤ (20942481227937/100000000000000 : ℝ)^17
        have hw : |(-2820694873/10000000000 : ℝ)|=(2820694873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430428707/1000000000 : ℝ)|^21 ≤ (17649416232911/50000000000000 : ℝ)^17
        have hw : |(430428707/1000000000 : ℝ)|=(430428707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5121922287/10000000000 : ℝ)|^21 ≤ (8751737259447/20000000000000 : ℝ)^17
        have hw : |(-5121922287/10000000000 : ℝ)|=(5121922287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7088549841/10000000000 : ℝ)*x 0 + (-721413541/10000000000 : ℝ)*x 1 + (-1924289617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7088549841/10000000000 : ℝ)^21 ≤ (3268620019423/5000000000000 : ℝ)^17 := by
    have hnat : (7088549841 : ℕ)^21*5000000000000^17 ≤ 3268620019423^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7088549841 10000000000 3268620019423 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721413541/10000000000 : ℝ)^21 ≤ (3886169775641/100000000000000 : ℝ)^17 := by
    have hnat : (721413541 : ℕ)^21*100000000000000^17 ≤ 3886169775641^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721413541 10000000000 3886169775641 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924289617/5000000000 : ℝ)^21 ≤ (6148285965441/20000000000000 : ℝ)^17 := by
    have hnat : (1924289617 : ℕ)^21*20000000000000^17 ≤ 6148285965441^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924289617 5000000000 6148285965441 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7088549841/10000000000 : ℝ), (-721413541/10000000000 : ℝ), (-1924289617/5000000000 : ℝ)] ![(3268620019423/5000000000000 : ℝ), (3886169775641/100000000000000 : ℝ), (6148285965441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7088549841/10000000000 : ℝ)|^21 ≤ (3268620019423/5000000000000 : ℝ)^17
        have hw : |(7088549841/10000000000 : ℝ)|=(7088549841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-721413541/10000000000 : ℝ)|^21 ≤ (3886169775641/100000000000000 : ℝ)^17
        have hw : |(-721413541/10000000000 : ℝ)|=(721413541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1924289617/5000000000 : ℝ)|^21 ≤ (6148285965441/20000000000000 : ℝ)^17
        have hw : |(-1924289617/5000000000 : ℝ)|=(1924289617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2161268811/10000000000 : ℝ)*x 0 + (6021056621/10000000000 : ℝ)*x 1 + (784902401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161268811/10000000000 : ℝ)^21 ≤ (15071958066403/100000000000000 : ℝ)^17 := by
    have hnat : (2161268811 : ℕ)^21*100000000000000^17 ≤ 15071958066403^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161268811 10000000000 15071958066403 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6021056621/10000000000 : ℝ)^21 ≤ (13358909413923/25000000000000 : ℝ)^17 := by
    have hnat : (6021056621 : ℕ)^21*25000000000000^17 ≤ 13358909413923^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021056621 10000000000 13358909413923 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (784902401/2000000000 : ℝ)^21 ≤ (31492404254993/100000000000000 : ℝ)^17 := by
    have hnat : (784902401 : ℕ)^21*100000000000000^17 ≤ 31492404254993^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784902401 2000000000 31492404254993 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161268811/10000000000 : ℝ), (6021056621/10000000000 : ℝ), (784902401/2000000000 : ℝ)] ![(15071958066403/100000000000000 : ℝ), (13358909413923/25000000000000 : ℝ), (31492404254993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161268811/10000000000 : ℝ)|^21 ≤ (15071958066403/100000000000000 : ℝ)^17
        have hw : |(2161268811/10000000000 : ℝ)|=(2161268811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6021056621/10000000000 : ℝ)|^21 ≤ (13358909413923/25000000000000 : ℝ)^17
        have hw : |(6021056621/10000000000 : ℝ)|=(6021056621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(784902401/2000000000 : ℝ)|^21 ≤ (31492404254993/100000000000000 : ℝ)^17
        have hw : |(784902401/2000000000 : ℝ)|=(784902401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_12 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (633910267/2000000000 : ℝ)*x 0 + (1401296579/2000000000 : ℝ)*x 1 + (-1720841317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (633910267/2000000000 : ℝ)^21 ≤ (6046798743021/25000000000000 : ℝ)^17 := by
    have hnat : (633910267 : ℕ)^21*25000000000000^17 ≤ 6046798743021^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633910267 2000000000 6046798743021 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401296579/2000000000 : ℝ)^21 ≤ (16109688731659/25000000000000 : ℝ)^17 := by
    have hnat : (1401296579 : ℕ)^21*25000000000000^17 ≤ 16109688731659^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401296579 2000000000 16109688731659 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720841317/10000000000 : ℝ)^21 ≤ (5687025045421/50000000000000 : ℝ)^17 := by
    have hnat : (1720841317 : ℕ)^21*50000000000000^17 ≤ 5687025045421^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720841317 10000000000 5687025045421 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(633910267/2000000000 : ℝ), (1401296579/2000000000 : ℝ), (-1720841317/10000000000 : ℝ)] ![(6046798743021/25000000000000 : ℝ), (16109688731659/25000000000000 : ℝ), (5687025045421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(633910267/2000000000 : ℝ)|^21 ≤ (6046798743021/25000000000000 : ℝ)^17
        have hw : |(633910267/2000000000 : ℝ)|=(633910267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1401296579/2000000000 : ℝ)|^21 ≤ (16109688731659/25000000000000 : ℝ)^17
        have hw : |(1401296579/2000000000 : ℝ)|=(1401296579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720841317/10000000000 : ℝ)|^21 ≤ (5687025045421/50000000000000 : ℝ)^17
        have hw : |(-1720841317/10000000000 : ℝ)|=(1720841317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1458362903/5000000000 : ℝ)*x 0 + (187086421/400000000 : ℝ)*x 1 + (-4671882501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1458362903/5000000000 : ℝ)^21 ≤ (2182673056541/10000000000000 : ℝ)^17 := by
    have hnat : (1458362903 : ℕ)^21*10000000000000^17 ≤ 2182673056541^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458362903 5000000000 2182673056541 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187086421/400000000 : ℝ)^21 ≤ (9778473316691/25000000000000 : ℝ)^17 := by
    have hnat : (187086421 : ℕ)^21*25000000000000^17 ≤ 9778473316691^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187086421 400000000 9778473316691 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4671882501/10000000000 : ℝ)^21 ≤ (9764844039141/25000000000000 : ℝ)^17 := by
    have hnat : (4671882501 : ℕ)^21*25000000000000^17 ≤ 9764844039141^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671882501 10000000000 9764844039141 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1458362903/5000000000 : ℝ), (187086421/400000000 : ℝ), (-4671882501/10000000000 : ℝ)] ![(2182673056541/10000000000000 : ℝ), (9778473316691/25000000000000 : ℝ), (9764844039141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1458362903/5000000000 : ℝ)|^21 ≤ (2182673056541/10000000000000 : ℝ)^17
        have hw : |(-1458362903/5000000000 : ℝ)|=(1458362903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187086421/400000000 : ℝ)|^21 ≤ (9778473316691/25000000000000 : ℝ)^17
        have hw : |(187086421/400000000 : ℝ)|=(187086421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4671882501/10000000000 : ℝ)|^21 ≤ (9764844039141/25000000000000 : ℝ)^17
        have hw : |(-4671882501/10000000000 : ℝ)|=(4671882501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6922566111/10000000000 : ℝ)*x 0 + (-67059069/625000000 : ℝ)*x 1 + (-94757993/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6922566111/10000000000 : ℝ)^21 ≤ (63486721889029/100000000000000 : ℝ)^17 := by
    have hnat : (6922566111 : ℕ)^21*100000000000000^17 ≤ 63486721889029^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6922566111 10000000000 63486721889029 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67059069/625000000 : ℝ)^21 ≤ (396604930081/6250000000000 : ℝ)^17 := by
    have hnat : (67059069 : ℕ)^21*6250000000000^17 ≤ 396604930081^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67059069 625000000 396604930081 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94757993/250000000 : ℝ)^21 ≤ (6033519842933/20000000000000 : ℝ)^17 := by
    have hnat : (94757993 : ℕ)^21*20000000000000^17 ≤ 6033519842933^17*250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94757993 250000000 6033519842933 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6922566111/10000000000 : ℝ), (-67059069/625000000 : ℝ), (-94757993/250000000 : ℝ)] ![(63486721889029/100000000000000 : ℝ), (396604930081/6250000000000 : ℝ), (6033519842933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6922566111/10000000000 : ℝ)|^21 ≤ (63486721889029/100000000000000 : ℝ)^17
        have hw : |(6922566111/10000000000 : ℝ)|=(6922566111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67059069/625000000 : ℝ)|^21 ≤ (396604930081/6250000000000 : ℝ)^17
        have hw : |(-67059069/625000000 : ℝ)|=(67059069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94757993/250000000 : ℝ)|^21 ≤ (6033519842933/20000000000000 : ℝ)^17
        have hw : |(-94757993/250000000 : ℝ)|=(94757993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (488859259/2000000000 : ℝ)*x 0 + (5428465341/10000000000 : ℝ)*x 1 + (215897279/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (488859259/2000000000 : ℝ)^21 ≤ (17546481763423/100000000000000 : ℝ)^17 := by
    have hnat : (488859259 : ℕ)^21*100000000000000^17 ≤ 17546481763423^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488859259 2000000000 17546481763423 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428465341/10000000000 : ℝ)^21 ≤ (23508133524899/50000000000000 : ℝ)^17 := by
    have hnat : (5428465341 : ℕ)^21*50000000000000^17 ≤ 23508133524899^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428465341 10000000000 23508133524899 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215897279/500000000 : ℝ)^21 ≤ (35437251170647/100000000000000 : ℝ)^17 := by
    have hnat : (215897279 : ℕ)^21*100000000000000^17 ≤ 35437251170647^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215897279 500000000 35437251170647 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(488859259/2000000000 : ℝ), (5428465341/10000000000 : ℝ), (215897279/500000000 : ℝ)] ![(17546481763423/100000000000000 : ℝ), (23508133524899/50000000000000 : ℝ), (35437251170647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(488859259/2000000000 : ℝ)|^21 ≤ (17546481763423/100000000000000 : ℝ)^17
        have hw : |(488859259/2000000000 : ℝ)|=(488859259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428465341/10000000000 : ℝ)|^21 ≤ (23508133524899/50000000000000 : ℝ)^17
        have hw : |(5428465341/10000000000 : ℝ)|=(5428465341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215897279/500000000 : ℝ)|^21 ≤ (35437251170647/100000000000000 : ℝ)^17
        have hw : |(215897279/500000000 : ℝ)|=(215897279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_17 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3/1000000000 : ℝ)*x 0 + (9999999999/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3/1000000000 : ℝ)^21 ≤ (741/25000000000000 : ℝ)^17 := by
    have hnat : (3 : ℕ)^21*25000000000000^17 ≤ 741^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3 1000000000 741 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999999/10000000000 : ℝ)^21 ≤ (1562499999807/1562500000000 : ℝ)^17 := by
    have hnat : (9999999999 : ℕ)^21*1562500000000^17 ≤ 1562499999807^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 1562499999807 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^21 ≤ (0 : ℝ)^17 := by
    have hnat : (0 : ℕ)^21*1^17 ≤ 0^17*1^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3/1000000000 : ℝ), (9999999999/10000000000 : ℝ), (0 : ℝ)] ![(741/25000000000000 : ℝ), (1562499999807/1562500000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3/1000000000 : ℝ)|^21 ≤ (741/25000000000000 : ℝ)^17
        have hw : |(-3/1000000000 : ℝ)|=(3/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9999999999/10000000000 : ℝ)|^21 ≤ (1562499999807/1562500000000 : ℝ)^17
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^21 ≤ (0 : ℝ)^17
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_19 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3469396279/10000000000 : ℝ)*x 0 + (6509624507/10000000000 : ℝ)*x 1 + (-512332957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3469396279/10000000000 : ℝ)^21 ≤ (6761115671503/25000000000000 : ℝ)^17 := by
    have hnat : (3469396279 : ℕ)^21*25000000000000^17 ≤ 6761115671503^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3469396279 10000000000 6761115671503 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6509624507/10000000000 : ℝ)^21 ≤ (58841908037041/100000000000000 : ℝ)^17 := by
    have hnat : (6509624507 : ℕ)^21*100000000000000^17 ≤ 58841908037041^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6509624507 10000000000 58841908037041 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512332957/2500000000 : ℝ)^21 ≤ (70568146303/500000000000 : ℝ)^17 := by
    have hnat : (512332957 : ℕ)^21*500000000000^17 ≤ 70568146303^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512332957 2500000000 70568146303 500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3469396279/10000000000 : ℝ), (6509624507/10000000000 : ℝ), (-512332957/2500000000 : ℝ)] ![(6761115671503/25000000000000 : ℝ), (58841908037041/100000000000000 : ℝ), (70568146303/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3469396279/10000000000 : ℝ)|^21 ≤ (6761115671503/25000000000000 : ℝ)^17
        have hw : |(3469396279/10000000000 : ℝ)|=(3469396279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6509624507/10000000000 : ℝ)|^21 ≤ (58841908037041/100000000000000 : ℝ)^17
        have hw : |(6509624507/10000000000 : ℝ)|=(6509624507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512332957/2500000000 : ℝ)|^21 ≤ (70568146303/500000000000 : ℝ)^17
        have hw : |(-512332957/2500000000 : ℝ)|=(512332957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1226792373/5000000000 : ℝ)*x 0 + (5069148547/10000000000 : ℝ)*x 1 + (-468246577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1226792373/5000000000 : ℝ)^21 ≤ (17628884909759/100000000000000 : ℝ)^17 := by
    have hnat : (1226792373 : ℕ)^21*100000000000000^17 ≤ 17628884909759^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226792373 5000000000 17628884909759 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5069148547/10000000000 : ℝ)^21 ≤ (10800602234169/25000000000000 : ℝ)^17 := by
    have hnat : (5069148547 : ℕ)^21*25000000000000^17 ≤ 10800602234169^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069148547 10000000000 10800602234169 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468246577/1000000000 : ℝ)^21 ≤ (39168706134313/100000000000000 : ℝ)^17 := by
    have hnat : (468246577 : ℕ)^21*100000000000000^17 ≤ 39168706134313^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468246577 1000000000 39168706134313 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1226792373/5000000000 : ℝ), (5069148547/10000000000 : ℝ), (-468246577/1000000000 : ℝ)] ![(17628884909759/100000000000000 : ℝ), (10800602234169/25000000000000 : ℝ), (39168706134313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1226792373/5000000000 : ℝ)|^21 ≤ (17628884909759/100000000000000 : ℝ)^17
        have hw : |(-1226792373/5000000000 : ℝ)|=(1226792373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5069148547/10000000000 : ℝ)|^21 ≤ (10800602234169/25000000000000 : ℝ)^17
        have hw : |(5069148547/10000000000 : ℝ)|=(5069148547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468246577/1000000000 : ℝ)|^21 ≤ (39168706134313/100000000000000 : ℝ)^17
        have hw : |(-468246577/1000000000 : ℝ)|=(468246577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (465066521/625000000 : ℝ)*x 0 + (-28076791/400000000 : ℝ)*x 1 + (-689455113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465066521/625000000 : ℝ)^21 ≤ (34705759139397/50000000000000 : ℝ)^17 := by
    have hnat : (465066521 : ℕ)^21*50000000000000^17 ≤ 34705759139397^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465066521 625000000 34705759139397 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28076791/400000000 : ℝ)^21 ≤ (1878433013053/50000000000000 : ℝ)^17 := by
    have hnat : (28076791 : ℕ)^21*50000000000000^17 ≤ 1878433013053^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28076791 400000000 1878433013053 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689455113/2000000000 : ℝ)^21 ≤ (26831615682787/100000000000000 : ℝ)^17 := by
    have hnat : (689455113 : ℕ)^21*100000000000000^17 ≤ 26831615682787^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689455113 2000000000 26831615682787 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(465066521/625000000 : ℝ), (-28076791/400000000 : ℝ), (-689455113/2000000000 : ℝ)] ![(34705759139397/50000000000000 : ℝ), (1878433013053/50000000000000 : ℝ), (26831615682787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(465066521/625000000 : ℝ)|^21 ≤ (34705759139397/50000000000000 : ℝ)^17
        have hw : |(465066521/625000000 : ℝ)|=(465066521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28076791/400000000 : ℝ)|^21 ≤ (1878433013053/50000000000000 : ℝ)^17
        have hw : |(-28076791/400000000 : ℝ)|=(28076791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-689455113/2000000000 : ℝ)|^21 ≤ (26831615682787/100000000000000 : ℝ)^17
        have hw : |(-689455113/2000000000 : ℝ)|=(689455113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2326177527/10000000000 : ℝ)*x 0 + (541040691/1000000000 : ℝ)*x 1 + (2219659757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2326177527/10000000000 : ℝ)^21 ≤ (3301016088319/20000000000000 : ℝ)^17 := by
    have hnat : (2326177527 : ℕ)^21*20000000000000^17 ≤ 3301016088319^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326177527 10000000000 3301016088319 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541040691/1000000000 : ℝ)^21 ≤ (46823136348959/100000000000000 : ℝ)^17 := by
    have hnat : (541040691 : ℕ)^21*100000000000000^17 ≤ 46823136348959^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541040691 1000000000 46823136348959 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219659757/5000000000 : ℝ)^21 ≤ (3667178319179/10000000000000 : ℝ)^17 := by
    have hnat : (2219659757 : ℕ)^21*10000000000000^17 ≤ 3667178319179^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219659757 5000000000 3667178319179 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2326177527/10000000000 : ℝ), (541040691/1000000000 : ℝ), (2219659757/5000000000 : ℝ)] ![(3301016088319/20000000000000 : ℝ), (46823136348959/100000000000000 : ℝ), (3667178319179/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2326177527/10000000000 : ℝ)|^21 ≤ (3301016088319/20000000000000 : ℝ)^17
        have hw : |(2326177527/10000000000 : ℝ)|=(2326177527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541040691/1000000000 : ℝ)|^21 ≤ (46823136348959/100000000000000 : ℝ)^17
        have hw : |(541040691/1000000000 : ℝ)|=(541040691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219659757/5000000000 : ℝ)|^21 ≤ (3667178319179/10000000000000 : ℝ)^17
        have hw : |(2219659757/5000000000 : ℝ)|=(2219659757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s0_25 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3648880437/10000000000 : ℝ)*x 0 + (132424359/200000000 : ℝ)*x 1 + (-52826349/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3648880437/10000000000 : ℝ)^21 ≤ (1798947079111/6250000000000 : ℝ)^17 := by
    have hnat : (3648880437 : ℕ)^21*6250000000000^17 ≤ 1798947079111^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648880437 10000000000 1798947079111 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132424359/200000000 : ℝ)^21 ≤ (60090472797811/100000000000000 : ℝ)^17 := by
    have hnat : (132424359 : ℕ)^21*100000000000000^17 ≤ 60090472797811^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132424359 200000000 60090472797811 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52826349/312500000 : ℝ)^21 ≤ (11126373917017/100000000000000 : ℝ)^17 := by
    have hnat : (52826349 : ℕ)^21*100000000000000^17 ≤ 11126373917017^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52826349 312500000 11126373917017 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3648880437/10000000000 : ℝ), (132424359/200000000 : ℝ), (-52826349/312500000 : ℝ)] ![(1798947079111/6250000000000 : ℝ), (60090472797811/100000000000000 : ℝ), (11126373917017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3648880437/10000000000 : ℝ)|^21 ≤ (1798947079111/6250000000000 : ℝ)^17
        have hw : |(3648880437/10000000000 : ℝ)|=(3648880437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132424359/200000000 : ℝ)|^21 ≤ (60090472797811/100000000000000 : ℝ)^17
        have hw : |(132424359/200000000 : ℝ)|=(132424359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52826349/312500000 : ℝ)|^21 ≤ (11126373917017/100000000000000 : ℝ)^17
        have hw : |(-52826349/312500000 : ℝ)|=(52826349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3343611119/10000000000 : ℝ)*x 0 + (4582450807/10000000000 : ℝ)*x 1 + (-4375701807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3343611119/10000000000 : ℝ)^21 ≤ (6459613547597/25000000000000 : ℝ)^17 := by
    have hnat : (3343611119 : ℕ)^21*25000000000000^17 ≤ 6459613547597^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3343611119 10000000000 6459613547597 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582450807/10000000000 : ℝ)^21 ≤ (9534460606723/25000000000000 : ℝ)^17 := by
    have hnat : (4582450807 : ℕ)^21*25000000000000^17 ≤ 9534460606723^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582450807 10000000000 9534460606723 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4375701807/10000000000 : ℝ)^21 ≤ (18011851684903/50000000000000 : ℝ)^17 := by
    have hnat : (4375701807 : ℕ)^21*50000000000000^17 ≤ 18011851684903^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375701807 10000000000 18011851684903 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3343611119/10000000000 : ℝ), (4582450807/10000000000 : ℝ), (-4375701807/10000000000 : ℝ)] ![(6459613547597/25000000000000 : ℝ), (9534460606723/25000000000000 : ℝ), (18011851684903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3343611119/10000000000 : ℝ)|^21 ≤ (6459613547597/25000000000000 : ℝ)^17
        have hw : |(-3343611119/10000000000 : ℝ)|=(3343611119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582450807/10000000000 : ℝ)|^21 ≤ (9534460606723/25000000000000 : ℝ)^17
        have hw : |(4582450807/10000000000 : ℝ)|=(4582450807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4375701807/10000000000 : ℝ)|^21 ≤ (18011851684903/50000000000000 : ℝ)^17
        have hw : |(-4375701807/10000000000 : ℝ)|=(4375701807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5759491733/10000000000 : ℝ)*x 0 + (-2259343157/10000000000 : ℝ)*x 1 + (-1031355289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5759491733/10000000000 : ℝ)^21 ≤ (50582927590089/100000000000000 : ℝ)^17 := by
    have hnat : (5759491733 : ℕ)^21*100000000000000^17 ≤ 50582927590089^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5759491733 10000000000 50582927590089 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259343157/10000000000 : ℝ)^21 ≤ (3184256214669/20000000000000 : ℝ)^17 := by
    have hnat : (2259343157 : ℕ)^21*20000000000000^17 ≤ 3184256214669^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259343157 10000000000 3184256214669 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031355289/2500000000 : ℝ)^21 ≤ (33495791327899/100000000000000 : ℝ)^17 := by
    have hnat : (1031355289 : ℕ)^21*100000000000000^17 ≤ 33495791327899^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031355289 2500000000 33495791327899 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5759491733/10000000000 : ℝ), (-2259343157/10000000000 : ℝ), (-1031355289/2500000000 : ℝ)] ![(50582927590089/100000000000000 : ℝ), (3184256214669/20000000000000 : ℝ), (33495791327899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5759491733/10000000000 : ℝ)|^21 ≤ (50582927590089/100000000000000 : ℝ)^17
        have hw : |(5759491733/10000000000 : ℝ)|=(5759491733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2259343157/10000000000 : ℝ)|^21 ≤ (3184256214669/20000000000000 : ℝ)^17
        have hw : |(-2259343157/10000000000 : ℝ)|=(2259343157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031355289/2500000000 : ℝ)|^21 ≤ (33495791327899/100000000000000 : ℝ)^17
        have hw : |(-1031355289/2500000000 : ℝ)|=(1031355289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3212118227/10000000000 : ℝ)*x 0 + (487129259/1000000000 : ℝ)*x 1 + (840724057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3212118227/10000000000 : ℝ)^21 ≤ (6147272663383/25000000000000 : ℝ)^17 := by
    have hnat : (3212118227 : ℕ)^21*25000000000000^17 ≤ 6147272663383^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3212118227 10000000000 6147272663383 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487129259/1000000000 : ℝ)^21 ≤ (41129055586051/100000000000000 : ℝ)^17 := by
    have hnat : (487129259 : ℕ)^21*100000000000000^17 ≤ 41129055586051^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487129259 1000000000 41129055586051 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840724057/2000000000 : ℝ)^21 ≤ (34281853740333/100000000000000 : ℝ)^17 := by
    have hnat : (840724057 : ℕ)^21*100000000000000^17 ≤ 34281853740333^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840724057 2000000000 34281853740333 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3212118227/10000000000 : ℝ), (487129259/1000000000 : ℝ), (840724057/2000000000 : ℝ)] ![(6147272663383/25000000000000 : ℝ), (41129055586051/100000000000000 : ℝ), (34281853740333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3212118227/10000000000 : ℝ)|^21 ≤ (6147272663383/25000000000000 : ℝ)^17
        have hw : |(3212118227/10000000000 : ℝ)|=(3212118227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487129259/1000000000 : ℝ)|^21 ≤ (41129055586051/100000000000000 : ℝ)^17
        have hw : |(487129259/1000000000 : ℝ)|=(487129259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(840724057/2000000000 : ℝ)|^21 ≤ (34281853740333/100000000000000 : ℝ)^17
        have hw : |(840724057/2000000000 : ℝ)|=(840724057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322030_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3871381313/10000000000 : ℝ)*x 0 + (278464391/500000000 : ℝ)*x 1 + (-2773001353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3871381313/10000000000 : ℝ)^21 ≤ (30966579130871/100000000000000 : ℝ)^17 := by
    have hnat : (3871381313 : ℕ)^21*100000000000000^17 ≤ 30966579130871^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3871381313 10000000000 30966579130871 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278464391/500000000 : ℝ)^21 ≤ (24263744436689/50000000000000 : ℝ)^17 := by
    have hnat : (278464391 : ℕ)^21*50000000000000^17 ≤ 24263744436689^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278464391 500000000 24263744436689 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2773001353/10000000000 : ℝ)^21 ≤ (10252965989237/50000000000000 : ℝ)^17 := by
    have hnat : (2773001353 : ℕ)^21*50000000000000^17 ≤ 10252965989237^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773001353 10000000000 10252965989237 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3871381313/10000000000 : ℝ), (278464391/500000000 : ℝ), (-2773001353/10000000000 : ℝ)] ![(30966579130871/100000000000000 : ℝ), (24263744436689/50000000000000 : ℝ), (10252965989237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3871381313/10000000000 : ℝ)|^21 ≤ (30966579130871/100000000000000 : ℝ)^17
        have hw : |(3871381313/10000000000 : ℝ)|=(3871381313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278464391/500000000 : ℝ)|^21 ≤ (24263744436689/50000000000000 : ℝ)^17
        have hw : |(278464391/500000000 : ℝ)|=(278464391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2773001353/10000000000 : ℝ)|^21 ≤ (10252965989237/50000000000000 : ℝ)^17
        have hw : |(-2773001353/10000000000 : ℝ)|=(2773001353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322030 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((1720642281/2500000000 : ℝ)*X 1 0+(-16582559/156250000 : ℝ)*X 1 1+(-768987451/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((632426049/2500000000 : ℝ)*X 2 0+(136215191/250000000 : ℝ)*X 2 1+(844282899/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3546864111/10000000000 : ℝ)*X 0 0+(3247077491/5000000000 : ℝ)*X 0 1+(-1981450489/10000000000 : ℝ)*X 0 2+(3546864111/10000000000 : ℝ)*X 1 0+(3247077491/5000000000 : ℝ)*X 1 1+(-1981450489/10000000000 : ℝ)*X 1 2+(3546864111/10000000000 : ℝ)*X 2 0+(3247077491/5000000000 : ℝ)*X 2 1+(-1981450489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2820694873/10000000000 : ℝ)*X 0 0+(430428707/1000000000 : ℝ)*X 0 1+(-5121922287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7088549841/10000000000 : ℝ)*X 1 0+(-721413541/10000000000 : ℝ)*X 1 1+(-1924289617/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2161268811/10000000000 : ℝ)*X 2 0+(6021056621/10000000000 : ℝ)*X 2 1+(784902401/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((633910267/2000000000 : ℝ)*X 0 0+(1401296579/2000000000 : ℝ)*X 0 1+(-1720841317/10000000000 : ℝ)*X 0 2+(633910267/2000000000 : ℝ)*X 1 0+(1401296579/2000000000 : ℝ)*X 1 1+(-1720841317/10000000000 : ℝ)*X 1 2+(633910267/2000000000 : ℝ)*X 2 0+(1401296579/2000000000 : ℝ)*X 2 1+(-1720841317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1458362903/5000000000 : ℝ)*X 0 0+(187086421/400000000 : ℝ)*X 0 1+(-4671882501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((6922566111/10000000000 : ℝ)*X 1 0+(-67059069/625000000 : ℝ)*X 1 1+(-94757993/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((488859259/2000000000 : ℝ)*X 2 0+(5428465341/10000000000 : ℝ)*X 2 1+(215897279/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((-3/1000000000 : ℝ)*X 0 0+(9999999999/10000000000 : ℝ)*X 0 1+(-3/1000000000 : ℝ)*X 2 0+(9999999999/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_17 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((3469396279/10000000000 : ℝ)*X 0 0+(6509624507/10000000000 : ℝ)*X 0 1+(-512332957/2500000000 : ℝ)*X 0 2+(3469396279/10000000000 : ℝ)*X 1 0+(6509624507/10000000000 : ℝ)*X 1 1+(-512332957/2500000000 : ℝ)*X 1 2+(3469396279/10000000000 : ℝ)*X 2 0+(6509624507/10000000000 : ℝ)*X 2 1+(-512332957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1226792373/5000000000 : ℝ)*X 0 0+(5069148547/10000000000 : ℝ)*X 0 1+(-468246577/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((465066521/625000000 : ℝ)*X 1 0+(-28076791/400000000 : ℝ)*X 1 1+(-689455113/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2326177527/10000000000 : ℝ)*X 2 0+(541040691/1000000000 : ℝ)*X 2 1+(2219659757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((3648880437/10000000000 : ℝ)*X 0 0+(132424359/200000000 : ℝ)*X 0 1+(-52826349/312500000 : ℝ)*X 0 2+(3648880437/10000000000 : ℝ)*X 1 0+(132424359/200000000 : ℝ)*X 1 1+(-52826349/312500000 : ℝ)*X 1 2+(3648880437/10000000000 : ℝ)*X 2 0+(132424359/200000000 : ℝ)*X 2 1+(-52826349/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21327/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21327/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7284779804007159/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (278725786883/125000000000 : ℝ)*(base39) + (3664251542993/1000000000000 : ℝ)*(base49) + (3142797706701/1000000000000 : ℝ)*(base50) + (422708507239/500000000000 : ℝ)*(base60) + (4526908297117/500000000000 : ℝ)*(major_s0_0) + (4526908297117/500000000000 : ℝ)*(major_s0_1) + (4526908297117/500000000000 : ℝ)*(major_s0_2) + (19613307/125000000000 : ℝ)*(sp_s0_1) + (13416252476309/1000000000000 : ℝ)*(sp_s0_7) + (6708067049101/500000000000 : ℝ)*(sp_s0_8) + (2683241056499/200000000000 : ℝ)*(sp_s0_9) + (4691339755549/1000000000000 : ℝ)*(sp_s0_12) + (38528349/1000000000000 : ℝ)*(sp_s0_20) + (85722163/1000000000000 : ℝ)*(sp_s0_22) + (4691339755549/1000000000000 : ℝ)*(f.failure) + (6708145502329/500000000000 : ℝ)*(f.sum) + (290344951/2500000000000000000000 : ℝ)*base62 + (117942745703459/1000000000000000000000000000 : ℝ)*base65 + (16387579103459/1000000000000000000000000000 : ℝ)*base67 + (79911333137661/1250000000000000000000000000 : ℝ)*base68 + (422394901966651/5000000000000000000000000000 : ℝ)*base71 + (345148107396541/1000000000000000000000000000 : ℝ)*base72 + (10683742112339/1250000000000000000000000000 : ℝ)*base74 + (15707800512661/1250000000000000000000000000 : ℝ)*base76 + (142546626696541/500000000000000000000000000 : ℝ)*base78 + (151/10000000000000000 : ℝ)*base87 + (151/10000000000000000 : ℝ)*base89 + (151/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(31/3125 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(31/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (169073153263466326947/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189889936921/250000000000 : ℝ)*(base39) + (62631/200000000000 : ℝ)*(base40) + (171238169153/500000000000 : ℝ)*(base49) + (24250455739/125000000000 : ℝ)*(base60) + (127713513953/40000000000 : ℝ)*(major_s0_0) + (127713513953/40000000000 : ℝ)*(major_s0_1) + (127713513953/40000000000 : ℝ)*(major_s0_2) + (1454645633/1000000000000 : ℝ)*(sp_s0_1) + (98764027/1000000000000 : ℝ)*(sp_s0_2) + (781420631/1000000000000 : ℝ)*(sp_s0_6) + (147852147533/31250000000 : ℝ)*(sp_s0_13) + (4729814075423/1000000000000 : ℝ)*(sp_s0_14) + (4731169957029/1000000000000 : ℝ)*(sp_s0_15) + (413406107201/250000000000 : ℝ)*(sp_s0_19) + (330881169887/200000000000 : ℝ)*(f.failure) + (147852147533/31250000000 : ℝ)*(f.sum) + (3136123221/10000000000000000000000 : ℝ)*base62 + (31723910958431/80000000000000000000000000 : ℝ)*base65 + (20078318934431/80000000000000000000000000 : ℝ)*base67 + (39230197010649/100000000000000000000000000 : ℝ)*base68 + (312825302829559/400000000000000000000000000 : ℝ)*base71 + (9262817713569/80000000000000000000000000 : ℝ)*base72 + (5654593049351/100000000000000000000000000 : ℝ)*base74 + (32723686619351/100000000000000000000000000 : ℝ)*base77 + (1693471337569/40000000000000000000000000 : ℝ)*base78 + (787/2000000000000000 : ℝ)*base86 + (787/2000000000000000 : ℝ)*base88 + (787/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16977/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16977/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13828568989895454711357/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (961185514567/500000000000 : ℝ)*(base39) + (18115603733/40000000000 : ℝ)*(base50) + (327089/1000000000000 : ℝ)*(base60) + (6807579126079/1000000000000 : ℝ)*(major_s0_0) + (18788616398859/1000000000000 : ℝ)*(major_s0_1) + (6807579126079/1000000000000 : ℝ)*(major_s0_2) + (4399997/1000000000000 : ℝ)*(sp_s0_9) + (5201973/200000000000 : ℝ)*(sp_s0_14) + (149965281/500000000000 : ℝ)*(sp_s0_15) + (599051863639/50000000000 : ℝ)*(sp_s0_17) + (1260966321207/125000000000 : ℝ)*(sp_s0_20) + (10087704559791/1000000000000 : ℝ)*(sp_s0_21) + (1260928279887/125000000000 : ℝ)*(sp_s0_22) + (705485167737/200000000000 : ℝ)*(sp_s0_25) + (705485167737/200000000000 : ℝ)*(f.failure) + (1260966321207/125000000000 : ℝ)*(f.sum) + (39594155930187/125000000000000000000000000 : ℝ)*base63 + (95066049712767/2000000000000000000000000000 : ℝ)*base64 + (180257832394293/2000000000000000000000000000 : ℝ)*base67 + (104610402800793/2500000000000000000000000000 : ℝ)*base69 + (1785450535639337/10000000000000000000000000000 : ℝ)*base71 + (1031336269687233/2000000000000000000000000000 : ℝ)*base73 + (627465600552947/2500000000000000000000000000 : ℝ)*base75 + (1507646909550793/2500000000000000000000000000 : ℝ)*base77 + (664329730640763/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1637/2000000000000000 : ℝ)*base86 + (1637/2000000000000000 : ℝ)*base88 + (1637/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (21327/100000 : ℝ) ^ (41/8 : ℝ) ≤ (7274364547911023/20000000000000000000 : ℝ) := by
    have hpowers : (21327/100000 : ℝ)^41 ≤ (7274364547911023/20000000000000000000 : ℝ)^8 := by
      have hnat : (21327 : ℕ)^41*20000000000000000000^8 ≤ 7274364547911023^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21327 100000 7274364547911023 20000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21327/100000 : ℝ)) (X := (7274364547911023/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20007274364547911023/20000000000000000000 : ℝ) ≤ (10000709590243907/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (20007274364547911023/20000000000000000000 : ℝ)^8 ≤ (10000709590243907/10000000000000000 : ℝ)^41 := by
      have hnat : (20007274364547911023 : ℕ)^8*10000000000000000^41 ≤ 10000709590243907^41*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007274364547911023 20000000000000000000 10000709590243907 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000709590243907/10000000000000000 : ℝ)) (X := (20007274364547911023/20000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10007274364547911023/10000000000000000000 : ℝ) ≤ (2500354743215503/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (10007274364547911023/10000000000000000000 : ℝ)^8 ≤ (2500354743215503/2500000000000000 : ℝ)^41 := by
      have hnat : (10007274364547911023 : ℕ)^8*2500000000000000^41 ≤ 2500354743215503^41*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007274364547911023 10000000000000000000 2500354743215503 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500354743215503/2500000000000000 : ℝ)) (X := (10007274364547911023/10000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(709590243907/2132700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(141876523621/426540000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (21327/100000 : ℝ)) (alpha := (709590243907/2132700000000000 : ℝ)) (beta := (141876523621/426540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21327/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(709590243907/2132700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(141876523621/426540000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (31/3125 : ℝ) ^ (41/8 : ℝ) ≤ (5396625981/100000000000000000000 : ℝ) := by
    have hpowers : (31/3125 : ℝ)^41 ≤ (5396625981/100000000000000000000 : ℝ)^8 := by
      have hnat : (31 : ℕ)^41*100000000000000000000^8 ≤ 5396625981^8*3125^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31 3125 5396625981 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31/3125 : ℝ)) (X := (5396625981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000000005396625981/100000000000000000000 : ℝ) ≤ (10000000000105301/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100000000005396625981/100000000000000000000 : ℝ)^8 ≤ (10000000000105301/10000000000000000 : ℝ)^41 := by
      have hnat : (100000000005396625981 : ℕ)^8*10000000000000000^41 ≤ 10000000000105301^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000000005396625981 100000000000000000000 10000000000105301 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000105301/10000000000000000 : ℝ)) (X := (100000000005396625981/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000000005396625981/50000000000000000000 : ℝ) ≤ (10000000000210601/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50000000005396625981/50000000000000000000 : ℝ)^8 ≤ (10000000000210601/10000000000000000 : ℝ)^41 := by
      have hnat : (50000000005396625981 : ℕ)^8*10000000000000000^41 ≤ 10000000000210601^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000005396625981 50000000000000000000 10000000000210601 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000210601/10000000000000000 : ℝ)) (X := (50000000005396625981/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(105301/99200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1053/992000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (31/3125 : ℝ)) (alpha := (105301/99200000000000 : ℝ)) (beta := (1053/992000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (31/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(105301/99200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1053/992000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16977/100000 : ℝ) ^ (41/8 : ℝ) ≤ (11298931139021493/100000000000000000000 : ℝ) := by
    have hpowers : (16977/100000 : ℝ)^41 ≤ (11298931139021493/100000000000000000000 : ℝ)^8 := by
      have hnat : (16977 : ℕ)^41*100000000000000000000^8 ≤ 11298931139021493^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16977 100000 11298931139021493 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16977/100000 : ℝ)) (X := (11298931139021493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100011298931139021493/100000000000000000000 : ℝ) ≤ (2000044091384963/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100011298931139021493/100000000000000000000 : ℝ)^8 ≤ (2000044091384963/2000000000000000 : ℝ)^41 := by
      have hnat : (100011298931139021493 : ℕ)^8*2000000000000000^41 ≤ 2000044091384963^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011298931139021493 100000000000000000000 2000044091384963 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000044091384963/2000000000000000 : ℝ)) (X := (100011298931139021493/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50011298931139021493/50000000000000000000 : ℝ) ≤ (10000440893803877/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50011298931139021493/50000000000000000000 : ℝ)^8 ≤ (10000440893803877/10000000000000000 : ℝ)^41 := by
      have hnat : (50011298931139021493 : ℕ)^8*10000000000000000^41 ≤ 10000440893803877^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011298931139021493 50000000000000000000 10000440893803877 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000440893803877/10000000000000000 : ℝ)) (X := (50011298931139021493/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(14697128321/113180000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(110218439531/848850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (16977/100000 : ℝ)) (alpha := (14697128321/113180000000000 : ℝ)) (beta := (110218439531/848850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16977/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(14697128321/113180000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(110218439531/848850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3343611119/10000000000 : ℝ)*X 0 0+(4582450807/10000000000 : ℝ)*X 0 1+(-4375701807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5759491733/10000000000 : ℝ)*X 1 0+(-2259343157/10000000000 : ℝ)*X 1 1+(-1031355289/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3212118227/10000000000 : ℝ)*X 2 0+(487129259/1000000000 : ℝ)*X 2 1+(840724057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3871381313/10000000000 : ℝ)*X 0 0+(278464391/500000000 : ℝ)*X 0 1+(-2773001353/10000000000 : ℝ)*X 0 2+(3871381313/10000000000 : ℝ)*X 1 0+(278464391/500000000 : ℝ)*X 1 1+(-2773001353/10000000000 : ℝ)*X 1 2+(3871381313/10000000000 : ℝ)*X 2 0+(278464391/500000000 : ℝ)*X 2 1+(-2773001353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-21099950717499355295627109181149/2494249522000000000000000000000 : ℝ) := by norm_num
    linear_combination (27313/1000000000000 : ℝ)*(base11) + (371/500000000000 : ℝ)*(base18) + (39279/1000000000000 : ℝ)*(base25) + (48866637241/100000000000 : ℝ)*(base39) + (621/250000000000 : ℝ)*(base40) + (52786924717/50000000000 : ℝ)*(base49) + (159251161819/250000000000 : ℝ)*(base50) + (8105641329/100000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (2819812843767/1000000000000 : ℝ)*(sp_s1_0) + (2819812870339/1000000000000 : ℝ)*(sp_s1_1) + (2819812831801/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (70495321777/25000000000 : ℝ)*(f.sum) + (1590476510365383/1754290000000000000000000000 : ℝ)*base62 + (26551478045429/56590000000000000000000000 : ℝ)*base65 + (37093053961/310000000000000000000000 : ℝ)*base66 + (33734744968933/56590000000000000000000000 : ℝ)*base68 + (15880259802772313/402298310000000000000000000000 : ℝ)*base71 + (14515250450839/17772500000000000000000000 : ℝ)*base73 + (74547129137/310000000000000000000000 : ℝ)*base74 + (2436118648031/7109000000000000000000000 : ℝ)*base76 + (190757451616997/440758000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p022_b015 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 31)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 := by omega
  rcases hc with rfl
  · exact collision_c322030 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 31)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
