-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:13:49.237092+00:00
-- url     : https://prove2.me/submissions/a7bd1cd6-c47c-4dea-a79a-bf272ac047c1

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
theorem collision_support_c302070_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074306377/5000000000 : ℝ)*x 0 + (-2227790979/5000000000 : ℝ)*x 1 + (-1538880167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074306377/5000000000 : ℝ)^131 ≤ (6535218022633/50000000000000 : ℝ)^99 := by
    have hnat : (1074306377 : ℕ)^131*50000000000000^99 ≤ 6535218022633^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074306377 5000000000 6535218022633 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227790979/5000000000 : ℝ)^131 ≤ (214436652721/625000000000 : ℝ)^99 := by
    have hnat : (2227790979 : ℕ)^131*625000000000^99 ≤ 214436652721^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227790979 5000000000 214436652721 625000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1538880167/2500000000 : ℝ)^131 ≤ (52619699498629/100000000000000 : ℝ)^99 := by
    have hnat : (1538880167 : ℕ)^131*100000000000000^99 ≤ 52619699498629^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538880167 2500000000 52619699498629 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074306377/5000000000 : ℝ), (-2227790979/5000000000 : ℝ), (-1538880167/2500000000 : ℝ)] ![(6535218022633/50000000000000 : ℝ), (214436652721/625000000000 : ℝ), (52619699498629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074306377/5000000000 : ℝ)|^131 ≤ (6535218022633/50000000000000 : ℝ)^99
        have hw : |(-1074306377/5000000000 : ℝ)|=(1074306377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227790979/5000000000 : ℝ)|^131 ≤ (214436652721/625000000000 : ℝ)^99
        have hw : |(-2227790979/5000000000 : ℝ)|=(2227790979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1538880167/2500000000 : ℝ)|^131 ≤ (52619699498629/100000000000000 : ℝ)^99
        have hw : |(-1538880167/2500000000 : ℝ)|=(1538880167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3139053761/5000000000 : ℝ)*x 0 + (4432438947/10000000000 : ℝ)*x 1 + (-2003457637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3139053761/5000000000 : ℝ)^131 ≤ (675134776619/1250000000000 : ℝ)^99 := by
    have hnat : (3139053761 : ℕ)^131*1250000000000^99 ≤ 675134776619^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139053761 5000000000 675134776619 1250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4432438947/10000000000 : ℝ)^131 ≤ (34074248112653/100000000000000 : ℝ)^99 := by
    have hnat : (4432438947 : ℕ)^131*100000000000000^99 ≤ 34074248112653^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432438947 10000000000 34074248112653 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003457637/10000000000 : ℝ)^131 ≤ (11914969745687/100000000000000 : ℝ)^99 := by
    have hnat : (2003457637 : ℕ)^131*100000000000000^99 ≤ 11914969745687^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003457637 10000000000 11914969745687 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3139053761/5000000000 : ℝ), (4432438947/10000000000 : ℝ), (-2003457637/10000000000 : ℝ)] ![(675134776619/1250000000000 : ℝ), (34074248112653/100000000000000 : ℝ), (11914969745687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3139053761/5000000000 : ℝ)|^131 ≤ (675134776619/1250000000000 : ℝ)^99
        have hw : |(3139053761/5000000000 : ℝ)|=(3139053761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4432438947/10000000000 : ℝ)|^131 ≤ (34074248112653/100000000000000 : ℝ)^99
        have hw : |(4432438947/10000000000 : ℝ)|=(4432438947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2003457637/10000000000 : ℝ)|^131 ≤ (11914969745687/100000000000000 : ℝ)^99
        have hw : |(-2003457637/10000000000 : ℝ)|=(2003457637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5195199257/10000000000 : ℝ)*x 0 + (-13595037/62500000 : ℝ)*x 1 + (-5439216241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195199257/10000000000 : ℝ)^131 ≤ (42041252925563/100000000000000 : ℝ)^99 := by
    have hnat : (5195199257 : ℕ)^131*100000000000000^99 ≤ 42041252925563^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195199257 10000000000 42041252925563 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13595037/62500000 : ℝ)^131 ≤ (415153884431/3125000000000 : ℝ)^99 := by
    have hnat : (13595037 : ℕ)^131*3125000000000^99 ≤ 415153884431^99*62500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13595037 62500000 415153884431 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439216241/10000000000 : ℝ)^131 ≤ (44673822758319/100000000000000 : ℝ)^99 := by
    have hnat : (5439216241 : ℕ)^131*100000000000000^99 ≤ 44673822758319^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439216241 10000000000 44673822758319 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195199257/10000000000 : ℝ), (-13595037/62500000 : ℝ), (-5439216241/10000000000 : ℝ)] ![(42041252925563/100000000000000 : ℝ), (415153884431/3125000000000 : ℝ), (44673822758319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195199257/10000000000 : ℝ)|^131 ≤ (42041252925563/100000000000000 : ℝ)^99
        have hw : |(5195199257/10000000000 : ℝ)|=(5195199257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13595037/62500000 : ℝ)|^131 ≤ (415153884431/3125000000000 : ℝ)^99
        have hw : |(-13595037/62500000 : ℝ)|=(13595037/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5439216241/10000000000 : ℝ)|^131 ≤ (44673822758319/100000000000000 : ℝ)^99
        have hw : |(-5439216241/10000000000 : ℝ)|=(5439216241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1627841113/10000000000 : ℝ)*x 0 + (-4925704439/10000000000 : ℝ)*x 1 + (-6080013001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1627841113/10000000000 : ℝ)^131 ≤ (4526364630941/50000000000000 : ℝ)^99 := by
    have hnat : (1627841113 : ℕ)^131*50000000000000^99 ≤ 4526364630941^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627841113 10000000000 4526364630941 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925704439/10000000000 : ℝ)^131 ≤ (19589988600119/50000000000000 : ℝ)^99 := by
    have hnat : (4925704439 : ℕ)^131*50000000000000^99 ≤ 19589988600119^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925704439 10000000000 19589988600119 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6080013001/10000000000 : ℝ)^131 ≤ (51767293526359/100000000000000 : ℝ)^99 := by
    have hnat : (6080013001 : ℕ)^131*100000000000000^99 ≤ 51767293526359^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6080013001 10000000000 51767293526359 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1627841113/10000000000 : ℝ), (-4925704439/10000000000 : ℝ), (-6080013001/10000000000 : ℝ)] ![(4526364630941/50000000000000 : ℝ), (19589988600119/50000000000000 : ℝ), (51767293526359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1627841113/10000000000 : ℝ)|^131 ≤ (4526364630941/50000000000000 : ℝ)^99
        have hw : |(-1627841113/10000000000 : ℝ)|=(1627841113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4925704439/10000000000 : ℝ)|^131 ≤ (19589988600119/50000000000000 : ℝ)^99
        have hw : |(-4925704439/10000000000 : ℝ)|=(4925704439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6080013001/10000000000 : ℝ)|^131 ≤ (51767293526359/100000000000000 : ℝ)^99
        have hw : |(-6080013001/10000000000 : ℝ)|=(6080013001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (389844007/625000000 : ℝ)*x 0 + (4925704439/10000000000 : ℝ)*x 1 + (-1379358157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389844007/625000000 : ℝ)^131 ≤ (53549044275987/100000000000000 : ℝ)^99 := by
    have hnat : (389844007 : ℕ)^131*100000000000000^99 ≤ 53549044275987^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389844007 625000000 53549044275987 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925704439/10000000000 : ℝ)^131 ≤ (19589988600119/50000000000000 : ℝ)^99 := by
    have hnat : (4925704439 : ℕ)^131*50000000000000^99 ≤ 19589988600119^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925704439 10000000000 19589988600119 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379358157/10000000000 : ℝ)^131 ≤ (7270978505821/100000000000000 : ℝ)^99 := by
    have hnat : (1379358157 : ℕ)^131*100000000000000^99 ≤ 7270978505821^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379358157 10000000000 7270978505821 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(389844007/625000000 : ℝ), (4925704439/10000000000 : ℝ), (-1379358157/10000000000 : ℝ)] ![(53549044275987/100000000000000 : ℝ), (19589988600119/50000000000000 : ℝ), (7270978505821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(389844007/625000000 : ℝ)|^131 ≤ (53549044275987/100000000000000 : ℝ)^99
        have hw : |(389844007/625000000 : ℝ)|=(389844007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925704439/10000000000 : ℝ)|^131 ≤ (19589988600119/50000000000000 : ℝ)^99
        have hw : |(4925704439/10000000000 : ℝ)|=(4925704439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1379358157/10000000000 : ℝ)|^131 ≤ (7270978505821/100000000000000 : ℝ)^99
        have hw : |(-1379358157/10000000000 : ℝ)|=(1379358157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (258328003/625000000 : ℝ)*x 0 + (-169893197/400000000 : ℝ)*x 1 + (4691242341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258328003/625000000 : ℝ)^131 ≤ (15532253637103/50000000000000 : ℝ)^99 := by
    have hnat : (258328003 : ℕ)^131*50000000000000^99 ≤ 15532253637103^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258328003 625000000 15532253637103 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169893197/400000000 : ℝ)^131 ≤ (1006377895323/3125000000000 : ℝ)^99 := by
    have hnat : (169893197 : ℕ)^131*3125000000000^99 ≤ 1006377895323^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169893197 400000000 1006377895323 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4691242341/10000000000 : ℝ)^131 ≤ (36731400069239/100000000000000 : ℝ)^99 := by
    have hnat : (4691242341 : ℕ)^131*100000000000000^99 ≤ 36731400069239^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4691242341 10000000000 36731400069239 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258328003/625000000 : ℝ), (-169893197/400000000 : ℝ), (4691242341/10000000000 : ℝ)] ![(15532253637103/50000000000000 : ℝ), (1006377895323/3125000000000 : ℝ), (36731400069239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258328003/625000000 : ℝ)|^131 ≤ (15532253637103/50000000000000 : ℝ)^99
        have hw : |(258328003/625000000 : ℝ)|=(258328003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169893197/400000000 : ℝ)|^131 ≤ (1006377895323/3125000000000 : ℝ)^99
        have hw : |(-169893197/400000000 : ℝ)|=(169893197/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4691242341/10000000000 : ℝ)|^131 ≤ (36731400069239/100000000000000 : ℝ)^99
        have hw : |(4691242341/10000000000 : ℝ)|=(4691242341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5178067947/10000000000 : ℝ)*x 0 + (-124883533/1000000000 : ℝ)*x 1 + (-6080013001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178067947/10000000000 : ℝ)^131 ≤ (167431632781/400000000000 : ℝ)^99 := by
    have hnat : (5178067947 : ℕ)^131*400000000000^99 ≤ 167431632781^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178067947 10000000000 167431632781 400000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124883533/1000000000 : ℝ)^131 ≤ (6374798265053/100000000000000 : ℝ)^99 := by
    have hnat : (124883533 : ℕ)^131*100000000000000^99 ≤ 6374798265053^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124883533 1000000000 6374798265053 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6080013001/10000000000 : ℝ)^131 ≤ (51767293526359/100000000000000 : ℝ)^99 := by
    have hnat : (6080013001 : ℕ)^131*100000000000000^99 ≤ 51767293526359^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6080013001 10000000000 51767293526359 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178067947/10000000000 : ℝ), (-124883533/1000000000 : ℝ), (-6080013001/10000000000 : ℝ)] ![(167431632781/400000000000 : ℝ), (6374798265053/100000000000000 : ℝ), (51767293526359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178067947/10000000000 : ℝ)|^131 ≤ (167431632781/400000000000 : ℝ)^99
        have hw : |(5178067947/10000000000 : ℝ)|=(5178067947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124883533/1000000000 : ℝ)|^131 ≤ (6374798265053/100000000000000 : ℝ)^99
        have hw : |(-124883533/1000000000 : ℝ)|=(124883533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6080013001/10000000000 : ℝ)|^131 ≤ (51767293526359/100000000000000 : ℝ)^99
        have hw : |(-6080013001/10000000000 : ℝ)|=(6080013001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-181117211/1000000000 : ℝ)*x 0 + (-2005460979/5000000000 : ℝ)*x 1 + (-1354691217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181117211/1000000000 : ℝ)^131 ≤ (10425774298363/100000000000000 : ℝ)^99 := by
    have hnat : (181117211 : ℕ)^131*100000000000000^99 ≤ 10425774298363^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181117211 1000000000 10425774298363 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005460979/5000000000 : ℝ)^131 ≤ (29853820461/100000000000 : ℝ)^99 := by
    have hnat : (2005460979 : ℕ)^131*100000000000^99 ≤ 29853820461^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005460979 5000000000 29853820461 100000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354691217/2000000000 : ℝ)^131 ≤ (14930101307041/25000000000000 : ℝ)^99 := by
    have hnat : (1354691217 : ℕ)^131*25000000000000^99 ≤ 14930101307041^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354691217 2000000000 14930101307041 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181117211/1000000000 : ℝ), (-2005460979/5000000000 : ℝ), (-1354691217/2000000000 : ℝ)] ![(10425774298363/100000000000000 : ℝ), (29853820461/100000000000 : ℝ), (14930101307041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181117211/1000000000 : ℝ)|^131 ≤ (10425774298363/100000000000000 : ℝ)^99
        have hw : |(-181117211/1000000000 : ℝ)|=(181117211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005460979/5000000000 : ℝ)|^131 ≤ (29853820461/100000000000 : ℝ)^99
        have hw : |(-2005460979/5000000000 : ℝ)|=(2005460979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1354691217/2000000000 : ℝ)|^131 ≤ (14930101307041/25000000000000 : ℝ)^99
        have hw : |(-1354691217/2000000000 : ℝ)|=(1354691217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6645985183/10000000000 : ℝ)*x 0 + (182230077/400000000 : ℝ)*x 1 + (-157087739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6645985183/10000000000 : ℝ)^131 ≤ (3639861331401/6250000000000 : ℝ)^99 := by
    have hnat : (6645985183 : ℕ)^131*6250000000000^99 ≤ 3639861331401^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6645985183 10000000000 3639861331401 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182230077/400000000 : ℝ)^131 ≤ (17667115529917/50000000000000 : ℝ)^99 := by
    have hnat : (182230077 : ℕ)^131*50000000000000^99 ≤ 17667115529917^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182230077 400000000 17667115529917 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157087739/1250000000 : ℝ)^131 ≤ (1606996904999/25000000000000 : ℝ)^99 := by
    have hnat : (157087739 : ℕ)^131*25000000000000^99 ≤ 1606996904999^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157087739 1250000000 1606996904999 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6645985183/10000000000 : ℝ), (182230077/400000000 : ℝ), (-157087739/1250000000 : ℝ)] ![(3639861331401/6250000000000 : ℝ), (17667115529917/50000000000000 : ℝ), (1606996904999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6645985183/10000000000 : ℝ)|^131 ≤ (3639861331401/6250000000000 : ℝ)^99
        have hw : |(6645985183/10000000000 : ℝ)|=(6645985183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182230077/400000000 : ℝ)|^131 ≤ (17667115529917/50000000000000 : ℝ)^99
        have hw : |(182230077/400000000 : ℝ)|=(182230077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157087739/1250000000 : ℝ)|^131 ≤ (1606996904999/25000000000000 : ℝ)^99
        have hw : |(-157087739/1250000000 : ℝ)|=(157087739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (862110429/2000000000 : ℝ)*x 0 + (-1006618603/2000000000 : ℝ)*x 1 + (462698461/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862110429/2000000000 : ℝ)^131 ≤ (8209980640549/25000000000000 : ℝ)^99 := by
    have hnat : (862110429 : ℕ)^131*25000000000000^99 ≤ 8209980640549^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862110429 2000000000 8209980640549 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006618603/2000000000 : ℝ)^131 ≤ (5039278838343/12500000000000 : ℝ)^99 := by
    have hnat : (1006618603 : ℕ)^131*12500000000000^99 ≤ 5039278838343^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006618603 2000000000 5039278838343 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462698461/1250000000 : ℝ)^131 ≤ (13422923355223/50000000000000 : ℝ)^99 := by
    have hnat : (462698461 : ℕ)^131*50000000000000^99 ≤ 13422923355223^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462698461 1250000000 13422923355223 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862110429/2000000000 : ℝ), (-1006618603/2000000000 : ℝ), (462698461/1250000000 : ℝ)] ![(8209980640549/25000000000000 : ℝ), (5039278838343/12500000000000 : ℝ), (13422923355223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862110429/2000000000 : ℝ)|^131 ≤ (8209980640549/25000000000000 : ℝ)^99
        have hw : |(862110429/2000000000 : ℝ)|=(862110429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006618603/2000000000 : ℝ)|^131 ≤ (5039278838343/12500000000000 : ℝ)^99
        have hw : |(-1006618603/2000000000 : ℝ)|=(1006618603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(462698461/1250000000 : ℝ)|^131 ≤ (13422923355223/50000000000000 : ℝ)^99
        have hw : |(462698461/1250000000 : ℝ)|=(462698461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (180421061/400000000 : ℝ)*x 0 + (-182269773/1250000000 : ℝ)*x 1 + (-3282627691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180421061/400000000 : ℝ)^131 ≤ (17435415976229/50000000000000 : ℝ)^99 := by
    have hnat : (180421061 : ℕ)^131*50000000000000^99 ≤ 17435415976229^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180421061 400000000 17435415976229 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182269773/1250000000 : ℝ)^131 ≤ (7825629285297/100000000000000 : ℝ)^99 := by
    have hnat : (182269773 : ℕ)^131*100000000000000^99 ≤ 7825629285297^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182269773 1250000000 7825629285297 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3282627691/5000000000 : ℝ)^131 ≤ (14325884685613/25000000000000 : ℝ)^99 := by
    have hnat : (3282627691 : ℕ)^131*25000000000000^99 ≤ 14325884685613^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282627691 5000000000 14325884685613 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180421061/400000000 : ℝ), (-182269773/1250000000 : ℝ), (-3282627691/5000000000 : ℝ)] ![(17435415976229/50000000000000 : ℝ), (7825629285297/100000000000000 : ℝ), (14325884685613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180421061/400000000 : ℝ)|^131 ≤ (17435415976229/50000000000000 : ℝ)^99
        have hw : |(180421061/400000000 : ℝ)|=(180421061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182269773/1250000000 : ℝ)|^131 ≤ (7825629285297/100000000000000 : ℝ)^99
        have hw : |(-182269773/1250000000 : ℝ)|=(182269773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3282627691/5000000000 : ℝ)|^131 ≤ (14325884685613/25000000000000 : ℝ)^99
        have hw : |(-3282627691/5000000000 : ℝ)|=(3282627691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-740150777/5000000000 : ℝ)*x 0 + (-4894503731/10000000000 : ℝ)*x 1 + (-310182567/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (740150777/5000000000 : ℝ)^131 ≤ (1596653056847/20000000000000 : ℝ)^99 := by
    have hnat : (740150777 : ℕ)^131*20000000000000^99 ≤ 1596653056847^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740150777 5000000000 1596653056847 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4894503731/10000000000 : ℝ)^131 ≤ (38851918984073/100000000000000 : ℝ)^99 := by
    have hnat : (4894503731 : ℕ)^131*100000000000000^99 ≤ 38851918984073^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4894503731 10000000000 38851918984073 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310182567/500000000 : ℝ)^131 ≤ (6645601964293/12500000000000 : ℝ)^99 := by
    have hnat : (310182567 : ℕ)^131*12500000000000^99 ≤ 6645601964293^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310182567 500000000 6645601964293 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-740150777/5000000000 : ℝ), (-4894503731/10000000000 : ℝ), (-310182567/500000000 : ℝ)] ![(1596653056847/20000000000000 : ℝ), (38851918984073/100000000000000 : ℝ), (6645601964293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-740150777/5000000000 : ℝ)|^131 ≤ (1596653056847/20000000000000 : ℝ)^99
        have hw : |(-740150777/5000000000 : ℝ)|=(740150777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4894503731/10000000000 : ℝ)|^131 ≤ (38851918984073/100000000000000 : ℝ)^99
        have hw : |(-4894503731/10000000000 : ℝ)|=(4894503731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310182567/500000000 : ℝ)|^131 ≤ (6645601964293/12500000000000 : ℝ)^99
        have hw : |(-310182567/500000000 : ℝ)|=(310182567/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6976855139/10000000000 : ℝ)*x 0 + (2012810003/5000000000 : ℝ)*x 1 + (-1468125413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6976855139/10000000000 : ℝ)^131 ≤ (7763105393519/12500000000000 : ℝ)^99 := by
    have hnat : (6976855139 : ℕ)^131*12500000000000^99 ≤ 7763105393519^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6976855139 10000000000 7763105393519 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012810003/5000000000 : ℝ)^131 ≤ (14999333544099/50000000000000 : ℝ)^99 := by
    have hnat : (2012810003 : ℕ)^131*50000000000000^99 ≤ 14999333544099^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012810003 5000000000 14999333544099 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468125413/10000000000 : ℝ)^131 ≤ (3948244870683/50000000000000 : ℝ)^99 := by
    have hnat : (1468125413 : ℕ)^131*50000000000000^99 ≤ 3948244870683^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468125413 10000000000 3948244870683 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6976855139/10000000000 : ℝ), (2012810003/5000000000 : ℝ), (-1468125413/10000000000 : ℝ)] ![(7763105393519/12500000000000 : ℝ), (14999333544099/50000000000000 : ℝ), (3948244870683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6976855139/10000000000 : ℝ)|^131 ≤ (7763105393519/12500000000000 : ℝ)^99
        have hw : |(6976855139/10000000000 : ℝ)|=(6976855139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012810003/5000000000 : ℝ)|^131 ≤ (14999333544099/50000000000000 : ℝ)^99
        have hw : |(2012810003/5000000000 : ℝ)|=(2012810003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1468125413/10000000000 : ℝ)|^131 ≤ (3948244870683/50000000000000 : ℝ)^99
        have hw : |(-1468125413/10000000000 : ℝ)|=(1468125413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3423060723/10000000000 : ℝ)*x 0 + (-2642619601/5000000000 : ℝ)*x 1 + (2152598313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3423060723/10000000000 : ℝ)^131 ≤ (12102981187359/50000000000000 : ℝ)^99 := by
    have hnat : (3423060723 : ℕ)^131*50000000000000^99 ≤ 12102981187359^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423060723 10000000000 12102981187359 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2642619601/5000000000 : ℝ)^131 ≤ (10752023351887/25000000000000 : ℝ)^99 := by
    have hnat : (2642619601 : ℕ)^131*25000000000000^99 ≤ 10752023351887^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642619601 5000000000 10752023351887 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152598313/5000000000 : ℝ)^131 ≤ (327859442067/1000000000000 : ℝ)^99 := by
    have hnat : (2152598313 : ℕ)^131*1000000000000^99 ≤ 327859442067^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152598313 5000000000 327859442067 1000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3423060723/10000000000 : ℝ), (-2642619601/5000000000 : ℝ), (2152598313/5000000000 : ℝ)] ![(12102981187359/50000000000000 : ℝ), (10752023351887/25000000000000 : ℝ), (327859442067/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3423060723/10000000000 : ℝ)|^131 ≤ (12102981187359/50000000000000 : ℝ)^99
        have hw : |(3423060723/10000000000 : ℝ)|=(3423060723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2642619601/5000000000 : ℝ)|^131 ≤ (10752023351887/25000000000000 : ℝ)^99
        have hw : |(-2642619601/5000000000 : ℝ)|=(2642619601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2152598313/5000000000 : ℝ)|^131 ≤ (327859442067/1000000000000 : ℝ)^99
        have hw : |(2152598313/5000000000 : ℝ)|=(2152598313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s0_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6270776431/10000000000 : ℝ)*x 0 + (-82954177/500000000 : ℝ)*x 1 + (-2348415519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6270776431/10000000000 : ℝ)^131 ≤ (26963671051087/50000000000000 : ℝ)^99 := by
    have hnat : (6270776431 : ℕ)^131*50000000000000^99 ≤ 26963671051087^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6270776431 10000000000 26963671051087 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82954177/500000000 : ℝ)^131 ≤ (4641672153603/50000000000000 : ℝ)^99 := by
    have hnat : (82954177 : ℕ)^131*50000000000000^99 ≤ 4641672153603^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82954177 500000000 4641672153603 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2348415519/5000000000 : ℝ)^131 ≤ (4598664197039/12500000000000 : ℝ)^99 := by
    have hnat : (2348415519 : ℕ)^131*12500000000000^99 ≤ 4598664197039^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348415519 5000000000 4598664197039 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6270776431/10000000000 : ℝ), (-82954177/500000000 : ℝ), (-2348415519/5000000000 : ℝ)] ![(26963671051087/50000000000000 : ℝ), (4641672153603/50000000000000 : ℝ), (4598664197039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6270776431/10000000000 : ℝ)|^131 ≤ (26963671051087/50000000000000 : ℝ)^99
        have hw : |(6270776431/10000000000 : ℝ)|=(6270776431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82954177/500000000 : ℝ)|^131 ≤ (4641672153603/50000000000000 : ℝ)^99
        have hw : |(-82954177/500000000 : ℝ)|=(82954177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2348415519/5000000000 : ℝ)|^131 ≤ (4598664197039/12500000000000 : ℝ)^99
        have hw : |(-2348415519/5000000000 : ℝ)|=(2348415519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3508682643/10000000000 : ℝ)*x 0 + (-2110114833/5000000000 : ℝ)*x 1 + (-5289795687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3508682643/10000000000 : ℝ)^131 ≤ (5002072143103/20000000000000 : ℝ)^99 := by
    have hnat : (3508682643 : ℕ)^131*20000000000000^99 ≤ 5002072143103^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3508682643 10000000000 5002072143103 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110114833/5000000000 : ℝ)^131 ≤ (6386495262349/20000000000000 : ℝ)^99 := by
    have hnat : (2110114833 : ℕ)^131*20000000000000^99 ≤ 6386495262349^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110114833 5000000000 6386495262349 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5289795687/10000000000 : ℝ)^131 ≤ (86114325917/200000000000 : ℝ)^99 := by
    have hnat : (5289795687 : ℕ)^131*200000000000^99 ≤ 86114325917^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289795687 10000000000 86114325917 200000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3508682643/10000000000 : ℝ), (-2110114833/5000000000 : ℝ), (-5289795687/10000000000 : ℝ)] ![(5002072143103/20000000000000 : ℝ), (6386495262349/20000000000000 : ℝ), (86114325917/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3508682643/10000000000 : ℝ)|^131 ≤ (5002072143103/20000000000000 : ℝ)^99
        have hw : |(-3508682643/10000000000 : ℝ)|=(3508682643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110114833/5000000000 : ℝ)|^131 ≤ (6386495262349/20000000000000 : ℝ)^99
        have hw : |(-2110114833/5000000000 : ℝ)|=(2110114833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5289795687/10000000000 : ℝ)|^131 ≤ (86114325917/200000000000 : ℝ)^99
        have hw : |(-5289795687/10000000000 : ℝ)|=(5289795687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2643091089/5000000000 : ℝ)*x 0 + (1056371709/2500000000 : ℝ)*x 1 + (-1753613381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643091089/5000000000 : ℝ)^131 ≤ (1075456183813/2500000000000 : ℝ)^99 := by
    have hnat : (2643091089 : ℕ)^131*2500000000000^99 ≤ 1075456183813^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643091089 5000000000 1075456183813 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056371709/2500000000 : ℝ)^131 ≤ (31985123118701/100000000000000 : ℝ)^99 := by
    have hnat : (1056371709 : ℕ)^131*100000000000000^99 ≤ 31985123118701^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056371709 2500000000 31985123118701 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1753613381/5000000000 : ℝ)^131 ≤ (3124578688547/12500000000000 : ℝ)^99 := by
    have hnat : (1753613381 : ℕ)^131*12500000000000^99 ≤ 3124578688547^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753613381 5000000000 3124578688547 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643091089/5000000000 : ℝ), (1056371709/2500000000 : ℝ), (-1753613381/5000000000 : ℝ)] ![(1075456183813/2500000000000 : ℝ), (31985123118701/100000000000000 : ℝ), (3124578688547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643091089/5000000000 : ℝ)|^131 ≤ (1075456183813/2500000000000 : ℝ)^99
        have hw : |(2643091089/5000000000 : ℝ)|=(2643091089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056371709/2500000000 : ℝ)|^131 ≤ (31985123118701/100000000000000 : ℝ)^99
        have hw : |(1056371709/2500000000 : ℝ)|=(1056371709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1753613381/5000000000 : ℝ)|^131 ≤ (3124578688547/12500000000000 : ℝ)^99
        have hw : |(-1753613381/5000000000 : ℝ)|=(1753613381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2040113617/5000000000 : ℝ)*x 0 + (-4907681249/10000000000 : ℝ)*x 1 + (4073459861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040113617/5000000000 : ℝ)^131 ≤ (6107661282189/20000000000000 : ℝ)^99 := by
    have hnat : (2040113617 : ℕ)^131*20000000000000^99 ≤ 6107661282189^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040113617 5000000000 6107661282189 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4907681249/10000000000 : ℝ)^131 ≤ (19495195552559/50000000000000 : ℝ)^99 := by
    have hnat : (4907681249 : ℕ)^131*50000000000000^99 ≤ 19495195552559^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907681249 10000000000 19495195552559 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4073459861/10000000000 : ℝ)^131 ≤ (6094260494211/20000000000000 : ℝ)^99 := by
    have hnat : (4073459861 : ℕ)^131*20000000000000^99 ≤ 6094260494211^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4073459861 10000000000 6094260494211 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2040113617/5000000000 : ℝ), (-4907681249/10000000000 : ℝ), (4073459861/10000000000 : ℝ)] ![(6107661282189/20000000000000 : ℝ), (19495195552559/50000000000000 : ℝ), (6094260494211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2040113617/5000000000 : ℝ)|^131 ≤ (6107661282189/20000000000000 : ℝ)^99
        have hw : |(2040113617/5000000000 : ℝ)|=(2040113617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4907681249/10000000000 : ℝ)|^131 ≤ (19495195552559/50000000000000 : ℝ)^99
        have hw : |(-4907681249/10000000000 : ℝ)|=(4907681249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4073459861/10000000000 : ℝ)|^131 ≤ (6094260494211/20000000000000 : ℝ)^99
        have hw : |(4073459861/10000000000 : ℝ)|=(4073459861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302070_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4660724909/10000000000 : ℝ)*x 0 + (-149021211/400000000 : ℝ)*x 1 + (-145928773/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4660724909/10000000000 : ℝ)^131 ≤ (18207776738737/50000000000000 : ℝ)^99 := by
    have hnat : (4660724909 : ℕ)^131*50000000000000^99 ≤ 18207776738737^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4660724909 10000000000 18207776738737 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149021211/400000000 : ℝ)^131 ≤ (27075858098233/100000000000000 : ℝ)^99 := by
    have hnat : (149021211 : ℕ)^131*100000000000000^99 ≤ 27075858098233^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149021211 400000000 27075858098233 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145928773/312500000 : ℝ)^131 ≤ (456357355093/1250000000000 : ℝ)^99 := by
    have hnat : (145928773 : ℕ)^131*1250000000000^99 ≤ 456357355093^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145928773 312500000 456357355093 1250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4660724909/10000000000 : ℝ), (-149021211/400000000 : ℝ), (-145928773/312500000 : ℝ)] ![(18207776738737/50000000000000 : ℝ), (27075858098233/100000000000000 : ℝ), (456357355093/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4660724909/10000000000 : ℝ)|^131 ≤ (18207776738737/50000000000000 : ℝ)^99
        have hw : |(4660724909/10000000000 : ℝ)|=(4660724909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149021211/400000000 : ℝ)|^131 ≤ (27075858098233/100000000000000 : ℝ)^99
        have hw : |(-149021211/400000000 : ℝ)|=(149021211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145928773/312500000 : ℝ)|^131 ≤ (456357355093/1250000000000 : ℝ)^99
        have hw : |(-145928773/312500000 : ℝ)|=(145928773/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302070 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
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
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
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
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1074306377/5000000000 : ℝ)*X 0 0+(-2227790979/5000000000 : ℝ)*X 0 1+(-1538880167/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3139053761/5000000000 : ℝ)*X 1 0+(4432438947/10000000000 : ℝ)*X 1 1+(-2003457637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5195199257/10000000000 : ℝ)*X 0 0+(-13595037/62500000 : ℝ)*X 0 1+(-5439216241/10000000000 : ℝ)*X 0 2+(5195199257/10000000000 : ℝ)*X 1 0+(-13595037/62500000 : ℝ)*X 1 1+(-5439216241/10000000000 : ℝ)*X 1 2+(5195199257/10000000000 : ℝ)*X 2 0+(-13595037/62500000 : ℝ)*X 2 1+(-5439216241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1627841113/10000000000 : ℝ)*X 0 0+(-4925704439/10000000000 : ℝ)*X 0 1+(-6080013001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((389844007/625000000 : ℝ)*X 1 0+(4925704439/10000000000 : ℝ)*X 1 1+(-1379358157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((258328003/625000000 : ℝ)*X 2 0+(-169893197/400000000 : ℝ)*X 2 1+(4691242341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((5178067947/10000000000 : ℝ)*X 0 0+(-124883533/1000000000 : ℝ)*X 0 1+(-6080013001/10000000000 : ℝ)*X 0 2+(5178067947/10000000000 : ℝ)*X 1 0+(-124883533/1000000000 : ℝ)*X 1 1+(-6080013001/10000000000 : ℝ)*X 1 2+(5178067947/10000000000 : ℝ)*X 2 0+(-124883533/1000000000 : ℝ)*X 2 1+(-6080013001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-181117211/1000000000 : ℝ)*X 0 0+(-2005460979/5000000000 : ℝ)*X 0 1+(-1354691217/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6645985183/10000000000 : ℝ)*X 1 0+(182230077/400000000 : ℝ)*X 1 1+(-157087739/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((862110429/2000000000 : ℝ)*X 2 0+(-1006618603/2000000000 : ℝ)*X 2 1+(462698461/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((180421061/400000000 : ℝ)*X 0 0+(-182269773/1250000000 : ℝ)*X 0 1+(-3282627691/5000000000 : ℝ)*X 0 2+(180421061/400000000 : ℝ)*X 1 0+(-182269773/1250000000 : ℝ)*X 1 1+(-3282627691/5000000000 : ℝ)*X 1 2+(180421061/400000000 : ℝ)*X 2 0+(-182269773/1250000000 : ℝ)*X 2 1+(-3282627691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-740150777/5000000000 : ℝ)*X 0 0+(-4894503731/10000000000 : ℝ)*X 0 1+(-310182567/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6976855139/10000000000 : ℝ)*X 1 0+(2012810003/5000000000 : ℝ)*X 1 1+(-1468125413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3423060723/10000000000 : ℝ)*X 2 0+(-2642619601/5000000000 : ℝ)*X 2 1+(2152598313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6270776431/10000000000 : ℝ)*X 0 0+(-82954177/500000000 : ℝ)*X 0 1+(-2348415519/5000000000 : ℝ)*X 0 2+(6270776431/10000000000 : ℝ)*X 1 0+(-82954177/500000000 : ℝ)*X 1 1+(-2348415519/5000000000 : ℝ)*X 1 2+(6270776431/10000000000 : ℝ)*X 2 0+(-82954177/500000000 : ℝ)*X 2 1+(-2348415519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4177/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4177/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (75763437887168073450927/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14266620389/40000000000 : ℝ)*(base1) + (137149034081/500000000000 : ℝ)*(base3) + (120590643081/62500000000 : ℝ)*(base39) + (2855377/500000000000 : ℝ)*(base49) + (664903470353/1000000000000 : ℝ)*(base59) + (5566002040583/1000000000000 : ℝ)*(major_s0_0) + (5566002040583/1000000000000 : ℝ)*(major_s0_1) + (5566002040583/1000000000000 : ℝ)*(major_s0_2) + (7235669/200000000000 : ℝ)*(sp_s0_1) + (7756528419319/1000000000000 : ℝ)*(sp_s0_7) + (959368285673/125000000000 : ℝ)*(sp_s0_8) + (7400684395567/1000000000000 : ℝ)*(sp_s0_9) + (1550175528407/500000000000 : ℝ)*(sp_s0_13) + (821485973/1000000000000 : ℝ)*(sp_s0_21) + (3731314634701/1000000000000 : ℝ)*(f.failure) + (7400684395567/1000000000000 : ℝ)*(f.sum) + (904315296691581/5000000000000000000000000000 : ℝ)*base62 + (4439870063466529/10000000000000000000000000000 : ℝ)*base64 + (18543764849691/10000000000000000000000000000 : ℝ)*base67 + (1969535767849691/10000000000000000000000000000 : ℝ)*base68 + (278324973515811/500000000000000000000000000 : ℝ)*base70 + (399555879533471/10000000000000000000000000000 : ℝ)*base73 + (1847313086533471/10000000000000000000000000000 : ℝ)*base74 + (300196283150309/10000000000000000000000000000 : ℝ)*base77 + (120704854308419/5000000000000000000000000000 : ℝ)*base78 + (4817/10000000000000000 : ℝ)*base87 + (4817/10000000000000000 : ℝ)*base89 + (4817/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-30381/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-30381/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39758676167003660912727/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173443767883/100000000000 : ℝ)*(base39) + (1276518951177/1000000000000 : ℝ)*(base59) + (3232249476697/500000000000 : ℝ)*(major_s0_0) + (3232249476697/500000000000 : ℝ)*(major_s0_1) + (3232249476697/500000000000 : ℝ)*(major_s0_2) + (21905001/200000000000 : ℝ)*(sp_s0_0) + (51099251/500000000000 : ℝ)*(sp_s0_1) + (50660653/1000000000000 : ℝ)*(sp_s0_9) + (5628221/125000000000 : ℝ)*(sp_s0_13) + (8595237606737/1000000000000 : ℝ)*(sp_s0_14) + (8595120789981/1000000000000 : ℝ)*(sp_s0_15) + (8595296471089/1000000000000 : ℝ)*(sp_s0_16) + (4333600448117/1000000000000 : ℝ)*(sp_s0_20) + (6207163/50000000000 : ℝ)*(sp_s0_22) + (866729094777/200000000000 : ℝ)*(f.failure) + (4297673565871/500000000000 : ℝ)*(f.sum) + (427773393879379/2500000000000000000000000000 : ℝ)*base62 + (3523616076090111/5000000000000000000000000000 : ℝ)*base64 + (1141664951151131/5000000000000000000000000000 : ℝ)*base66 + (1976377539348869/5000000000000000000000000000 : ℝ)*base68 + (170880000446949/250000000000000000000000000 : ℝ)*base70 + (1483575334090111/5000000000000000000000000000 : ℝ)*base72 + (680046493090111/5000000000000000000000000000 : ℝ)*base75 + (1114344661348869/5000000000000000000000000000 : ℝ)*base76 + (211696187120621/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (509/2000000000000000 : ℝ)*base87 + (509/2000000000000000 : ℝ)*base89 + (509/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28597/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28597/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38666395739817376871733/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (492487569183/250000000000 : ℝ)*(base39) + (2763491/500000000000 : ℝ)*(base49) + (700702523287/1000000000000 : ℝ)*(base59) + (6173064751227/1000000000000 : ℝ)*(major_s0_0) + (6173064751227/1000000000000 : ℝ)*(major_s0_1) + (6173064751227/1000000000000 : ℝ)*(major_s0_2) + (77268157/1000000000000 : ℝ)*(sp_s0_6) + (381981407/500000000000 : ℝ)*(sp_s0_7) + (7928673/200000000000 : ℝ)*(sp_s0_15) + (52046639/1000000000000 : ℝ)*(sp_s0_16) + (128235709821/15625000000 : ℝ)*(sp_s0_21) + (8207809747993/1000000000000 : ℝ)*(sp_s0_22) + (8207797344719/1000000000000 : ℝ)*(sp_s0_23) + (827639537483/200000000000 : ℝ)*(sp_s0_27) + (1034568738893/250000000000 : ℝ)*(f.failure) + (4103924695679/500000000000 : ℝ)*(f.sum) + (2572537864376089/5000000000000000000000000000 : ℝ)*base62 + (5865137484703501/10000000000000000000000000000 : ℝ)*base64 + (4402646711544321/10000000000000000000000000000 : ℝ)*base66 + (4148843056544321/10000000000000000000000000000 : ℝ)*base69 + (44278849257959/500000000000000000000000000 : ℝ)*base70 + (2119879561296499/10000000000000000000000000000 : ℝ)*base73 + (2022032671296499/10000000000000000000000000000 : ℝ)*base74 + (3279295544455679/10000000000000000000000000000 : ℝ)*base76 + (2715877876876089/5000000000000000000000000000 : ℝ)*base79 + (619/2500000000000000 : ℝ)*base86 + (619/2500000000000000 : ℝ)*base88 + (619/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (4177/20000 : ℝ) ^ (65/16 : ℝ) ≤ (86257641190646519/50000000000000000000 : ℝ) := by
    have hpowers : (4177/20000 : ℝ)^65 ≤ (86257641190646519/50000000000000000000 : ℝ)^16 := by
      have hnat : (4177 : ℕ)^65*50000000000000000000^16 ≤ 86257641190646519^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4177 20000 86257641190646519 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4177/20000 : ℝ)) (X := (86257641190646519/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50086257641190646519/50000000000000000000 : ℝ) ≤ (10004243771503691/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50086257641190646519/50000000000000000000 : ℝ)^16 ≤ (10004243771503691/10000000000000000 : ℝ)^65 := by
      have hnat : (50086257641190646519 : ℕ)^16*10000000000000000^65 ≤ 10004243771503691^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086257641190646519 50000000000000000000 10004243771503691 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004243771503691/10000000000000000 : ℝ)) (X := (50086257641190646519/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25086257641190646519/25000000000000000000 : ℝ) ≤ (5004241018529583/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25086257641190646519/25000000000000000000 : ℝ)^16 ≤ (5004241018529583/5000000000000000 : ℝ)^65 := by
      have hnat : (25086257641190646519 : ℕ)^16*5000000000000000^65 ≤ 5004241018529583^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25086257641190646519 25000000000000000000 5004241018529583 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004241018529583/5000000000000000 : ℝ)) (X := (25086257641190646519/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4243771503691/2088500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(169530622219/83540000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (4177/20000 : ℝ)) (alpha := (4243771503691/2088500000000000 : ℝ)) (beta := (169530622219/83540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4177/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4243771503691/2088500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(169530622219/83540000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30381/100000 : ℝ) ^ (65/16 : ℝ) ≤ (395403848638231561/50000000000000000000 : ℝ) := by
    have hpowers : (30381/100000 : ℝ)^65 ≤ (395403848638231561/50000000000000000000 : ℝ)^16 := by
      have hnat : (30381 : ℕ)^65*50000000000000000000^16 ≤ 395403848638231561^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30381 100000 395403848638231561 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30381/100000 : ℝ)) (X := (395403848638231561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50395403848638231561/50000000000000000000 : ℝ) ≤ (10019408279298083/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50395403848638231561/50000000000000000000 : ℝ)^16 ≤ (10019408279298083/10000000000000000 : ℝ)^65 := by
      have hnat : (50395403848638231561 : ℕ)^16*10000000000000000^65 ≤ 10019408279298083^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50395403848638231561 50000000000000000000 10019408279298083 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019408279298083/10000000000000000 : ℝ)) (X := (50395403848638231561/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25395403848638231561/25000000000000000000 : ℝ) ≤ (10038702101661963/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25395403848638231561/25000000000000000000 : ℝ)^16 ≤ (10038702101661963/10000000000000000 : ℝ)^65 := by
      have hnat : (25395403848638231561 : ℕ)^16*10000000000000000^65 ≤ 10038702101661963^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25395403848638231561 25000000000000000000 10038702101661963 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10038702101661963/10000000000000000 : ℝ)) (X := (25395403848638231561/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1492944561391/233700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(482345559097/75952500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (30381/100000 : ℝ)) (alpha := (1492944561391/233700000000000 : ℝ)) (beta := (482345559097/75952500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (30381/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1492944561391/233700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(482345559097/75952500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (28597/100000 : ℝ) ^ (65/16 : ℝ) ≤ (309223104155042703/50000000000000000000 : ℝ) := by
    have hpowers : (28597/100000 : ℝ)^65 ≤ (309223104155042703/50000000000000000000 : ℝ)^16 := by
      have hnat : (28597 : ℕ)^65*50000000000000000000^16 ≤ 309223104155042703^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28597 100000 309223104155042703 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28597/100000 : ℝ)) (X := (309223104155042703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50309223104155042703/50000000000000000000 : ℝ) ≤ (5007593966268159/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50309223104155042703/50000000000000000000 : ℝ)^16 ≤ (5007593966268159/5000000000000000 : ℝ)^65 := by
      have hnat : (50309223104155042703 : ℕ)^16*5000000000000000^65 ≤ 5007593966268159^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50309223104155042703 50000000000000000000 5007593966268159 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007593966268159/5000000000000000 : ℝ)) (X := (50309223104155042703/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25309223104155042703/25000000000000000000 : ℝ) ≤ (401212226172301/400000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25309223104155042703/25000000000000000000 : ℝ)^16 ≤ (401212226172301/400000000000000 : ℝ)^65 := by
      have hnat : (25309223104155042703 : ℕ)^16*400000000000000^65 ≤ 401212226172301^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25309223104155042703 25000000000000000000 401212226172301 400000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401212226172301/400000000000000 : ℝ)) (X := (25309223104155042703/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(7593966268159/1429850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(15117721771207/2859700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (28597/100000 : ℝ)) (alpha := (7593966268159/1429850000000000 : ℝ)) (beta := (15117721771207/2859700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28597/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(7593966268159/1429850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(15117721771207/2859700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3508682643/10000000000 : ℝ)*X 0 0+(-2110114833/5000000000 : ℝ)*X 0 1+(-5289795687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2643091089/5000000000 : ℝ)*X 1 0+(1056371709/2500000000 : ℝ)*X 1 1+(-1753613381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2040113617/5000000000 : ℝ)*X 2 0+(-4907681249/10000000000 : ℝ)*X 2 1+(4073459861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4660724909/10000000000 : ℝ)*X 0 0+(-149021211/400000000 : ℝ)*X 0 1+(-145928773/312500000 : ℝ)*X 0 2+(4660724909/10000000000 : ℝ)*X 1 0+(-149021211/400000000 : ℝ)*X 1 1+(-145928773/312500000 : ℝ)*X 1 2+(4660724909/10000000000 : ℝ)*X 2 0+(-149021211/400000000 : ℝ)*X 2 1+(-145928773/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302070_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-177384896699509720083390596507000873/30241669949075000000000000000000000 : ℝ) := by norm_num
    linear_combination (516403/500000000000 : ℝ)*(base1) + (298843/200000000000 : ℝ)*(base22) + (433453/500000000000 : ℝ)*(base25) + (98508087041/200000000000 : ℝ)*(base39) + (156569853523/1000000000000 : ℝ)*(base40) + (218392881583/1000000000000 : ℝ)*(base49) + (329961/1000000000000 : ℝ)*(base54) + (286124901603/1000000000000 : ℝ)*(base59) + (14917/10000 : ℝ)*(major_s1_0) + (14917/10000 : ℝ)*(major_s1_1) + (1491699670039/1000000000000 : ℝ)*(major_s1_2) + (195519395037/100000000000 : ℝ)*(sp_s1_0) + (488798229391/250000000000 : ℝ)*(sp_s1_1) + (977595113241/500000000000 : ℝ)*(sp_s1_2) + (999998637233/1000000000000 : ℝ)*(sp_s1_6) + (488798229391/250000000000 : ℝ)*(f.sum) + (4692974939147223607/21720136425000000000000000000000 : ℝ)*base62 + (816793840172223/2859700000000000000000000000 : ℝ)*base65 + (276548043257/11685000000000000000000000 : ℝ)*base66 + (2849184842741/357462500000000000000000000 : ℝ)*base68 + (1348781739579036089/11944966900000000000000000000000 : ℝ)*base70 + (4435652727039/5221250000000000000000000 : ℝ)*base73 + (17777140395977/60762000000000000000000000 : ℝ)*base74 + (31770915006539/41770000000000000000000000 : ℝ)*base76 + (32272065101618707/48808245000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b029 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 := by omega
  rcases hc with rfl
  · exact collision_c302070 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
