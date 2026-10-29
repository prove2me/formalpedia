-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:00.171648+00:00
-- url     : https://prove2.me/submissions/66e6a86b-fc31-4b79-9bcd-d7fb9b9d1dde

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
theorem collision_support_c328070_s0_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190374509/10000000000 : ℝ)*x 0 + (-3714074269/10000000000 : ℝ)*x 1 + (-5984683157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190374509/10000000000 : ℝ)^93 ≤ (1997069813101/12500000000000 : ℝ)^77 := by
    have hnat : (2190374509 : ℕ)^93*12500000000000^77 ≤ 1997069813101^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190374509 10000000000 1997069813101 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3714074269/10000000000 : ℝ)^93 ≤ (30232139792111/100000000000000 : ℝ)^77 := by
    have hnat : (3714074269 : ℕ)^93*100000000000000^77 ≤ 30232139792111^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714074269 10000000000 30232139792111 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5984683157/10000000000 : ℝ)^93 ≤ (26895650839401/50000000000000 : ℝ)^77 := by
    have hnat : (5984683157 : ℕ)^93*50000000000000^77 ≤ 26895650839401^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984683157 10000000000 26895650839401 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190374509/10000000000 : ℝ), (-3714074269/10000000000 : ℝ), (-5984683157/10000000000 : ℝ)] ![(1997069813101/12500000000000 : ℝ), (30232139792111/100000000000000 : ℝ), (26895650839401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190374509/10000000000 : ℝ)|^93 ≤ (1997069813101/12500000000000 : ℝ)^77
        have hw : |(-2190374509/10000000000 : ℝ)|=(2190374509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3714074269/10000000000 : ℝ)|^93 ≤ (30232139792111/100000000000000 : ℝ)^77
        have hw : |(-3714074269/10000000000 : ℝ)|=(3714074269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5984683157/10000000000 : ℝ)|^93 ≤ (26895650839401/50000000000000 : ℝ)^77
        have hw : |(-5984683157/10000000000 : ℝ)|=(5984683157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328070_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1496170829/2500000000 : ℝ)*x 0 + (928518563/2500000000 : ℝ)*x 1 + (-2190374333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1496170829/2500000000 : ℝ)^93 ≤ (53791303404879/100000000000000 : ℝ)^77 := by
    have hnat : (1496170829 : ℕ)^93*100000000000000^77 ≤ 53791303404879^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496170829 2500000000 53791303404879 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (928518563/2500000000 : ℝ)^93 ≤ (30232139624979/100000000000000 : ℝ)^77 := by
    have hnat : (928518563 : ℕ)^93*100000000000000^77 ≤ 30232139624979^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928518563 2500000000 30232139624979 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190374333/10000000000 : ℝ)^93 ≤ (3195311390863/20000000000000 : ℝ)^77 := by
    have hnat : (2190374333 : ℕ)^93*20000000000000^77 ≤ 3195311390863^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190374333 10000000000 3195311390863 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1496170829/2500000000 : ℝ), (928518563/2500000000 : ℝ), (-2190374333/10000000000 : ℝ)] ![(53791303404879/100000000000000 : ℝ), (30232139624979/100000000000000 : ℝ), (3195311390863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1496170829/2500000000 : ℝ)|^93 ≤ (53791303404879/100000000000000 : ℝ)^77
        have hw : |(1496170829/2500000000 : ℝ)|=(1496170829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(928518563/2500000000 : ℝ)|^93 ≤ (30232139624979/100000000000000 : ℝ)^77
        have hw : |(928518563/2500000000 : ℝ)|=(928518563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190374333/10000000000 : ℝ)|^93 ≤ (3195311390863/20000000000000 : ℝ)^77
        have hw : |(-2190374333/10000000000 : ℝ)|=(2190374333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328070_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (883296801/2500000000 : ℝ)*x 0 + (-4979062241/10000000000 : ℝ)*x 1 + (3533186937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883296801/2500000000 : ℝ)^93 ≤ (711572585773/2500000000000 : ℝ)^77 := by
    have hnat : (883296801 : ℕ)^93*2500000000000^77 ≤ 711572585773^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883296801 2500000000 711572585773 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979062241/10000000000 : ℝ)^93 ≤ (21537097861499/50000000000000 : ℝ)^77 := by
    have hnat : (4979062241 : ℕ)^93*50000000000000^77 ≤ 21537097861499^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979062241 10000000000 21537097861499 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3533186937/10000000000 : ℝ)^93 ≤ (14231450416529/50000000000000 : ℝ)^77 := by
    have hnat : (3533186937 : ℕ)^93*50000000000000^77 ≤ 14231450416529^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3533186937 10000000000 14231450416529 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(883296801/2500000000 : ℝ), (-4979062241/10000000000 : ℝ), (3533186937/10000000000 : ℝ)] ![(711572585773/2500000000000 : ℝ), (21537097861499/50000000000000 : ℝ), (14231450416529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(883296801/2500000000 : ℝ)|^93 ≤ (711572585773/2500000000000 : ℝ)^77
        have hw : |(883296801/2500000000 : ℝ)|=(883296801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4979062241/10000000000 : ℝ)|^93 ≤ (21537097861499/50000000000000 : ℝ)^77
        have hw : |(-4979062241/10000000000 : ℝ)|=(4979062241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3533186937/10000000000 : ℝ)|^93 ≤ (14231450416529/50000000000000 : ℝ)^77
        have hw : |(3533186937/10000000000 : ℝ)|=(3533186937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328070_s0_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4762815293/10000000000 : ℝ)*x 0 + (-30706609/125000000 : ℝ)*x 1 + (-595351893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4762815293/10000000000 : ℝ)^93 ≤ (40825013276971/100000000000000 : ℝ)^77 := by
    have hnat : (4762815293 : ℕ)^93*100000000000000^77 ≤ 40825013276971^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762815293 10000000000 40825013276971 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30706609/125000000 : ℝ)^93 ≤ (18349974974211/100000000000000 : ℝ)^77 := by
    have hnat : (30706609 : ℕ)^93*100000000000000^77 ≤ 18349974974211^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30706609 125000000 18349974974211 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595351893/1250000000 : ℝ)^93 ≤ (20412505867207/50000000000000 : ℝ)^77 := by
    have hnat : (595351893 : ℕ)^93*50000000000000^77 ≤ 20412505867207^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595351893 1250000000 20412505867207 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4762815293/10000000000 : ℝ), (-30706609/125000000 : ℝ), (-595351893/1250000000 : ℝ)] ![(40825013276971/100000000000000 : ℝ), (18349974974211/100000000000000 : ℝ), (20412505867207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4762815293/10000000000 : ℝ)|^93 ≤ (40825013276971/100000000000000 : ℝ)^77
        have hw : |(4762815293/10000000000 : ℝ)|=(4762815293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30706609/125000000 : ℝ)|^93 ≤ (18349974974211/100000000000000 : ℝ)^77
        have hw : |(-30706609/125000000 : ℝ)|=(30706609/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-595351893/1250000000 : ℝ)|^93 ≤ (20412505867207/50000000000000 : ℝ)^77
        have hw : |(-595351893/1250000000 : ℝ)|=(595351893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328070 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2190374509/10000000000 : ℝ)*X 0 0+(-3714074269/10000000000 : ℝ)*X 0 1+(-5984683157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1496170829/2500000000 : ℝ)*X 1 0+(928518563/2500000000 : ℝ)*X 1 1+(-2190374333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((883296801/2500000000 : ℝ)*X 2 0+(-4979062241/10000000000 : ℝ)*X 2 1+(3533186937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4762815293/10000000000 : ℝ)*X 0 0+(-30706609/125000000 : ℝ)*X 0 1+(-595351893/1250000000 : ℝ)*X 0 2+(4762815293/10000000000 : ℝ)*X 1 0+(-30706609/125000000 : ℝ)*X 1 1+(-595351893/1250000000 : ℝ)*X 1 2+(4762815293/10000000000 : ℝ)*X 2 0+(-30706609/125000000 : ℝ)*X 2 1+(-595351893/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-49493564984383387251617039499/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34441/500000000000 : ℝ)*(base12) + (160119/1000000000000 : ℝ)*(base15) + (23953/1000000000000 : ℝ)*(base33) + (394814395107/500000000000 : ℝ)*(base39) + (17159/250000000000 : ℝ)*(base43) + (173279166779/500000000000 : ℝ)*(base49) + (167507/1000000000000 : ℝ)*(base54) + (517501903599/1000000000000 : ℝ)*(base59) + (2169749976047/1000000000000 : ℝ)*(major_s0_0) + (542437482841/250000000000 : ℝ)*(major_s0_1) + (2169749832493/1000000000000 : ℝ)*(major_s0_2) + (3299570861437/1000000000000 : ℝ)*(sp_s0_0) + (1649785407441/500000000000 : ℝ)*(sp_s0_1) + (3299570738859/1000000000000 : ℝ)*(sp_s0_2) + (999999832493/1000000000000 : ℝ)*(sp_s0_6) + (659914199791/200000000000 : ℝ)*(f.sum) + (2070044166864783/10000000000000000000000000000 : ℝ)*base63 + (40460524519481/200000000000000000000000000 : ℝ)*base65 + (480302474796629/2500000000000000000000000000 : ℝ)*base67 + (7021873420064183/10000000000000000000000000000 : ℝ)*base69 + (570445426443393/10000000000000000000000000000 : ℝ)*base70 + (75482359216301/200000000000000000000000000 : ℝ)*base72 + (24496384584003/50000000000000000000000000 : ℝ)*base75 + (2189233143582557/10000000000000000000000000000 : ℝ)*base77 + (2227803625814267/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c328071_s0_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1735451063/5000000000 : ℝ)*x 0 + (2491112881/5000000000 : ℝ)*x 1 + (179592957/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1735451063/5000000000 : ℝ)^93 ≤ (13928998020763/50000000000000 : ℝ)^77 := by
    have hnat : (1735451063 : ℕ)^93*50000000000000^77 ≤ 13928998020763^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735451063 5000000000 13928998020763 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491112881/5000000000 : ℝ)^93 ≤ (43107252554937/100000000000000 : ℝ)^77 := by
    have hnat : (2491112881 : ℕ)^93*100000000000000^77 ≤ 43107252554937^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491112881 5000000000 43107252554937 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179592957/500000000 : ℝ)^93 ≤ (14517375695823/50000000000000 : ℝ)^77 := by
    have hnat : (179592957 : ℕ)^93*50000000000000^77 ≤ 14517375695823^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179592957 500000000 14517375695823 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1735451063/5000000000 : ℝ), (2491112881/5000000000 : ℝ), (179592957/500000000 : ℝ)] ![(13928998020763/50000000000000 : ℝ), (43107252554937/100000000000000 : ℝ), (14517375695823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1735451063/5000000000 : ℝ)|^93 ≤ (13928998020763/50000000000000 : ℝ)^77
        have hw : |(1735451063/5000000000 : ℝ)|=(1735451063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2491112881/5000000000 : ℝ)|^93 ≤ (43107252554937/100000000000000 : ℝ)^77
        have hw : |(2491112881/5000000000 : ℝ)|=(2491112881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179592957/500000000 : ℝ)|^93 ≤ (14517375695823/50000000000000 : ℝ)^77
        have hw : |(179592957/500000000 : ℝ)|=(179592957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6134740211/10000000000 : ℝ)*x 0 + (-701504617/2000000000 : ℝ)*x 1 + (-1117024293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6134740211/10000000000 : ℝ)^93 ≤ (11084902331929/20000000000000 : ℝ)^77 := by
    have hnat : (6134740211 : ℕ)^93*20000000000000^77 ≤ 11084902331929^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134740211 10000000000 11084902331929 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701504617/2000000000 : ℝ)^93 ≤ (5642677000223/20000000000000 : ℝ)^77 := by
    have hnat : (701504617 : ℕ)^93*20000000000000^77 ≤ 5642677000223^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701504617 2000000000 5642677000223 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117024293/5000000000 : ℝ)^93 ≤ (16362103333171/100000000000000 : ℝ)^77 := by
    have hnat : (1117024293 : ℕ)^93*100000000000000^77 ≤ 16362103333171^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117024293 5000000000 16362103333171 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6134740211/10000000000 : ℝ), (-701504617/2000000000 : ℝ), (-1117024293/5000000000 : ℝ)] ![(11084902331929/20000000000000 : ℝ), (5642677000223/20000000000000 : ℝ), (16362103333171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6134740211/10000000000 : ℝ)|^93 ≤ (11084902331929/20000000000000 : ℝ)^77
        have hw : |(6134740211/10000000000 : ℝ)|=(6134740211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-701504617/2000000000 : ℝ)|^93 ≤ (5642677000223/20000000000000 : ℝ)^77
        have hw : |(-701504617/2000000000 : ℝ)|=(701504617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117024293/5000000000 : ℝ)|^93 ≤ (16362103333171/100000000000000 : ℝ)^77
        have hw : |(-1117024293/5000000000 : ℝ)|=(1117024293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-733718429/2000000000 : ℝ)*x 0 + (-4460457989/10000000000 : ℝ)*x 1 + (98579233/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733718429/2000000000 : ℝ)^93 ≤ (14892781288593/50000000000000 : ℝ)^77 := by
    have hnat : (733718429 : ℕ)^93*50000000000000^77 ≤ 14892781288593^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733718429 2000000000 14892781288593 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4460457989/10000000000 : ℝ)^93 ≤ (18857896166837/50000000000000 : ℝ)^77 := by
    have hnat : (4460457989 : ℕ)^93*50000000000000^77 ≤ 18857896166837^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460457989 10000000000 18857896166837 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98579233/250000000 : ℝ)^93 ≤ (3249864507881/10000000000000 : ℝ)^77 := by
    have hnat : (98579233 : ℕ)^93*10000000000000^77 ≤ 3249864507881^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98579233 250000000 3249864507881 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-733718429/2000000000 : ℝ), (-4460457989/10000000000 : ℝ), (98579233/250000000 : ℝ)] ![(14892781288593/50000000000000 : ℝ), (18857896166837/50000000000000 : ℝ), (3249864507881/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-733718429/2000000000 : ℝ)|^93 ≤ (14892781288593/50000000000000 : ℝ)^77
        have hw : |(-733718429/2000000000 : ℝ)|=(733718429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4460457989/10000000000 : ℝ)|^93 ≤ (18857896166837/50000000000000 : ℝ)^77
        have hw : |(-4460457989/10000000000 : ℝ)|=(4460457989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98579233/250000000 : ℝ)|^93 ≤ (3249864507881/10000000000000 : ℝ)^77
        have hw : |(98579233/250000000 : ℝ)|=(98579233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3388582191/10000000000 : ℝ)*x 0 + (993866759/2000000000 : ℝ)*x 1 + (3686928171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3388582191/10000000000 : ℝ)^93 ≤ (3382746432001/12500000000000 : ℝ)^77 := by
    have hnat : (3388582191 : ℕ)^93*12500000000000^77 ≤ 3382746432001^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3388582191 10000000000 3382746432001 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993866759/2000000000 : ℝ)^93 ≤ (1718902674073/4000000000000 : ℝ)^77 := by
    have hnat : (993866759 : ℕ)^93*4000000000000^77 ≤ 1718902674073^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993866759 2000000000 1718902674073 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3686928171/10000000000 : ℝ)^93 ≤ (29965461673513/100000000000000 : ℝ)^77 := by
    have hnat : (3686928171 : ℕ)^93*100000000000000^77 ≤ 29965461673513^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686928171 10000000000 29965461673513 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3388582191/10000000000 : ℝ), (993866759/2000000000 : ℝ), (3686928171/10000000000 : ℝ)] ![(3382746432001/12500000000000 : ℝ), (1718902674073/4000000000000 : ℝ), (29965461673513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3388582191/10000000000 : ℝ)|^93 ≤ (3382746432001/12500000000000 : ℝ)^77
        have hw : |(3388582191/10000000000 : ℝ)|=(3388582191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993866759/2000000000 : ℝ)|^93 ≤ (1718902674073/4000000000000 : ℝ)^77
        have hw : |(993866759/2000000000 : ℝ)|=(993866759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3686928171/10000000000 : ℝ)|^93 ≤ (29965461673513/100000000000000 : ℝ)^77
        have hw : |(3686928171/10000000000 : ℝ)|=(3686928171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1192428331/2000000000 : ℝ)*x 0 + (-1808381413/5000000000 : ℝ)*x 1 + (-36337291/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1192428331/2000000000 : ℝ)^93 ≤ (26773345387873/50000000000000 : ℝ)^77 := by
    have hnat : (1192428331 : ℕ)^93*50000000000000^77 ≤ 26773345387873^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192428331 2000000000 26773345387873 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1808381413/5000000000 : ℝ)^93 ≤ (1463903262091/5000000000000 : ℝ)^77 := by
    have hnat : (1808381413 : ℕ)^93*5000000000000^77 ≤ 1463903262091^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808381413 5000000000 1463903262091 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36337291/156250000 : ℝ)^93 ≤ (3435048793817/20000000000000 : ℝ)^77 := by
    have hnat : (36337291 : ℕ)^93*20000000000000^77 ≤ 3435048793817^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36337291 156250000 3435048793817 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1192428331/2000000000 : ℝ), (-1808381413/5000000000 : ℝ), (-36337291/156250000 : ℝ)] ![(26773345387873/50000000000000 : ℝ), (1463903262091/5000000000000 : ℝ), (3435048793817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1192428331/2000000000 : ℝ)|^93 ≤ (26773345387873/50000000000000 : ℝ)^77
        have hw : |(1192428331/2000000000 : ℝ)|=(1192428331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1808381413/5000000000 : ℝ)|^93 ≤ (1463903262091/5000000000000 : ℝ)^77
        have hw : |(-1808381413/5000000000 : ℝ)|=(1808381413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36337291/156250000 : ℝ)|^93 ≤ (3435048793817/20000000000000 : ℝ)^77
        have hw : |(-36337291/156250000 : ℝ)|=(36337291/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-49501/5000000000 : ℝ)*x 0 + (-103938027/625000000 : ℝ)*x 1 + (4520879751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49501/5000000000 : ℝ)^93 ≤ (45159361/50000000000000 : ℝ)^77 := by
    have hnat : (49501 : ℕ)^93*50000000000000^77 ≤ 45159361^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49501 5000000000 45159361 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103938027/625000000 : ℝ)^93 ≤ (11455192432127/100000000000000 : ℝ)^77 := by
    have hnat : (103938027 : ℕ)^93*100000000000000^77 ≤ 11455192432127^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103938027 625000000 11455192432127 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520879751/5000000000 : ℝ)^93 ≤ (88544717237829/100000000000000 : ℝ)^77 := by
    have hnat : (4520879751 : ℕ)^93*100000000000000^77 ≤ 88544717237829^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520879751 5000000000 88544717237829 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49501/5000000000 : ℝ), (-103938027/625000000 : ℝ), (4520879751/5000000000 : ℝ)] ![(45159361/50000000000000 : ℝ), (11455192432127/100000000000000 : ℝ), (88544717237829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49501/5000000000 : ℝ)|^93 ≤ (45159361/50000000000000 : ℝ)^77
        have hw : |(-49501/5000000000 : ℝ)|=(49501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103938027/625000000 : ℝ)|^93 ≤ (11455192432127/100000000000000 : ℝ)^77
        have hw : |(-103938027/625000000 : ℝ)|=(103938027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520879751/5000000000 : ℝ)|^93 ≤ (88544717237829/100000000000000 : ℝ)^77
        have hw : |(4520879751/5000000000 : ℝ)|=(4520879751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-784031997/2500000000 : ℝ)*x 0 + (-3272903399/10000000000 : ℝ)*x 1 + (1394396383/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784031997/2500000000 : ℝ)^93 ≤ (6161526750119/25000000000000 : ℝ)^77 := by
    have hnat : (784031997 : ℕ)^93*25000000000000^77 ≤ 6161526750119^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784031997 2500000000 6161526750119 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3272903399/10000000000 : ℝ)^93 ≤ (6487540646051/25000000000000 : ℝ)^77 := by
    have hnat : (3272903399 : ℕ)^93*25000000000000^77 ≤ 6487540646051^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3272903399 10000000000 6487540646051 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394396383/2500000000 : ℝ)^93 ≤ (9880746080089/20000000000000 : ℝ)^77 := by
    have hnat : (1394396383 : ℕ)^93*20000000000000^77 ≤ 9880746080089^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394396383 2500000000 9880746080089 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784031997/2500000000 : ℝ), (-3272903399/10000000000 : ℝ), (1394396383/2500000000 : ℝ)] ![(6161526750119/25000000000000 : ℝ), (6487540646051/25000000000000 : ℝ), (9880746080089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784031997/2500000000 : ℝ)|^93 ≤ (6161526750119/25000000000000 : ℝ)^77
        have hw : |(-784031997/2500000000 : ℝ)|=(784031997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3272903399/10000000000 : ℝ)|^93 ≤ (6487540646051/25000000000000 : ℝ)^77
        have hw : |(-3272903399/10000000000 : ℝ)|=(3272903399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394396383/2500000000 : ℝ)|^93 ≤ (9880746080089/20000000000000 : ℝ)^77
        have hw : |(1394396383/2500000000 : ℝ)|=(1394396383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4396299469/10000000000 : ℝ)*x 0 + (2393191127/5000000000 : ℝ)*x 1 + (710153377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4396299469/10000000000 : ℝ)^93 ≤ (37061550437229/100000000000000 : ℝ)^77 := by
    have hnat : (4396299469 : ℕ)^93*100000000000000^77 ≤ 37061550437229^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396299469 10000000000 37061550437229 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2393191127/5000000000 : ℝ)^93 ≤ (328552967101/800000000000 : ℝ)^77 := by
    have hnat : (2393191127 : ℕ)^93*800000000000^77 ≤ 328552967101^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393191127 5000000000 328552967101 800000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710153377/2500000000 : ℝ)^93 ≤ (2733666082647/12500000000000 : ℝ)^77 := by
    have hnat : (710153377 : ℕ)^93*12500000000000^77 ≤ 2733666082647^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710153377 2500000000 2733666082647 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4396299469/10000000000 : ℝ), (2393191127/5000000000 : ℝ), (710153377/2500000000 : ℝ)] ![(37061550437229/100000000000000 : ℝ), (328552967101/800000000000 : ℝ), (2733666082647/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4396299469/10000000000 : ℝ)|^93 ≤ (37061550437229/100000000000000 : ℝ)^77
        have hw : |(4396299469/10000000000 : ℝ)|=(4396299469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2393191127/5000000000 : ℝ)|^93 ≤ (328552967101/800000000000 : ℝ)^77
        have hw : |(2393191127/5000000000 : ℝ)|=(2393191127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(710153377/2500000000 : ℝ)|^93 ≤ (2733666082647/12500000000000 : ℝ)^77
        have hw : |(710153377/2500000000 : ℝ)|=(710153377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3475233081/5000000000 : ℝ)*x 0 + (-3147768489/10000000000 : ℝ)*x 1 + (-791862039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3475233081/5000000000 : ℝ)^93 ≤ (1611111762619/2500000000000 : ℝ)^77 := by
    have hnat : (3475233081 : ℕ)^93*2500000000000^77 ≤ 1611111762619^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3475233081 5000000000 1611111762619 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3147768489/10000000000 : ℝ)^93 ≤ (12378319207829/50000000000000 : ℝ)^77 := by
    have hnat : (3147768489 : ℕ)^93*50000000000000^77 ≤ 12378319207829^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3147768489 10000000000 12378319207829 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791862039/5000000000 : ℝ)^93 ≤ (2159778211733/20000000000000 : ℝ)^77 := by
    have hnat : (791862039 : ℕ)^93*20000000000000^77 ≤ 2159778211733^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791862039 5000000000 2159778211733 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3475233081/5000000000 : ℝ), (-3147768489/10000000000 : ℝ), (-791862039/5000000000 : ℝ)] ![(1611111762619/2500000000000 : ℝ), (12378319207829/50000000000000 : ℝ), (2159778211733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3475233081/5000000000 : ℝ)|^93 ≤ (1611111762619/2500000000000 : ℝ)^77
        have hw : |(3475233081/5000000000 : ℝ)|=(3475233081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3147768489/10000000000 : ℝ)|^93 ≤ (12378319207829/50000000000000 : ℝ)^77
        have hw : |(-3147768489/10000000000 : ℝ)|=(3147768489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-791862039/5000000000 : ℝ)|^93 ≤ (2159778211733/20000000000000 : ℝ)^77
        have hw : |(-791862039/5000000000 : ℝ)|=(791862039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-387/10000000000 : ℝ)*x 0 + (-910116521/5000000000 : ℝ)*x 1 + (8929972069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387/10000000000 : ℝ)^93 ≤ (111557/100000000000000 : ℝ)^77 := by
    have hnat : (387 : ℕ)^93*100000000000000^77 ≤ 111557^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387 10000000000 111557 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910116521/5000000000 : ℝ)^93 ≤ (6387885934683/50000000000000 : ℝ)^77 := by
    have hnat : (910116521 : ℕ)^93*50000000000000^77 ≤ 6387885934683^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910116521 5000000000 6387885934683 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8929972069/10000000000 : ℝ)^93 ≤ (87224228016221/100000000000000 : ℝ)^77 := by
    have hnat : (8929972069 : ℕ)^93*100000000000000^77 ≤ 87224228016221^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8929972069 10000000000 87224228016221 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387/10000000000 : ℝ), (-910116521/5000000000 : ℝ), (8929972069/10000000000 : ℝ)] ![(111557/100000000000000 : ℝ), (6387885934683/50000000000000 : ℝ), (87224228016221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387/10000000000 : ℝ)|^93 ≤ (111557/100000000000000 : ℝ)^77
        have hw : |(-387/10000000000 : ℝ)|=(387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910116521/5000000000 : ℝ)|^93 ≤ (6387885934683/50000000000000 : ℝ)^77
        have hw : |(-910116521/5000000000 : ℝ)|=(910116521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8929972069/10000000000 : ℝ)|^93 ≤ (87224228016221/100000000000000 : ℝ)^77
        have hw : |(8929972069/10000000000 : ℝ)|=(8929972069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-79102691/250000000 : ℝ)*x 0 + (-414214547/1000000000 : ℝ)*x 1 + (4740925551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79102691/250000000 : ℝ)^93 ≤ (24911928751501/100000000000000 : ℝ)^77 := by
    have hnat : (79102691 : ℕ)^93*100000000000000^77 ≤ 24911928751501^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79102691 250000000 24911928751501 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414214547/1000000000 : ℝ)^93 ≤ (34489568171427/100000000000000 : ℝ)^77 := by
    have hnat : (414214547 : ℕ)^93*100000000000000^77 ≤ 34489568171427^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414214547 1000000000 34489568171427 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4740925551/10000000000 : ℝ)^93 ≤ (20299251533503/50000000000000 : ℝ)^77 := by
    have hnat : (4740925551 : ℕ)^93*50000000000000^77 ≤ 20299251533503^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4740925551 10000000000 20299251533503 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79102691/250000000 : ℝ), (-414214547/1000000000 : ℝ), (4740925551/10000000000 : ℝ)] ![(24911928751501/100000000000000 : ℝ), (34489568171427/100000000000000 : ℝ), (20299251533503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79102691/250000000 : ℝ)|^93 ≤ (24911928751501/100000000000000 : ℝ)^77
        have hw : |(-79102691/250000000 : ℝ)|=(79102691/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414214547/1000000000 : ℝ)|^93 ≤ (34489568171427/100000000000000 : ℝ)^77
        have hw : |(-414214547/1000000000 : ℝ)|=(414214547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4740925551/10000000000 : ℝ)|^93 ≤ (20299251533503/50000000000000 : ℝ)^77
        have hw : |(4740925551/10000000000 : ℝ)|=(4740925551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2959187249/10000000000 : ℝ)*x 0 + (524736257/1000000000 : ℝ)*x 1 + (3805202529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2959187249/10000000000 : ℝ)^93 ≤ (22976623199039/100000000000000 : ℝ)^77 := by
    have hnat : (2959187249 : ℕ)^93*100000000000000^77 ≤ 22976623199039^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959187249 10000000000 22976623199039 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524736257/1000000000 : ℝ)^93 ≤ (45893059404473/100000000000000 : ℝ)^77 := by
    have hnat : (524736257 : ℕ)^93*100000000000000^77 ≤ 45893059404473^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524736257 1000000000 45893059404473 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3805202529/10000000000 : ℝ)^93 ≤ (31130317385159/100000000000000 : ℝ)^77 := by
    have hnat : (3805202529 : ℕ)^93*100000000000000^77 ≤ 31130317385159^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805202529 10000000000 31130317385159 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2959187249/10000000000 : ℝ), (524736257/1000000000 : ℝ), (3805202529/10000000000 : ℝ)] ![(22976623199039/100000000000000 : ℝ), (45893059404473/100000000000000 : ℝ), (31130317385159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2959187249/10000000000 : ℝ)|^93 ≤ (22976623199039/100000000000000 : ℝ)^77
        have hw : |(2959187249/10000000000 : ℝ)|=(2959187249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524736257/1000000000 : ℝ)|^93 ≤ (45893059404473/100000000000000 : ℝ)^77
        have hw : |(524736257/1000000000 : ℝ)|=(524736257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3805202529/10000000000 : ℝ)|^93 ≤ (31130317385159/100000000000000 : ℝ)^77
        have hw : |(3805202529/10000000000 : ℝ)|=(3805202529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s0_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6837521341/10000000000 : ℝ)*x 0 + (-2965574299/10000000000 : ℝ)*x 1 + (-969056497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6837521341/10000000000 : ℝ)^93 ≤ (15795447660803/25000000000000 : ℝ)^77 := by
    have hnat : (6837521341 : ℕ)^93*25000000000000^77 ≤ 15795447660803^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6837521341 10000000000 15795447660803 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2965574299/10000000000 : ℝ)^93 ≤ (23036533791937/100000000000000 : ℝ)^77 := by
    have hnat : (2965574299 : ℕ)^93*100000000000000^77 ≤ 23036533791937^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965574299 10000000000 23036533791937 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969056497/5000000000 : ℝ)^93 ≤ (13781675558329/100000000000000 : ℝ)^77 := by
    have hnat : (969056497 : ℕ)^93*100000000000000^77 ≤ 13781675558329^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969056497 5000000000 13781675558329 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6837521341/10000000000 : ℝ), (-2965574299/10000000000 : ℝ), (-969056497/5000000000 : ℝ)] ![(15795447660803/25000000000000 : ℝ), (23036533791937/100000000000000 : ℝ), (13781675558329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6837521341/10000000000 : ℝ)|^93 ≤ (15795447660803/25000000000000 : ℝ)^77
        have hw : |(6837521341/10000000000 : ℝ)|=(6837521341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2965574299/10000000000 : ℝ)|^93 ≤ (23036533791937/100000000000000 : ℝ)^77
        have hw : |(-2965574299/10000000000 : ℝ)|=(2965574299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969056497/5000000000 : ℝ)|^93 ≤ (13781675558329/100000000000000 : ℝ)^77
        have hw : |(-969056497/5000000000 : ℝ)|=(969056497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3342085881/10000000000 : ℝ)*x 0 + (-924449241/2500000000 : ℝ)*x 1 + (31262327/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3342085881/10000000000 : ℝ)^93 ≤ (26614123822417/100000000000000 : ℝ)^77 := by
    have hnat : (3342085881 : ℕ)^93*100000000000000^77 ≤ 26614123822417^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342085881 10000000000 26614123822417 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924449241/2500000000 : ℝ)^93 ≤ (15036092914699/50000000000000 : ℝ)^77 := by
    have hnat : (924449241 : ℕ)^93*50000000000000^77 ≤ 15036092914699^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924449241 2500000000 15036092914699 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31262327/62500000 : ℝ)^93 ≤ (43313690335131/100000000000000 : ℝ)^77 := by
    have hnat : (31262327 : ℕ)^93*100000000000000^77 ≤ 43313690335131^77*62500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31262327 62500000 43313690335131 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3342085881/10000000000 : ℝ), (-924449241/2500000000 : ℝ), (31262327/62500000 : ℝ)] ![(26614123822417/100000000000000 : ℝ), (15036092914699/50000000000000 : ℝ), (43313690335131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3342085881/10000000000 : ℝ)|^93 ≤ (26614123822417/100000000000000 : ℝ)^77
        have hw : |(-3342085881/10000000000 : ℝ)|=(3342085881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-924449241/2500000000 : ℝ)|^93 ≤ (15036092914699/50000000000000 : ℝ)^77
        have hw : |(-924449241/2500000000 : ℝ)|=(924449241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31262327/62500000 : ℝ)|^93 ≤ (43313690335131/100000000000000 : ℝ)^77
        have hw : |(31262327/62500000 : ℝ)|=(31262327/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4072905671/10000000000 : ℝ)*x 0 + (1129342537/2500000000 : ℝ)*x 1 + (3476034723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4072905671/10000000000 : ℝ)^93 ≤ (16897230181007/50000000000000 : ℝ)^77 := by
    have hnat : (4072905671 : ℕ)^93*50000000000000^77 ≤ 16897230181007^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072905671 10000000000 16897230181007 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129342537/2500000000 : ℝ)^93 ≤ (38297780932299/100000000000000 : ℝ)^77 := by
    have hnat : (1129342537 : ℕ)^93*100000000000000^77 ≤ 38297780932299^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129342537 2500000000 38297780932299 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3476034723/10000000000 : ℝ)^93 ≤ (5581551740291/20000000000000 : ℝ)^77 := by
    have hnat : (3476034723 : ℕ)^93*20000000000000^77 ≤ 5581551740291^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3476034723 10000000000 5581551740291 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4072905671/10000000000 : ℝ), (1129342537/2500000000 : ℝ), (3476034723/10000000000 : ℝ)] ![(16897230181007/50000000000000 : ℝ), (38297780932299/100000000000000 : ℝ), (5581551740291/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4072905671/10000000000 : ℝ)|^93 ≤ (16897230181007/50000000000000 : ℝ)^77
        have hw : |(4072905671/10000000000 : ℝ)|=(4072905671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129342537/2500000000 : ℝ)|^93 ≤ (38297780932299/100000000000000 : ℝ)^77
        have hw : |(1129342537/2500000000 : ℝ)|=(1129342537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3476034723/10000000000 : ℝ)|^93 ≤ (5581551740291/20000000000000 : ℝ)^77
        have hw : |(3476034723/10000000000 : ℝ)|=(3476034723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2453837039/5000000000 : ℝ)*x 0 + (-161882973/400000000 : ℝ)*x 1 + (-96317711/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2453837039/5000000000 : ℝ)^93 ≤ (21164699151793/50000000000000 : ℝ)^77 := by
    have hnat : (2453837039 : ℕ)^93*50000000000000^77 ≤ 21164699151793^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453837039 5000000000 21164699151793 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161882973/400000000 : ℝ)^93 ≤ (33535762000939/100000000000000 : ℝ)^77 := by
    have hnat : (161882973 : ℕ)^93*100000000000000^77 ≤ 33535762000939^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161882973 400000000 33535762000939 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96317711/312500000 : ℝ)^93 ≤ (24134839682427/100000000000000 : ℝ)^77 := by
    have hnat : (96317711 : ℕ)^93*100000000000000^77 ≤ 24134839682427^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96317711 312500000 24134839682427 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2453837039/5000000000 : ℝ), (-161882973/400000000 : ℝ), (-96317711/312500000 : ℝ)] ![(21164699151793/50000000000000 : ℝ), (33535762000939/100000000000000 : ℝ), (24134839682427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2453837039/5000000000 : ℝ)|^93 ≤ (21164699151793/50000000000000 : ℝ)^77
        have hw : |(2453837039/5000000000 : ℝ)|=(2453837039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161882973/400000000 : ℝ)|^93 ≤ (33535762000939/100000000000000 : ℝ)^77
        have hw : |(-161882973/400000000 : ℝ)|=(161882973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96317711/312500000 : ℝ)|^93 ≤ (24134839682427/100000000000000 : ℝ)^77
        have hw : |(-96317711/312500000 : ℝ)|=(96317711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328071_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2977434233/10000000000 : ℝ)*x 0 + (-774820027/2500000000 : ℝ)*x 1 + (117412121/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2977434233/10000000000 : ℝ)^93 ≤ (5786962797209/25000000000000 : ℝ)^77 := by
    have hnat : (2977434233 : ℕ)^93*25000000000000^77 ≤ 5786962797209^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977434233 10000000000 5786962797209 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774820027/2500000000 : ℝ)^93 ≤ (1214839201393/5000000000000 : ℝ)^77 := by
    have hnat : (774820027 : ℕ)^93*5000000000000^77 ≤ 1214839201393^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774820027 2500000000 1214839201393 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117412121/200000000 : ℝ)^93 ≤ (13138841193007/25000000000000 : ℝ)^77 := by
    have hnat : (117412121 : ℕ)^93*25000000000000^77 ≤ 13138841193007^77*200000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117412121 200000000 13138841193007 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2977434233/10000000000 : ℝ), (-774820027/2500000000 : ℝ), (117412121/200000000 : ℝ)] ![(5786962797209/25000000000000 : ℝ), (1214839201393/5000000000000 : ℝ), (13138841193007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2977434233/10000000000 : ℝ)|^93 ≤ (5786962797209/25000000000000 : ℝ)^77
        have hw : |(2977434233/10000000000 : ℝ)|=(2977434233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-774820027/2500000000 : ℝ)|^93 ≤ (1214839201393/5000000000000 : ℝ)^77
        have hw : |(-774820027/2500000000 : ℝ)|=(774820027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117412121/200000000 : ℝ)|^93 ≤ (13138841193007/25000000000000 : ℝ)^77
        have hw : |(117412121/200000000 : ℝ)|=(117412121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328071 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (80697/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1296095383713331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1296095383713331/10000000000000000 : ℝ)) (beta := (16694097234717/200000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1296095383713331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(16694097234717/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((1735451063/5000000000 : ℝ)*X 1 0+(2491112881/5000000000 : ℝ)*X 1 1+(179592957/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6134740211/10000000000 : ℝ)*X 2 0+(-701504617/2000000000 : ℝ)*X 2 1+(-1117024293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-733718429/2000000000 : ℝ)*X 0 0+(-4460457989/10000000000 : ℝ)*X 0 1+(98579233/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3388582191/10000000000 : ℝ)*X 1 0+(993866759/2000000000 : ℝ)*X 1 1+(3686928171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1192428331/2000000000 : ℝ)*X 2 0+(-1808381413/5000000000 : ℝ)*X 2 1+(-36337291/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-49501/5000000000 : ℝ)*X 0 0+(-103938027/625000000 : ℝ)*X 0 1+(4520879751/5000000000 : ℝ)*X 0 2+(-49501/5000000000 : ℝ)*X 1 0+(-103938027/625000000 : ℝ)*X 1 1+(4520879751/5000000000 : ℝ)*X 1 2+(-49501/5000000000 : ℝ)*X 2 0+(-103938027/625000000 : ℝ)*X 2 1+(4520879751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-784031997/2500000000 : ℝ)*X 0 0+(-3272903399/10000000000 : ℝ)*X 0 1+(1394396383/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4396299469/10000000000 : ℝ)*X 1 0+(2393191127/5000000000 : ℝ)*X 1 1+(710153377/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3475233081/5000000000 : ℝ)*X 2 0+(-3147768489/10000000000 : ℝ)*X 2 1+(-791862039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-387/10000000000 : ℝ)*X 0 0+(-910116521/5000000000 : ℝ)*X 0 1+(8929972069/10000000000 : ℝ)*X 0 2+(-387/10000000000 : ℝ)*X 1 0+(-910116521/5000000000 : ℝ)*X 1 1+(8929972069/10000000000 : ℝ)*X 1 2+(-387/10000000000 : ℝ)*X 2 0+(-910116521/5000000000 : ℝ)*X 2 1+(8929972069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-79102691/250000000 : ℝ)*X 0 0+(-414214547/1000000000 : ℝ)*X 0 1+(4740925551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2959187249/10000000000 : ℝ)*X 1 0+(524736257/1000000000 : ℝ)*X 1 1+(3805202529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6837521341/10000000000 : ℝ)*X 2 0+(-2965574299/10000000000 : ℝ)*X 2 1+(-969056497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21749/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21749/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9530998579561918566579/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46683088343/500000000000 : ℝ)*(base1) + (692115976229/1000000000000 : ℝ)*(base7) + (140043/50000000000 : ℝ)*(base40) + (3805101/500000000000 : ℝ)*(base54) + (1328484122071/1000000000000 : ℝ)*(base60) + (4069882477507/1000000000000 : ℝ)*(major_s0_0) + (4069882477507/1000000000000 : ℝ)*(major_s0_1) + (813974973461/200000000000 : ℝ)*(major_s0_2) + (19924723/100000000000 : ℝ)*(sp_s0_2) + (239401842373/40000000000 : ℝ)*(sp_s0_7) + (5891542432617/1000000000000 : ℝ)*(sp_s0_8) + (5891473025207/1000000000000 : ℝ)*(sp_s0_9) + (1237240083611/500000000000 : ℝ)*(sp_s0_13) + (68725011/500000000000 : ℝ)*(sp_s0_22) + (1875737977881/1000000000000 : ℝ)*(f.failure) + (5891679882639/1000000000000 : ℝ)*(f.sum) + (971834036786219/2000000000000000000000000000 : ℝ)*base63 + (357290470463/40000000000000000000000000 : ℝ)*base65 + (4709964700454183/10000000000000000000000000000 : ℝ)*base66 + (267671466891409/2000000000000000000000000000 : ℝ)*base69 + (7334355118838433/10000000000000000000000000000 : ℝ)*base70 + (4808399769481/200000000000000000000000000 : ℝ)*base72 + (49096665430519/200000000000000000000000000 : ℝ)*base74 + (1160736820454183/10000000000000000000000000000 : ℝ)*base76 + (1828974848071767/10000000000000000000000000000 : ℝ)*base79 + (1199/4000000000000000 : ℝ)*base87 + (1199/4000000000000000 : ℝ)*base89 + (1199/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-7011/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7011/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9158607870056378722569/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100227058511/100000000000 : ℝ)*(base1) + (285595852947/200000000000 : ℝ)*(base7) + (131182598881/200000000000 : ℝ)*(base40) + (506448192949/500000000000 : ℝ)*(base60) + (871173862867/250000000000 : ℝ)*(major_s0_0) + (871173862867/250000000000 : ℝ)*(major_s0_1) + (871173862867/250000000000 : ℝ)*(major_s0_2) + (3873511/62500000000 : ℝ)*(sp_s0_1) + (165561063/250000000000 : ℝ)*(sp_s0_13) + (5597396853017/1000000000000 : ℝ)*(sp_s0_14) + (4595064291731/1000000000000 : ℝ)*(sp_s0_15) + (4595068682767/1000000000000 : ℝ)*(sp_s0_16) + (507770475241/250000000000 : ℝ)*(sp_s0_20) + (2879257/50000000000 : ℝ)*(sp_s0_23) + (200754433199/125000000000 : ℝ)*(f.failure) + (4595126267907/1000000000000 : ℝ)*(f.sum) + (430486969461927/2500000000000000000000000000 : ℝ)*base62 + (321781121361/50000000000000000000000000 : ℝ)*base65 + (1614214067779977/2500000000000000000000000000 : ℝ)*base67 + (302923694529977/2500000000000000000000000000 : ℝ)*base68 + (575881747598027/2500000000000000000000000000 : ℝ)*base71 + (36365629513639/50000000000000000000000000 : ℝ)*base73 + (7191363336361/50000000000000000000000000 : ℝ)*base75 + (407776347470023/2500000000000000000000000000 : ℝ)*base76 + (1371453302961927/2500000000000000000000000000 : ℝ)*base79 + (121/500000000000000 : ℝ)*base87 + (121/500000000000000 : ℝ)*base89 + (121/500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4343/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4343/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (56245806928086462243/2500000000000000000000000 : ℝ) := by norm_num
    linear_combination (358627318253/125000000000 : ℝ)*(base1) + (51050079907/40000000000 : ℝ)*(base7) + (65367846221/40000000000 : ℝ)*(base40) + (637158197537/1000000000000 : ℝ)*(base60) + (86397630457/25000000000 : ℝ)*(major_s0_0) + (86397630457/25000000000 : ℝ)*(major_s0_1) + (86397630457/25000000000 : ℝ)*(major_s0_2) + (2731423/40000000000 : ℝ)*(sp_s0_1) + (2248221/50000000000 : ℝ)*(sp_s0_2) + (17089743/1000000000000 : ℝ)*(sp_s0_7) + (47618597/200000000000 : ℝ)*(sp_s0_16) + (375071989767/50000000000 : ℝ)*(sp_s0_21) + (1158092513371/250000000000 : ℝ)*(sp_s0_22) + (2316077640827/500000000000 : ℝ)*(sp_s0_23) + (1592766548349/1000000000000 : ℝ)*(f.failure) + (4632438339059/1000000000000 : ℝ)*(f.sum) + (53270647069283/250000000000000000000000000 : ℝ)*base63 + (303748662169/5000000000000000000000000 : ℝ)*base64 + (59537264977733/250000000000000000000000000 : ℝ)*base66 + (6574611672267/250000000000000000000000000 : ℝ)*base68 + (121701612011183/250000000000000000000000000 : ℝ)*base70 + (633026292331/5000000000000000000000000 : ℝ)*base72 + (1395529077669/5000000000000000000000000 : ℝ)*base74 + (12918060297267/250000000000000000000000000 : ℝ)*base77 + (38633886955717/250000000000000000000000000 : ℝ)*base79 + (971/4000000000000000 : ℝ)*base87 + (971/4000000000000000 : ℝ)*base89 + (971/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (21749/100000 : ℝ) ^ (91/16 : ℝ) ≤ (1704849240587237/10000000000000000000 : ℝ) := by
    have hpowers : (21749/100000 : ℝ)^91 ≤ (1704849240587237/10000000000000000000 : ℝ)^16 := by
      have hnat : (21749 : ℕ)^91*10000000000000000000^16 ≤ 1704849240587237^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21749 100000 1704849240587237 10000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21749/100000 : ℝ)) (X := (1704849240587237/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10001704849240587237/10000000000000000000 : ℝ) ≤ (2500074933163921/2500000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (10001704849240587237/10000000000000000000 : ℝ)^16 ≤ (2500074933163921/2500000000000000 : ℝ)^91 := by
      have hnat : (10001704849240587237 : ℕ)^16*2500000000000000^91 ≤ 2500074933163921^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001704849240587237 10000000000000000000 2500074933163921 2500000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074933163921/2500000000000000 : ℝ)) (X := (10001704849240587237/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5001704849240587237/5000000000000000000 : ℝ) ≤ (5000299711603101/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (5001704849240587237/5000000000000000000 : ℝ)^16 ≤ (5000299711603101/5000000000000000 : ℝ)^91 := by
      have hnat : (5001704849240587237 : ℕ)^16*5000000000000000^91 ≤ 5000299711603101^91*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001704849240587237 5000000000000000000 5000299711603101 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000299711603101/5000000000000000 : ℝ)) (X := (5001704849240587237/5000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10704737703/77675000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(149845275259/1087450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (21749/100000 : ℝ)) (alpha := (10704737703/77675000000000 : ℝ)) (beta := (149845275259/1087450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21749/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10704737703/77675000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(149845275259/1087450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7011/12500 : ℝ) ^ (91/16 : ℝ) ≤ (3729905802306881433/100000000000000000000 : ℝ) := by
    have hpowers : (7011/12500 : ℝ)^91 ≤ (3729905802306881433/100000000000000000000 : ℝ)^16 := by
      have hnat : (7011 : ℕ)^91*100000000000000000000^16 ≤ 3729905802306881433^16*12500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7011 12500 3729905802306881433 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7011/12500 : ℝ)) (X := (3729905802306881433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (103729905802306881433/100000000000000000000 : ℝ) ≤ (10064595029126213/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (103729905802306881433/100000000000000000000 : ℝ)^16 ≤ (10064595029126213/10000000000000000 : ℝ)^91 := by
      have hnat : (103729905802306881433 : ℕ)^16*10000000000000000^91 ≤ 10064595029126213^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103729905802306881433 100000000000000000000 10064595029126213 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064595029126213/10000000000000000 : ℝ)) (X := (103729905802306881433/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53729905802306881433/50000000000000000000 : ℝ) ≤ (405092130702373/400000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (53729905802306881433/50000000000000000000 : ℝ)^16 ≤ (405092130702373/400000000000000 : ℝ)^91 := by
      have hnat : (53729905802306881433 : ℕ)^16*400000000000000^91 ≤ 405092130702373^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53729905802306881433 50000000000000000000 405092130702373 400000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (405092130702373/400000000000000 : ℝ)) (X := (53729905802306881433/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64595029126213/5608800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(7838529804139/701100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (7011/12500 : ℝ)) (alpha := (64595029126213/5608800000000000 : ℝ)) (beta := (7838529804139/701100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7011/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64595029126213/5608800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(7838529804139/701100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (4343/12500 : ℝ) ^ (91/16 : ℝ) ≤ (122383807325937249/50000000000000000000 : ℝ) := by
    have hpowers : (4343/12500 : ℝ)^91 ≤ (122383807325937249/50000000000000000000 : ℝ)^16 := by
      have hnat : (4343 : ℕ)^91*50000000000000000000^16 ≤ 122383807325937249^16*12500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4343 12500 122383807325937249 50000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4343/12500 : ℝ)) (X := (122383807325937249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50122383807325937249/50000000000000000000 : ℝ) ≤ (1000429927199499/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (50122383807325937249/50000000000000000000 : ℝ)^16 ≤ (1000429927199499/1000000000000000 : ℝ)^91 := by
      have hnat : (50122383807325937249 : ℕ)^16*1000000000000000^91 ≤ 1000429927199499^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50122383807325937249 50000000000000000000 1000429927199499 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000429927199499/1000000000000000 : ℝ)) (X := (50122383807325937249/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25122383807325937249/25000000000000000000 : ℝ) ≤ (1000858990086621/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (25122383807325937249/25000000000000000000 : ℝ)^16 ≤ (1000858990086621/1000000000000000 : ℝ)^91 := by
      have hnat : (25122383807325937249 : ℕ)^16*1000000000000000^91 ≤ 1000858990086621^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25122383807325937249 25000000000000000000 1000858990086621 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000858990086621/1000000000000000 : ℝ)) (X := (25122383807325937249/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(429927199499/347440000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(214531443561/173720000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (4343/12500 : ℝ)) (alpha := (429927199499/347440000000000 : ℝ)) (beta := (214531443561/173720000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4343/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(429927199499/347440000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(214531443561/173720000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3342085881/10000000000 : ℝ)*X 0 0+(-924449241/2500000000 : ℝ)*X 0 1+(31262327/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4072905671/10000000000 : ℝ)*X 1 0+(1129342537/2500000000 : ℝ)*X 1 1+(3476034723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2453837039/5000000000 : ℝ)*X 2 0+(-161882973/400000000 : ℝ)*X 2 1+(-96317711/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2977434233/10000000000 : ℝ)*X 0 0+(-774820027/2500000000 : ℝ)*X 0 1+(117412121/200000000 : ℝ)*X 0 2+(2977434233/10000000000 : ℝ)*X 1 0+(-774820027/2500000000 : ℝ)*X 1 1+(117412121/200000000 : ℝ)*X 1 2+(2977434233/10000000000 : ℝ)*X 2 0+(-774820027/2500000000 : ℝ)*X 2 1+(117412121/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-20037/2000 : ℝ) < ((-8679/4000 : ℝ)*P 0+(-8679/4000 : ℝ)*P 1+(-8679/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-20037/2000 : ℝ) < (-1662234150808782220368101896393/169424710000000000000000000000 : ℝ) := by norm_num
    linear_combination (161989382017/500000000000 : ℝ)*(base1) + (266941/500000000000 : ℝ)*(base19) + (520497/1000000000000 : ℝ)*(base21) + (154631/1000000000000 : ℝ)*(base39) + (127279687713/200000000000 : ℝ)*(base40) + (169614726273/500000000000 : ℝ)*(base49) + (82019/500000000000 : ℝ)*(base50) + (79225234397/125000000000 : ℝ)*(base60) + (8679/4000 : ℝ)*(major_s1_0) + (8679/4000 : ℝ)*(major_s1_1) + (8679/4000 : ℝ)*(major_s1_2) + (71886569369/20000000000 : ℝ)*(sp_s1_0) + (1635174585267/500000000000 : ℝ)*(sp_s1_1) + (3270349183919/1000000000000 : ℝ)*(sp_s1_2) + (338010617983/500000000000 : ℝ)*(sp_s1_6) + (102198428263/31250000000 : ℝ)*(f.sum) + (10178799671293037/25373977500000000000000000000 : ℝ)*base62 + (540248043381/2714375000000000000000000 : ℝ)*base64 + (11585485979/233700000000000000000000 : ℝ)*base67 + (1137191100193/5428750000000000000000000 : ℝ)*base69 + (374167407080031/8433563125000000000000000000 : ℝ)*base71 + (33540424581059/108745000000000000000000000 : ℝ)*base72 + (150441354389/292125000000000000000000 : ℝ)*base74 + (2337506617321/31070000000000000000000000 : ℝ)*base77 + (16655704928578889/127068532500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p028_b033 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c328070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c328071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p028_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
