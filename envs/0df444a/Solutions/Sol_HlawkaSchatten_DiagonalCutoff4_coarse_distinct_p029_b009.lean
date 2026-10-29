-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:26:10.8576+00:00
-- url     : https://prove2.me/submissions/b26509d9-cf46-498f-8507-523e5bc6141c

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
theorem collision_support_c329023_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (589418453/1000000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (1335334619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589418453/1000000000 : ℝ)^95 ≤ (52957474789181/100000000000000 : ℝ)^79 := by
    have hnat : (589418453 : ℕ)^95*100000000000000^79 ≤ 52957474789181^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589418453 1000000000 52957474789181 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^95 ≤ (0 : ℝ)^79 := by
    have hnat : (0 : ℕ)^95*1^79 ≤ 0^79*1^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1335334619/2500000000 : ℝ)^95 ≤ (11760631300079/25000000000000 : ℝ)^79 := by
    have hnat : (1335334619 : ℕ)^95*25000000000000^79 ≤ 11760631300079^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335334619 2500000000 11760631300079 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(589418453/1000000000 : ℝ), (0 : ℝ), (1335334619/2500000000 : ℝ)] ![(52957474789181/100000000000000 : ℝ), (0 : ℝ), (11760631300079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(589418453/1000000000 : ℝ)|^95 ≤ (52957474789181/100000000000000 : ℝ)^79
        have hw : |(589418453/1000000000 : ℝ)|=(589418453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^95 ≤ (0 : ℝ)^79
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1335334619/2500000000 : ℝ)|^95 ≤ (11760631300079/25000000000000 : ℝ)^79
        have hw : |(1335334619/2500000000 : ℝ)|=(1335334619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (542866243/2000000000 : ℝ)*x 0 + (1221030597/2000000000 : ℝ)*x 1 + (-1521382389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542866243/2000000000 : ℝ)^95 ≤ (166744543617/800000000000 : ℝ)^79 := by
    have hnat : (542866243 : ℕ)^95*800000000000^79 ≤ 166744543617^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542866243 2000000000 166744543617 800000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221030597/2000000000 : ℝ)^95 ≤ (13811260909593/25000000000000 : ℝ)^79 := by
    have hnat : (1221030597 : ℕ)^95*25000000000000^79 ≤ 13811260909593^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221030597 2000000000 13811260909593 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1521382389/5000000000 : ℝ)^95 ≤ (23911888400071/100000000000000 : ℝ)^79 := by
    have hnat : (1521382389 : ℕ)^95*100000000000000^79 ≤ 23911888400071^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521382389 5000000000 23911888400071 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542866243/2000000000 : ℝ), (1221030597/2000000000 : ℝ), (-1521382389/5000000000 : ℝ)] ![(166744543617/800000000000 : ℝ), (13811260909593/25000000000000 : ℝ), (23911888400071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542866243/2000000000 : ℝ)|^95 ≤ (166744543617/800000000000 : ℝ)^79
        have hw : |(542866243/2000000000 : ℝ)|=(542866243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1221030597/2000000000 : ℝ)|^95 ≤ (13811260909593/25000000000000 : ℝ)^79
        have hw : |(1221030597/2000000000 : ℝ)|=(1221030597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1521382389/5000000000 : ℝ)|^95 ≤ (23911888400071/100000000000000 : ℝ)^79
        have hw : |(-1521382389/5000000000 : ℝ)|=(1521382389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3484961951/10000000000 : ℝ)*x 0 + (116777781/500000000 : ℝ)*x 1 + (3016147313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3484961951/10000000000 : ℝ)^95 ≤ (5630003337889/20000000000000 : ℝ)^79 := by
    have hnat : (3484961951 : ℕ)^95*20000000000000^79 ≤ 5630003337889^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3484961951 10000000000 5630003337889 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116777781/500000000 : ℝ)^95 ≤ (3479358992791/20000000000000 : ℝ)^79 := by
    have hnat : (116777781 : ℕ)^95*20000000000000^79 ≤ 3479358992791^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116777781 500000000 3479358992791 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3016147313/5000000000 : ℝ)^95 ≤ (217812753323/400000000000 : ℝ)^79 := by
    have hnat : (3016147313 : ℕ)^95*400000000000^79 ≤ 217812753323^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016147313 5000000000 217812753323 400000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3484961951/10000000000 : ℝ), (116777781/500000000 : ℝ), (3016147313/5000000000 : ℝ)] ![(5630003337889/20000000000000 : ℝ), (3479358992791/20000000000000 : ℝ), (217812753323/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3484961951/10000000000 : ℝ)|^95 ≤ (5630003337889/20000000000000 : ℝ)^79
        have hw : |(-3484961951/10000000000 : ℝ)|=(3484961951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116777781/500000000 : ℝ)|^95 ≤ (3479358992791/20000000000000 : ℝ)^79
        have hw : |(116777781/500000000 : ℝ)|=(116777781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3016147313/5000000000 : ℝ)|^95 ≤ (217812753323/400000000000 : ℝ)^79
        have hw : |(3016147313/5000000000 : ℝ)|=(3016147313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (97429747/200000000 : ℝ)*x 0 + (507/2000000000 : ℝ)*x 1 + (317354941/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97429747/200000000 : ℝ)^95 ≤ (42111737918521/100000000000000 : ℝ)^79 := by
    have hnat : (97429747 : ℕ)^95*100000000000000^79 ≤ 42111737918521^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97429747 200000000 42111737918521 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507/2000000000 : ℝ)^95 ≤ (1169701/100000000000000 : ℝ)^79 := by
    have hnat : (507 : ℕ)^95*100000000000000^79 ≤ 1169701^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507 2000000000 1169701 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317354941/500000000 : ℝ)^95 ≤ (57888260905721/100000000000000 : ℝ)^79 := by
    have hnat : (317354941 : ℕ)^95*100000000000000^79 ≤ 57888260905721^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317354941 500000000 57888260905721 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(97429747/200000000 : ℝ), (507/2000000000 : ℝ), (317354941/500000000 : ℝ)] ![(42111737918521/100000000000000 : ℝ), (1169701/100000000000000 : ℝ), (57888260905721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(97429747/200000000 : ℝ)|^95 ≤ (42111737918521/100000000000000 : ℝ)^79
        have hw : |(97429747/200000000 : ℝ)|=(97429747/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(507/2000000000 : ℝ)|^95 ≤ (1169701/100000000000000 : ℝ)^79
        have hw : |(507/2000000000 : ℝ)|=(507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317354941/500000000 : ℝ)|^95 ≤ (57888260905721/100000000000000 : ℝ)^79
        have hw : |(317354941/500000000 : ℝ)|=(317354941/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (45241579/400000000 : ℝ)*x 0 + (4095042509/5000000000 : ℝ)*x 1 + (-978886347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45241579/400000000 : ℝ)^95 ≤ (181851574299/2500000000000 : ℝ)^79 := by
    have hnat : (45241579 : ℕ)^95*2500000000000^79 ≤ 181851574299^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45241579 400000000 181851574299 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4095042509/5000000000 : ℝ)^95 ≤ (786550423107/1000000000000 : ℝ)^79 := by
    have hnat : (4095042509 : ℕ)^95*1000000000000^79 ≤ 786550423107^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4095042509 5000000000 786550423107 1000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978886347/5000000000 : ℝ)^95 ≤ (14070894711849/100000000000000 : ℝ)^79 := by
    have hnat : (978886347 : ℕ)^95*100000000000000^79 ≤ 14070894711849^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978886347 5000000000 14070894711849 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(45241579/400000000 : ℝ), (4095042509/5000000000 : ℝ), (-978886347/5000000000 : ℝ)] ![(181851574299/2500000000000 : ℝ), (786550423107/1000000000000 : ℝ), (14070894711849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(45241579/400000000 : ℝ)|^95 ≤ (181851574299/2500000000000 : ℝ)^79
        have hw : |(45241579/400000000 : ℝ)|=(45241579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4095042509/5000000000 : ℝ)|^95 ≤ (786550423107/1000000000000 : ℝ)^79
        have hw : |(4095042509/5000000000 : ℝ)|=(4095042509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978886347/5000000000 : ℝ)|^95 ≤ (14070894711849/100000000000000 : ℝ)^79
        have hw : |(-978886347/5000000000 : ℝ)|=(978886347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_12 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (450010173/2000000000 : ℝ)*x 0 + (1646104949/2500000000 : ℝ)*x 1 + (2931608801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450010173/2000000000 : ℝ)^95 ≤ (3326754702177/20000000000000 : ℝ)^79 := by
    have hnat : (450010173 : ℕ)^95*20000000000000^79 ≤ 3326754702177^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450010173 2000000000 3326754702177 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1646104949/2500000000 : ℝ)^95 ≤ (30250431180651/50000000000000 : ℝ)^79 := by
    have hnat : (1646104949 : ℕ)^95*50000000000000^79 ≤ 30250431180651^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646104949 2500000000 30250431180651 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2931608801/10000000000 : ℝ)^95 ≤ (2286536410893/10000000000000 : ℝ)^79 := by
    have hnat : (2931608801 : ℕ)^95*10000000000000^79 ≤ 2286536410893^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2931608801 10000000000 2286536410893 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450010173/2000000000 : ℝ), (1646104949/2500000000 : ℝ), (2931608801/10000000000 : ℝ)] ![(3326754702177/20000000000000 : ℝ), (30250431180651/50000000000000 : ℝ), (2286536410893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450010173/2000000000 : ℝ)|^95 ≤ (3326754702177/20000000000000 : ℝ)^79
        have hw : |(450010173/2000000000 : ℝ)|=(450010173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1646104949/2500000000 : ℝ)|^95 ≤ (30250431180651/50000000000000 : ℝ)^79
        have hw : |(1646104949/2500000000 : ℝ)|=(1646104949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2931608801/10000000000 : ℝ)|^95 ≤ (2286536410893/10000000000000 : ℝ)^79
        have hw : |(2931608801/10000000000 : ℝ)|=(2931608801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2581416397/5000000000 : ℝ)*x 0 + (4156887101/10000000000 : ℝ)*x 1 + (164215333/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2581416397/5000000000 : ℝ)^95 ≤ (45158427058591/100000000000000 : ℝ)^79 := by
    have hnat : (2581416397 : ℕ)^95*100000000000000^79 ≤ 45158427058591^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581416397 5000000000 45158427058591 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4156887101/10000000000 : ℝ)^95 ≤ (8699549033493/25000000000000 : ℝ)^79 := by
    have hnat : (4156887101 : ℕ)^95*25000000000000^79 ≤ 8699549033493^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156887101 10000000000 8699549033493 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164215333/625000000 : ℝ)^95 ≤ (10021688391977/50000000000000 : ℝ)^79 := by
    have hnat : (164215333 : ℕ)^95*50000000000000^79 ≤ 10021688391977^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164215333 625000000 10021688391977 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2581416397/5000000000 : ℝ), (4156887101/10000000000 : ℝ), (164215333/625000000 : ℝ)] ![(45158427058591/100000000000000 : ℝ), (8699549033493/25000000000000 : ℝ), (10021688391977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2581416397/5000000000 : ℝ)|^95 ≤ (45158427058591/100000000000000 : ℝ)^79
        have hw : |(-2581416397/5000000000 : ℝ)|=(2581416397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4156887101/10000000000 : ℝ)|^95 ≤ (8699549033493/25000000000000 : ℝ)^79
        have hw : |(4156887101/10000000000 : ℝ)|=(4156887101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164215333/625000000 : ℝ)|^95 ≤ (10021688391977/50000000000000 : ℝ)^79
        have hw : |(164215333/625000000 : ℝ)|=(164215333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3393641699/5000000000 : ℝ)*x 0 + (11781/500000000 : ℝ)*x 1 + (1099769079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3393641699/5000000000 : ℝ)^95 ≤ (62749330101109/100000000000000 : ℝ)^79 := by
    have hnat : (3393641699 : ℕ)^95*100000000000000^79 ≤ 62749330101109^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3393641699 5000000000 62749330101109 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11781/500000000 : ℝ)^95 ≤ (272231681/100000000000000 : ℝ)^79 := by
    have hnat : (11781 : ℕ)^95*100000000000000^79 ≤ 272231681^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11781 500000000 272231681 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099769079/2500000000 : ℝ)^95 ≤ (37250397650269/100000000000000 : ℝ)^79 := by
    have hnat : (1099769079 : ℕ)^95*100000000000000^79 ≤ 37250397650269^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099769079 2500000000 37250397650269 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3393641699/5000000000 : ℝ), (11781/500000000 : ℝ), (1099769079/2500000000 : ℝ)] ![(62749330101109/100000000000000 : ℝ), (272231681/100000000000000 : ℝ), (37250397650269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3393641699/5000000000 : ℝ)|^95 ≤ (62749330101109/100000000000000 : ℝ)^79
        have hw : |(3393641699/5000000000 : ℝ)|=(3393641699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11781/500000000 : ℝ)|^95 ≤ (272231681/100000000000000 : ℝ)^79
        have hw : |(11781/500000000 : ℝ)|=(11781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099769079/2500000000 : ℝ)|^95 ≤ (37250397650269/100000000000000 : ℝ)^79
        have hw : |(1099769079/2500000000 : ℝ)|=(1099769079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (882554051/10000000000 : ℝ)*x 0 + (5732632699/10000000000 : ℝ)*x 1 + (-624211083/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882554051/10000000000 : ℝ)^95 ≤ (5397846943727/100000000000000 : ℝ)^79 := by
    have hnat : (882554051 : ℕ)^95*100000000000000^79 ≤ 5397846943727^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882554051 10000000000 5397846943727 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5732632699/10000000000 : ℝ)^95 ≤ (12804221748667/25000000000000 : ℝ)^79 := by
    have hnat : (5732632699 : ℕ)^95*25000000000000^79 ≤ 12804221748667^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5732632699 10000000000 12804221748667 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624211083/1250000000 : ℝ)^95 ≤ (43385266038239/100000000000000 : ℝ)^79 := by
    have hnat : (624211083 : ℕ)^95*100000000000000^79 ≤ 43385266038239^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624211083 1250000000 43385266038239 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(882554051/10000000000 : ℝ), (5732632699/10000000000 : ℝ), (-624211083/1250000000 : ℝ)] ![(5397846943727/100000000000000 : ℝ), (12804221748667/25000000000000 : ℝ), (43385266038239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(882554051/10000000000 : ℝ)|^95 ≤ (5397846943727/100000000000000 : ℝ)^79
        have hw : |(882554051/10000000000 : ℝ)|=(882554051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5732632699/10000000000 : ℝ)|^95 ≤ (12804221748667/25000000000000 : ℝ)^79
        have hw : |(5732632699/10000000000 : ℝ)|=(5732632699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-624211083/1250000000 : ℝ)|^95 ≤ (43385266038239/100000000000000 : ℝ)^79
        have hw : |(-624211083/1250000000 : ℝ)|=(624211083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_19 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1278357223/5000000000 : ℝ)*x 0 + (645111933/1250000000 : ℝ)*x 1 + (2111541587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1278357223/5000000000 : ℝ)^95 ≤ (3879262135081/20000000000000 : ℝ)^79 := by
    have hnat : (1278357223 : ℕ)^95*20000000000000^79 ≤ 3879262135081^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278357223 5000000000 3879262135081 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645111933/1250000000 : ℝ)^95 ≤ (22569025167389/50000000000000 : ℝ)^79 := by
    have hnat : (645111933 : ℕ)^95*50000000000000^79 ≤ 22569025167389^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645111933 1250000000 22569025167389 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111541587/5000000000 : ℝ)^95 ≤ (4433204872629/12500000000000 : ℝ)^79 := by
    have hnat : (2111541587 : ℕ)^95*12500000000000^79 ≤ 4433204872629^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111541587 5000000000 4433204872629 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1278357223/5000000000 : ℝ), (645111933/1250000000 : ℝ), (2111541587/5000000000 : ℝ)] ![(3879262135081/20000000000000 : ℝ), (22569025167389/50000000000000 : ℝ), (4433204872629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1278357223/5000000000 : ℝ)|^95 ≤ (3879262135081/20000000000000 : ℝ)^79
        have hw : |(1278357223/5000000000 : ℝ)|=(1278357223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(645111933/1250000000 : ℝ)|^95 ≤ (22569025167389/50000000000000 : ℝ)^79
        have hw : |(645111933/1250000000 : ℝ)|=(645111933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111541587/5000000000 : ℝ)|^95 ≤ (4433204872629/12500000000000 : ℝ)^79
        have hw : |(2111541587/5000000000 : ℝ)|=(2111541587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079445847/5000000000 : ℝ)*x 0 + (771521079/1250000000 : ℝ)*x 1 + (3489918303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079445847/5000000000 : ℝ)^95 ≤ (791337122379/5000000000000 : ℝ)^79 := by
    have hnat : (1079445847 : ℕ)^95*5000000000000^79 ≤ 791337122379^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079445847 5000000000 791337122379 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771521079/1250000000 : ℝ)^95 ≤ (6996886280383/12500000000000 : ℝ)^79 := by
    have hnat : (771521079 : ℕ)^95*12500000000000^79 ≤ 6996886280383^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771521079 1250000000 6996886280383 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3489918303/10000000000 : ℝ)^95 ≤ (28198167299269/100000000000000 : ℝ)^79 := by
    have hnat : (3489918303 : ℕ)^95*100000000000000^79 ≤ 28198167299269^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3489918303 10000000000 28198167299269 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079445847/5000000000 : ℝ), (771521079/1250000000 : ℝ), (3489918303/10000000000 : ℝ)] ![(791337122379/5000000000000 : ℝ), (6996886280383/12500000000000 : ℝ), (28198167299269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079445847/5000000000 : ℝ)|^95 ≤ (791337122379/5000000000000 : ℝ)^79
        have hw : |(-1079445847/5000000000 : ℝ)|=(1079445847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771521079/1250000000 : ℝ)|^95 ≤ (6996886280383/12500000000000 : ℝ)^79
        have hw : |(771521079/1250000000 : ℝ)|=(771521079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3489918303/10000000000 : ℝ)|^95 ≤ (28198167299269/100000000000000 : ℝ)^79
        have hw : |(3489918303/10000000000 : ℝ)|=(3489918303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7944631509/10000000000 : ℝ)*x 0 + (-1/15625000 : ℝ)*x 1 + (1535077329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7944631509/10000000000 : ℝ)^95 ≤ (18957258883331/25000000000000 : ℝ)^79 := by
    have hnat : (7944631509 : ℕ)^95*25000000000000^79 ≤ 18957258883331^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7944631509 10000000000 18957258883331 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1/15625000 : ℝ)^95 ≤ (223463/100000000000000 : ℝ)^79 := by
    have hnat : (1 : ℕ)^95*100000000000000^79 ≤ 223463^79*15625000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 15625000 223463 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1535077329/5000000000 : ℝ)^95 ≤ (24170964231317/100000000000000 : ℝ)^79 := by
    have hnat : (1535077329 : ℕ)^95*100000000000000^79 ≤ 24170964231317^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535077329 5000000000 24170964231317 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7944631509/10000000000 : ℝ), (-1/15625000 : ℝ), (1535077329/5000000000 : ℝ)] ![(18957258883331/25000000000000 : ℝ), (223463/100000000000000 : ℝ), (24170964231317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7944631509/10000000000 : ℝ)|^95 ≤ (18957258883331/25000000000000 : ℝ)^79
        have hw : |(7944631509/10000000000 : ℝ)|=(7944631509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1/15625000 : ℝ)|^95 ≤ (223463/100000000000000 : ℝ)^79
        have hw : |(-1/15625000 : ℝ)|=(1/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1535077329/5000000000 : ℝ)|^95 ≤ (24170964231317/100000000000000 : ℝ)^79
        have hw : |(1535077329/5000000000 : ℝ)|=(1535077329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (697878833/10000000000 : ℝ)*x 0 + (3876149629/5000000000 : ℝ)*x 1 + (-2871517757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (697878833/10000000000 : ℝ)^95 ≤ (407013573/10000000000 : ℝ)^79 := by
    have hnat : (697878833 : ℕ)^95*10000000000^79 ≤ 407013573^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697878833 10000000000 407013573 10000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3876149629/5000000000 : ℝ)^95 ≤ (73626933413623/100000000000000 : ℝ)^79 := by
    have hnat : (3876149629 : ℕ)^95*100000000000000^79 ≤ 73626933413623^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3876149629 5000000000 73626933413623 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2871517757/10000000000 : ℝ)^95 ≤ (5575732712657/25000000000000 : ℝ)^79 := by
    have hnat : (2871517757 : ℕ)^95*25000000000000^79 ≤ 5575732712657^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2871517757 10000000000 5575732712657 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(697878833/10000000000 : ℝ), (3876149629/5000000000 : ℝ), (-2871517757/10000000000 : ℝ)] ![(407013573/10000000000 : ℝ), (73626933413623/100000000000000 : ℝ), (5575732712657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(697878833/10000000000 : ℝ)|^95 ≤ (407013573/10000000000 : ℝ)^79
        have hw : |(697878833/10000000000 : ℝ)|=(697878833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3876149629/5000000000 : ℝ)|^95 ≤ (73626933413623/100000000000000 : ℝ)^79
        have hw : |(3876149629/5000000000 : ℝ)|=(3876149629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2871517757/10000000000 : ℝ)|^95 ≤ (5575732712657/25000000000000 : ℝ)^79
        have hw : |(-2871517757/10000000000 : ℝ)|=(2871517757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_24 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-157/2000000000 : ℝ)*x 0 + (624999997/625000000 : ℝ)*x 1 + (-157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157/2000000000 : ℝ)^95 ≤ (57133/20000000000000 : ℝ)^79 := by
    have hnat : (157 : ℕ)^95*20000000000000^79 ≤ 57133^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157 2000000000 57133 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624999997/625000000 : ℝ)^95 ≤ (19999999884557/20000000000000 : ℝ)^79 := by
    have hnat : (624999997 : ℕ)^95*20000000000000^79 ≤ 19999999884557^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624999997 625000000 19999999884557 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157/2000000000 : ℝ)^95 ≤ (57133/20000000000000 : ℝ)^79 := by
    have hnat : (157 : ℕ)^95*20000000000000^79 ≤ 57133^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157 2000000000 57133 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-157/2000000000 : ℝ), (624999997/625000000 : ℝ), (-157/2000000000 : ℝ)] ![(57133/20000000000000 : ℝ), (19999999884557/20000000000000 : ℝ), (57133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-157/2000000000 : ℝ)|^95 ≤ (57133/20000000000000 : ℝ)^79
        have hw : |(-157/2000000000 : ℝ)|=(157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624999997/625000000 : ℝ)|^95 ≤ (19999999884557/20000000000000 : ℝ)^79
        have hw : |(624999997/625000000 : ℝ)|=(624999997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157/2000000000 : ℝ)|^95 ≤ (57133/20000000000000 : ℝ)^79
        have hw : |(-157/2000000000 : ℝ)|=(157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s0_26 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3176086333/5000000000 : ℝ)*x 0 + (617546781/2000000000 : ℝ)*x 1 + (2371426361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3176086333/5000000000 : ℝ)^95 ≤ (463551306741/800000000000 : ℝ)^79 := by
    have hnat : (3176086333 : ℕ)^95*800000000000^79 ≤ 463551306741^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3176086333 5000000000 463551306741 800000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617546781/2000000000 : ℝ)^95 ≤ (2433749016131/10000000000000 : ℝ)^79 := by
    have hnat : (617546781 : ℕ)^95*10000000000000^79 ≤ 2433749016131^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617546781 2000000000 2433749016131 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371426361/10000000000 : ℝ)^95 ≤ (17718596483207/100000000000000 : ℝ)^79 := by
    have hnat : (2371426361 : ℕ)^95*100000000000000^79 ≤ 17718596483207^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371426361 10000000000 17718596483207 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3176086333/5000000000 : ℝ), (617546781/2000000000 : ℝ), (2371426361/10000000000 : ℝ)] ![(463551306741/800000000000 : ℝ), (2433749016131/10000000000000 : ℝ), (17718596483207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3176086333/5000000000 : ℝ)|^95 ≤ (463551306741/800000000000 : ℝ)^79
        have hw : |(3176086333/5000000000 : ℝ)|=(3176086333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(617546781/2000000000 : ℝ)|^95 ≤ (2433749016131/10000000000000 : ℝ)^79
        have hw : |(617546781/2000000000 : ℝ)|=(617546781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2371426361/10000000000 : ℝ)|^95 ≤ (17718596483207/100000000000000 : ℝ)^79
        have hw : |(2371426361/10000000000 : ℝ)|=(2371426361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-661112269/2000000000 : ℝ)*x 0 + (2588556791/5000000000 : ℝ)*x 1 + (3497793811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661112269/2000000000 : ℝ)^95 ≤ (13208307440579/50000000000000 : ℝ)^79 := by
    have hnat : (661112269 : ℕ)^95*50000000000000^79 ≤ 13208307440579^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661112269 2000000000 13208307440579 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588556791/5000000000 : ℝ)^95 ≤ (22654339652843/50000000000000 : ℝ)^79 := by
    have hnat : (2588556791 : ℕ)^95*50000000000000^79 ≤ 22654339652843^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588556791 5000000000 22654339652843 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3497793811/10000000000 : ℝ)^95 ≤ (2827470578893/10000000000000 : ℝ)^79 := by
    have hnat : (3497793811 : ℕ)^95*10000000000000^79 ≤ 2827470578893^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3497793811 10000000000 2827470578893 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-661112269/2000000000 : ℝ), (2588556791/5000000000 : ℝ), (3497793811/10000000000 : ℝ)] ![(13208307440579/50000000000000 : ℝ), (22654339652843/50000000000000 : ℝ), (2827470578893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-661112269/2000000000 : ℝ)|^95 ≤ (13208307440579/50000000000000 : ℝ)^79
        have hw : |(-661112269/2000000000 : ℝ)|=(661112269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588556791/5000000000 : ℝ)|^95 ≤ (22654339652843/50000000000000 : ℝ)^79
        have hw : |(2588556791/5000000000 : ℝ)|=(2588556791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3497793811/10000000000 : ℝ)|^95 ≤ (2827470578893/10000000000000 : ℝ)^79
        have hw : |(3497793811/10000000000 : ℝ)|=(3497793811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2751698451/5000000000 : ℝ)*x 0 + (-467362753/5000000000 : ℝ)*x 1 + (5190733683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751698451/5000000000 : ℝ)^95 ≤ (12191029436057/25000000000000 : ℝ)^79 := by
    have hnat : (2751698451 : ℕ)^95*25000000000000^79 ≤ 12191029436057^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751698451 5000000000 12191029436057 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467362753/5000000000 : ℝ)^95 ≤ (180744491727/3125000000000 : ℝ)^79 := by
    have hnat : (467362753 : ℕ)^95*3125000000000^79 ≤ 180744491727^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467362753 5000000000 180744491727 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190733683/10000000000 : ℝ)^95 ≤ (22726029253631/50000000000000 : ℝ)^79 := by
    have hnat : (5190733683 : ℕ)^95*50000000000000^79 ≤ 22726029253631^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190733683 10000000000 22726029253631 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751698451/5000000000 : ℝ), (-467362753/5000000000 : ℝ), (5190733683/10000000000 : ℝ)] ![(12191029436057/25000000000000 : ℝ), (180744491727/3125000000000 : ℝ), (22726029253631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751698451/5000000000 : ℝ)|^95 ≤ (12191029436057/25000000000000 : ℝ)^79
        have hw : |(2751698451/5000000000 : ℝ)|=(2751698451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-467362753/5000000000 : ℝ)|^95 ≤ (180744491727/3125000000000 : ℝ)^79
        have hw : |(-467362753/5000000000 : ℝ)|=(467362753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190733683/10000000000 : ℝ)|^95 ≤ (22726029253631/50000000000000 : ℝ)^79
        have hw : |(5190733683/10000000000 : ℝ)|=(5190733683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3130681753/10000000000 : ℝ)*x 0 + (687984301/1250000000 : ℝ)*x 1 + (-1656372113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3130681753/10000000000 : ℝ)^95 ≤ (24745135877891/100000000000000 : ℝ)^79 := by
    have hnat : (3130681753 : ℕ)^95*100000000000000^79 ≤ 24745135877891^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3130681753 10000000000 24745135877891 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687984301/1250000000 : ℝ)^95 ≤ (4876920576293/10000000000000 : ℝ)^79 := by
    have hnat : (687984301 : ℕ)^95*10000000000000^79 ≤ 4876920576293^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687984301 1250000000 4876920576293 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1656372113/5000000000 : ℝ)^95 ≤ (13242829177061/50000000000000 : ℝ)^79 := by
    have hnat : (1656372113 : ℕ)^95*50000000000000^79 ≤ 13242829177061^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656372113 5000000000 13242829177061 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3130681753/10000000000 : ℝ), (687984301/1250000000 : ℝ), (-1656372113/5000000000 : ℝ)] ![(24745135877891/100000000000000 : ℝ), (4876920576293/10000000000000 : ℝ), (13242829177061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3130681753/10000000000 : ℝ)|^95 ≤ (24745135877891/100000000000000 : ℝ)^79
        have hw : |(3130681753/10000000000 : ℝ)|=(3130681753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687984301/1250000000 : ℝ)|^95 ≤ (4876920576293/10000000000000 : ℝ)^79
        have hw : |(687984301/1250000000 : ℝ)|=(687984301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1656372113/5000000000 : ℝ)|^95 ≤ (13242829177061/50000000000000 : ℝ)^79
        have hw : |(-1656372113/5000000000 : ℝ)|=(1656372113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329023_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3704058157/10000000000 : ℝ)*x 0 + (300630657/625000000 : ℝ)*x 1 + (698724071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3704058157/10000000000 : ℝ)^95 ≤ (30291543361219/100000000000000 : ℝ)^79 := by
    have hnat : (3704058157 : ℕ)^95*100000000000000^79 ≤ 30291543361219^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704058157 10000000000 30291543361219 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300630657/625000000 : ℝ)^95 ≤ (41474315112697/100000000000000 : ℝ)^79 := by
    have hnat : (300630657 : ℕ)^95*100000000000000^79 ≤ 41474315112697^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300630657 625000000 41474315112697 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (698724071/2000000000 : ℝ)^95 ≤ (14117070755559/50000000000000 : ℝ)^79 := by
    have hnat : (698724071 : ℕ)^95*50000000000000^79 ≤ 14117070755559^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698724071 2000000000 14117070755559 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3704058157/10000000000 : ℝ), (300630657/625000000 : ℝ), (698724071/2000000000 : ℝ)] ![(30291543361219/100000000000000 : ℝ), (41474315112697/100000000000000 : ℝ), (14117070755559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3704058157/10000000000 : ℝ)|^95 ≤ (30291543361219/100000000000000 : ℝ)^79
        have hw : |(3704058157/10000000000 : ℝ)|=(3704058157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300630657/625000000 : ℝ)|^95 ≤ (41474315112697/100000000000000 : ℝ)^79
        have hw : |(300630657/625000000 : ℝ)|=(300630657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(698724071/2000000000 : ℝ)|^95 ≤ (14117070755559/50000000000000 : ℝ)^79
        have hw : |(698724071/2000000000 : ℝ)|=(698724071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329023 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((589418453/1000000000 : ℝ)*X 1 0+(1335334619/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((542866243/2000000000 : ℝ)*X 2 0+(1221030597/2000000000 : ℝ)*X 2 1+(-1521382389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3484961951/10000000000 : ℝ)*X 0 0+(116777781/500000000 : ℝ)*X 0 1+(3016147313/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((97429747/200000000 : ℝ)*X 1 0+(507/2000000000 : ℝ)*X 1 1+(317354941/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((45241579/400000000 : ℝ)*X 2 0+(4095042509/5000000000 : ℝ)*X 2 1+(-978886347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((450010173/2000000000 : ℝ)*X 0 0+(1646104949/2500000000 : ℝ)*X 0 1+(2931608801/10000000000 : ℝ)*X 0 2+(450010173/2000000000 : ℝ)*X 1 0+(1646104949/2500000000 : ℝ)*X 1 1+(2931608801/10000000000 : ℝ)*X 1 2+(450010173/2000000000 : ℝ)*X 2 0+(1646104949/2500000000 : ℝ)*X 2 1+(2931608801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2581416397/5000000000 : ℝ)*X 0 0+(4156887101/10000000000 : ℝ)*X 0 1+(164215333/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3393641699/5000000000 : ℝ)*X 1 0+(11781/500000000 : ℝ)*X 1 1+(1099769079/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((882554051/10000000000 : ℝ)*X 2 0+(5732632699/10000000000 : ℝ)*X 2 1+(-624211083/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1278357223/5000000000 : ℝ)*X 0 0+(645111933/1250000000 : ℝ)*X 0 1+(2111541587/5000000000 : ℝ)*X 0 2+(1278357223/5000000000 : ℝ)*X 1 0+(645111933/1250000000 : ℝ)*X 1 1+(2111541587/5000000000 : ℝ)*X 1 2+(1278357223/5000000000 : ℝ)*X 2 0+(645111933/1250000000 : ℝ)*X 2 1+(2111541587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1079445847/5000000000 : ℝ)*X 0 0+(771521079/1250000000 : ℝ)*X 0 1+(3489918303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((7944631509/10000000000 : ℝ)*X 1 0+(-1/15625000 : ℝ)*X 1 1+(1535077329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((697878833/10000000000 : ℝ)*X 2 0+(3876149629/5000000000 : ℝ)*X 2 1+(-2871517757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_24 : ((-157/2000000000 : ℝ)*X 0 0+(624999997/625000000 : ℝ)*X 0 1+(-157/2000000000 : ℝ)*X 0 2+(-157/2000000000 : ℝ)*X 2 0+(624999997/625000000 : ℝ)*X 2 1+(-157/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_24 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((3176086333/5000000000 : ℝ)*X 0 0+(617546781/2000000000 : ℝ)*X 0 1+(2371426361/10000000000 : ℝ)*X 0 2+(3176086333/5000000000 : ℝ)*X 1 0+(617546781/2000000000 : ℝ)*X 1 1+(2371426361/10000000000 : ℝ)*X 1 2+(3176086333/5000000000 : ℝ)*X 2 0+(617546781/2000000000 : ℝ)*X 2 1+(2371426361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((13213/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13213/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9258303996389670821973/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309961882969/250000000000 : ℝ)*(base7) + (45373021991/200000000000 : ℝ)*(base50) + (4313337/500000000000 : ℝ)*(base53) + (4752569243/125000000000 : ℝ)*(base60) + (41334084627/25000000000 : ℝ)*(major_s0_0) + (1868954273147/1000000000000 : ℝ)*(major_s0_1) + (826677379203/500000000000 : ℝ)*(major_s0_2) + (475200896947/250000000000 : ℝ)*(sp_s0_7) + (380166384321/200000000000 : ℝ)*(sp_s0_8) + (1900824146527/1000000000000 : ℝ)*(sp_s0_9) + (1983413428493/1000000000000 : ℝ)*(sp_s0_12) + (14166909/500000000000 : ℝ)*(sp_s0_20) + (2050219/125000000000 : ℝ)*(sp_s0_22) + (215590888067/1000000000000 : ℝ)*(sp_s0_24) + (92945737077/125000000000 : ℝ)*(f.failure) + (47521013707/25000000000 : ℝ)*(f.sum) + (788296719317837/10000000000000000000000000000 : ℝ)*base62 + (1424698754824603/5000000000000000000000000000 : ℝ)*base64 + (7325988758942253/10000000000000000000000000000 : ℝ)*base66 + (3828992330224629/5000000000000000000000000000 : ℝ)*base68 + (1581855852694177/5000000000000000000000000000 : ℝ)*base71 + (4447172841773/250000000000000000000000000 : ℝ)*base73 + (1943636074868579/10000000000000000000000000000 : ℝ)*base74 + (6752828599061/250000000000000000000000000 : ℝ)*base76 + (4423986708271333/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1647/3125000000000000 : ℝ)*base86 + (1647/3125000000000000 : ℝ)*base88 + (1647/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20823/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(20823/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (763143109272152686059/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (15103209/1000000000000 : ℝ)*(base3) + (212708905871/500000000000 : ℝ)*(base7) + (287271018479/1000000000000 : ℝ)*(base40) + (442944116403/1000000000000 : ℝ)*(base49) + (12770712021/500000000000 : ℝ)*(base60) + (875807762567/500000000000 : ℝ)*(major_s0_0) + (875807762567/500000000000 : ℝ)*(major_s0_1) + (875807762567/500000000000 : ℝ)*(major_s0_2) + (3849101/125000000000 : ℝ)*(sp_s0_1) + (92757/100000000000 : ℝ)*(sp_s0_2) + (1244111361109/500000000000 : ℝ)*(sp_s0_13) + (2488207032619/1000000000000 : ℝ)*(sp_s0_14) + (2488221794649/1000000000000 : ℝ)*(sp_s0_15) + (606577733841/500000000000 : ℝ)*(sp_s0_19) + (787752759149/1000000000000 : ℝ)*(f.failure) + (1244111361109/500000000000 : ℝ)*(f.sum) + (85317927/250000000000000000000 : ℝ)*base62 + (4917825068296833/5000000000000000000000000000 : ℝ)*base65 + (570382612703167/5000000000000000000000000000 : ℝ)*base67 + (2016973131877519/5000000000000000000000000000 : ℝ)*base69 + (210680356635897/312500000000000000000000000 : ℝ)*base71 + (3393269861296833/5000000000000000000000000000 : ℝ)*base73 + (1276397570622481/5000000000000000000000000000 : ℝ)*base75 + (957090744377519/5000000000000000000000000000 : ℝ)*base77 + (1427299/78125000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (16239/25000000000000000 : ℝ)*base86 + (16239/25000000000000000 : ℝ)*base88 + (16239/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28681/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28681/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16785730844752361283/2441406250000000000000000 : ℝ) := by norm_num
    linear_combination (892749/1000000000000 : ℝ)*(base3) + (1278698002777/1000000000000 : ℝ)*(base7) + (833577/200000000000 : ℝ)*(base11) + (33183306439/125000000000 : ℝ)*(base40) + (16489812127/125000000000 : ℝ)*(base50) + (233716756661/125000000000 : ℝ)*(major_s0_0) + (233716756661/125000000000 : ℝ)*(major_s0_1) + (233716756661/125000000000 : ℝ)*(major_s0_2) + (9922427/1000000000000 : ℝ)*(sp_s0_2) + (1383711/40000000000 : ℝ)*(sp_s0_9) + (221551984301/100000000000 : ℝ)*(sp_s0_20) + (2215524903643/1000000000000 : ℝ)*(sp_s0_21) + (2215479495693/1000000000000 : ℝ)*(sp_s0_22) + (2119571227789/1000000000000 : ℝ)*(sp_s0_26) + (840874117761/1000000000000 : ℝ)*(f.failure) + (443104802179/200000000000 : ℝ)*(f.sum) + (2563771733/5000000000000000000000 : ℝ)*base63 + (756997900931461/1250000000000000000000000000 : ℝ)*base64 + (832490377068539/1250000000000000000000000000 : ℝ)*base66 + (160848957094277/1250000000000000000000000000 : ℝ)*base69 + (19254608589023/156250000000000000000000000 : ℝ)*base70 + (15499970681461/1250000000000000000000000000 : ℝ)*base72 + (323358988655723/1250000000000000000000000000 : ℝ)*base75 + (713590870780723/1250000000000000000000000000 : ℝ)*base76 + (605815793/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (16229/25000000000000000 : ℝ)*base87 + (16229/25000000000000000 : ℝ)*base89 + (16229/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (13213/25000 : ℝ) ^ (93/16 : ℝ) ≤ (1228187137488039829/50000000000000000000 : ℝ) := by
    have hpowers : (13213/25000 : ℝ)^93 ≤ (1228187137488039829/50000000000000000000 : ℝ)^16 := by
      have hnat : (13213 : ℕ)^93*50000000000000000000^16 ≤ 1228187137488039829^16*25000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13213 25000 1228187137488039829 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13213/25000 : ℝ)) (X := (1228187137488039829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51228187137488039829/50000000000000000000 : ℝ) ≤ (1255229598345237/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (51228187137488039829/50000000000000000000 : ℝ)^16 ≤ (1255229598345237/1250000000000000 : ℝ)^93 := by
      have hnat : (51228187137488039829 : ℕ)^16*1250000000000000^93 ≤ 1255229598345237^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51228187137488039829 50000000000000000000 1255229598345237 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255229598345237/1250000000000000 : ℝ)) (X := (51228187137488039829/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26228187137488039829/25000000000000000000 : ℝ) ≤ (315089099554723/312500000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (26228187137488039829/25000000000000000000 : ℝ)^16 ≤ (315089099554723/312500000000000 : ℝ)^93 := by
      have hnat : (26228187137488039829 : ℕ)^16*312500000000000^93 ≤ 315089099554723^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26228187137488039829 25000000000000000000 315089099554723 312500000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315089099554723/312500000000000 : ℝ)) (X := (26228187137488039829/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5229598345237/660650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1025359974731/132130000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (13213/25000 : ℝ)) (alpha := (5229598345237/660650000000000 : ℝ)) (beta := (1025359974731/132130000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13213/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5229598345237/660650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1025359974731/132130000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (20823/100000 : ℝ) ^ (93/16 : ℝ) ≤ (136754913499587/1250000000000000000 : ℝ) := by
    have hpowers : (20823/100000 : ℝ)^93 ≤ (136754913499587/1250000000000000000 : ℝ)^16 := by
      have hnat : (20823 : ℕ)^93*1250000000000000000^16 ≤ 136754913499587^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20823 100000 136754913499587 1250000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20823/100000 : ℝ)) (X := (136754913499587/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (1250136754913499587/1250000000000000000 : ℝ) ≤ (2500047053323067/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (1250136754913499587/1250000000000000000 : ℝ)^16 ≤ (2500047053323067/2500000000000000 : ℝ)^93 := by
      have hnat : (1250136754913499587 : ℕ)^16*2500000000000000^93 ≤ 2500047053323067^93*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250136754913499587 1250000000000000000 2500047053323067 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500047053323067/2500000000000000 : ℝ)) (X := (1250136754913499587/1250000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (625136754913499587/625000000000000000 : ℝ) ≤ (5000188204769241/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (625136754913499587/625000000000000000 : ℝ)^16 ≤ (5000188204769241/5000000000000000 : ℝ)^93 := by
      have hnat : (625136754913499587 : ℕ)^16*5000000000000000^93 ≤ 5000188204769241^93*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625136754913499587 625000000000000000 5000188204769241 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000188204769241/5000000000000000 : ℝ)) (X := (625136754913499587/625000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(47053323067/520575000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(94098123107/1041150000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (20823/100000 : ℝ)) (alpha := (47053323067/520575000000000 : ℝ)) (beta := (94098123107/1041150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (20823/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(47053323067/520575000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(94098123107/1041150000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (28681/50000 : ℝ) ^ (93/16 : ℝ) ≤ (1976849748684852711/50000000000000000000 : ℝ) := by
    have hpowers : (28681/50000 : ℝ)^93 ≤ (1976849748684852711/50000000000000000000 : ℝ)^16 := by
      have hnat : (28681 : ℕ)^93*50000000000000000000^16 ≤ 1976849748684852711^16*50000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28681 50000 1976849748684852711 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28681/50000 : ℝ)) (X := (1976849748684852711/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (51976849748684852711/50000000000000000000 : ℝ) ≤ (5033466702050391/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (51976849748684852711/50000000000000000000 : ℝ)^16 ≤ (5033466702050391/5000000000000000 : ℝ)^93 := by
      have hnat : (51976849748684852711 : ℕ)^16*5000000000000000^93 ≤ 5033466702050391^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51976849748684852711 50000000000000000000 5033466702050391 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033466702050391/5000000000000000 : ℝ)) (X := (51976849748684852711/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26976849748684852711/25000000000000000000 : ℝ) ≤ (1266473903090449/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (26976849748684852711/25000000000000000000 : ℝ)^16 ≤ (1266473903090449/1250000000000000 : ℝ)^93 := by
      have hnat : (26976849748684852711 : ℕ)^16*1250000000000000^93 ≤ 1266473903090449^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26976849748684852711 25000000000000000000 1266473903090449 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1266473903090449/1250000000000000 : ℝ)) (X := (26976849748684852711/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(33466702050391/2868100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(281990524447/24940000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (28681/50000 : ℝ)) (alpha := (33466702050391/2868100000000000 : ℝ)) (beta := (281990524447/24940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (28681/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(33466702050391/2868100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(281990524447/24940000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-661112269/2000000000 : ℝ)*X 0 0+(2588556791/5000000000 : ℝ)*X 0 1+(3497793811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2751698451/5000000000 : ℝ)*X 1 0+(-467362753/5000000000 : ℝ)*X 1 1+(5190733683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3130681753/10000000000 : ℝ)*X 2 0+(687984301/1250000000 : ℝ)*X 2 1+(-1656372113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3704058157/10000000000 : ℝ)*X 0 0+(300630657/625000000 : ℝ)*X 0 1+(698724071/2000000000 : ℝ)*X 0 2+(3704058157/10000000000 : ℝ)*X 1 0+(300630657/625000000 : ℝ)*X 1 1+(698724071/2000000000 : ℝ)*X 1 2+(3704058157/10000000000 : ℝ)*X 2 0+(300630657/625000000 : ℝ)*X 2 1+(698724071/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329023_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-11714674093111494377055110998050551/1143641569510000000000000000000000 : ℝ) := by norm_num
    linear_combination (137419/1000000000000 : ℝ)*(base7) + (75981/125000000000 : ℝ)*(base13) + (35123/500000000000 : ℝ)*(base15) + (6059/1000000000000 : ℝ)*(base24) + (51247/200000000000 : ℝ)*(base33) + (59555243531/500000000000 : ℝ)*(base40) + (1463698783067/1000000000000 : ℝ)*(base49) + (156800327631/200000000000 : ℝ)*(base50) + (444711948753/200000000000 : ℝ)*(major_s1_0) + (55589/25000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (1707217842269/500000000000 : ℝ)*(sp_s1_0) + (682887193181/200000000000 : ℝ)*(sp_s1_1) + (853609007523/250000000000 : ℝ)*(sp_s1_2) + (1000000137419/1000000000000 : ℝ)*(sp_s1_6) + (1707218146193/500000000000 : ℝ)*(f.sum) + (40804075325291099/5972244630000000000000000000000 : ℝ)*base62 + (1080376558983/3117500000000000000000000 : ℝ)*base65 + (22867620054151/208230000000000000000000000 : ℝ)*base67 + (68546884789667/286810000000000000000000000 : ℝ)*base69 + (62189699542249489/164766110000000000000000000000 : ℝ)*base71 + (218968018793/26426000000000000000000000 : ℝ)*base72 + (33131396952557/208230000000000000000000000 : ℝ)*base74 + (48981630191829/132130000000000000000000000 : ℝ)*base77 + (171406658549175001/1375671495000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c329024_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4557031657/10000000000 : ℝ)*x 0 + (2868075153/10000000000 : ℝ)*x 1 + (-4557030797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4557031657/10000000000 : ℝ)^95 ≤ (19432306995947/50000000000000 : ℝ)^79 := by
    have hnat : (4557031657 : ℕ)^95*50000000000000^79 ≤ 19432306995947^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557031657 10000000000 19432306995947 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2868075153/10000000000 : ℝ)^95 ≤ (11135390414519/50000000000000 : ℝ)^79 := by
    have hnat : (2868075153 : ℕ)^95*50000000000000^79 ≤ 11135390414519^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868075153 10000000000 11135390414519 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4557030797/10000000000 : ℝ)^95 ≤ (38864605171921/100000000000000 : ℝ)^79 := by
    have hnat : (4557030797 : ℕ)^95*100000000000000^79 ≤ 38864605171921^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557030797 10000000000 38864605171921 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4557031657/10000000000 : ℝ), (2868075153/10000000000 : ℝ), (-4557030797/10000000000 : ℝ)] ![(19432306995947/50000000000000 : ℝ), (11135390414519/50000000000000 : ℝ), (38864605171921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4557031657/10000000000 : ℝ)|^95 ≤ (19432306995947/50000000000000 : ℝ)^79
        have hw : |(-4557031657/10000000000 : ℝ)|=(4557031657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2868075153/10000000000 : ℝ)|^95 ≤ (11135390414519/50000000000000 : ℝ)^79
        have hw : |(2868075153/10000000000 : ℝ)|=(2868075153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4557030797/10000000000 : ℝ)|^95 ≤ (38864605171921/100000000000000 : ℝ)^79
        have hw : |(-4557030797/10000000000 : ℝ)|=(4557030797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329024_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4557031657/10000000000 : ℝ)*x 0 + (-2868075153/10000000000 : ℝ)*x 1 + (-4557030797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4557031657/10000000000 : ℝ)^95 ≤ (19432306995947/50000000000000 : ℝ)^79 := by
    have hnat : (4557031657 : ℕ)^95*50000000000000^79 ≤ 19432306995947^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557031657 10000000000 19432306995947 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2868075153/10000000000 : ℝ)^95 ≤ (11135390414519/50000000000000 : ℝ)^79 := by
    have hnat : (2868075153 : ℕ)^95*50000000000000^79 ≤ 11135390414519^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868075153 10000000000 11135390414519 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4557030797/10000000000 : ℝ)^95 ≤ (38864605171921/100000000000000 : ℝ)^79 := by
    have hnat : (4557030797 : ℕ)^95*100000000000000^79 ≤ 38864605171921^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557030797 10000000000 38864605171921 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4557031657/10000000000 : ℝ), (-2868075153/10000000000 : ℝ), (-4557030797/10000000000 : ℝ)] ![(19432306995947/50000000000000 : ℝ), (11135390414519/50000000000000 : ℝ), (38864605171921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4557031657/10000000000 : ℝ)|^95 ≤ (19432306995947/50000000000000 : ℝ)^79
        have hw : |(4557031657/10000000000 : ℝ)|=(4557031657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2868075153/10000000000 : ℝ)|^95 ≤ (11135390414519/50000000000000 : ℝ)^79
        have hw : |(-2868075153/10000000000 : ℝ)|=(2868075153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4557030797/10000000000 : ℝ)|^95 ≤ (38864605171921/100000000000000 : ℝ)^79
        have hw : |(-4557030797/10000000000 : ℝ)|=(4557030797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329024_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (155241903/500000000 : ℝ)*x 0 + (5712494601/10000000000 : ℝ)*x 1 + (1552418737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155241903/500000000 : ℝ)^95 ≤ (24499700022143/100000000000000 : ℝ)^79 := by
    have hnat : (155241903 : ℕ)^95*100000000000000^79 ≤ 24499700022143^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155241903 500000000 24499700022143 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5712494601/10000000000 : ℝ)^95 ≤ (25500302750663/50000000000000 : ℝ)^79 := by
    have hnat : (5712494601 : ℕ)^95*50000000000000^79 ≤ 25500302750663^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712494601 10000000000 25500302750663 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552418737/5000000000 : ℝ)^95 ≤ (1531230903851/6250000000000 : ℝ)^79 := by
    have hnat : (1552418737 : ℕ)^95*6250000000000^79 ≤ 1531230903851^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552418737 5000000000 1531230903851 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(155241903/500000000 : ℝ), (5712494601/10000000000 : ℝ), (1552418737/5000000000 : ℝ)] ![(24499700022143/100000000000000 : ℝ), (25500302750663/50000000000000 : ℝ), (1531230903851/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(155241903/500000000 : ℝ)|^95 ≤ (24499700022143/100000000000000 : ℝ)^79
        have hw : |(155241903/500000000 : ℝ)|=(155241903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5712494601/10000000000 : ℝ)|^95 ≤ (25500302750663/50000000000000 : ℝ)^79
        have hw : |(5712494601/10000000000 : ℝ)|=(5712494601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1552418737/5000000000 : ℝ)|^95 ≤ (1531230903851/6250000000000 : ℝ)^79
        have hw : |(1552418737/5000000000 : ℝ)|=(1552418737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329024_s0_5 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (0 : ℝ)*x 1 + (-1 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^95 ≤ (0 : ℝ)^79 := by
    have hnat : (0 : ℕ)^95*1^79 ≤ 0^79*1^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^95 ≤ (0 : ℝ)^79 := by
    have hnat : (0 : ℕ)^95*1^79 ≤ 0^79*1^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1 : ℝ)^95 ≤ (1 : ℝ)^79 := by
    have hnat : (1 : ℕ)^95*1^79 ≤ 1^79*1^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^95 ≤ (0 : ℝ)^79
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^95 ≤ (0 : ℝ)^79
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1 : ℝ)|^95 ≤ (1 : ℝ)^79
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329024_s0_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (155241903/500000000 : ℝ)*x 0 + (5712494601/10000000000 : ℝ)*x 1 + (-1552418737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155241903/500000000 : ℝ)^95 ≤ (24499700022143/100000000000000 : ℝ)^79 := by
    have hnat : (155241903 : ℕ)^95*100000000000000^79 ≤ 24499700022143^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155241903 500000000 24499700022143 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5712494601/10000000000 : ℝ)^95 ≤ (25500302750663/50000000000000 : ℝ)^79 := by
    have hnat : (5712494601 : ℕ)^95*50000000000000^79 ≤ 25500302750663^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712494601 10000000000 25500302750663 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552418737/5000000000 : ℝ)^95 ≤ (1531230903851/6250000000000 : ℝ)^79 := by
    have hnat : (1552418737 : ℕ)^95*6250000000000^79 ≤ 1531230903851^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552418737 5000000000 1531230903851 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(155241903/500000000 : ℝ), (5712494601/10000000000 : ℝ), (-1552418737/5000000000 : ℝ)] ![(24499700022143/100000000000000 : ℝ), (25500302750663/50000000000000 : ℝ), (1531230903851/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(155241903/500000000 : ℝ)|^95 ≤ (24499700022143/100000000000000 : ℝ)^79
        have hw : |(155241903/500000000 : ℝ)|=(155241903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5712494601/10000000000 : ℝ)|^95 ≤ (25500302750663/50000000000000 : ℝ)^79
        have hw : |(5712494601/10000000000 : ℝ)|=(5712494601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1552418737/5000000000 : ℝ)|^95 ≤ (1531230903851/6250000000000 : ℝ)^79
        have hw : |(-1552418737/5000000000 : ℝ)|=(1552418737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329024 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
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
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4557031657/10000000000 : ℝ)*X 0 0+(2868075153/10000000000 : ℝ)*X 0 1+(-4557030797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329024_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4557031657/10000000000 : ℝ)*X 1 0+(-2868075153/10000000000 : ℝ)*X 1 1+(-4557030797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329024_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((155241903/500000000 : ℝ)*X 2 0+(5712494601/10000000000 : ℝ)*X 2 1+(1552418737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329024_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_5 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329024_s0_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((155241903/500000000 : ℝ)*X 0 0+(5712494601/10000000000 : ℝ)*X 0 1+(-1552418737/5000000000 : ℝ)*X 0 2+(155241903/500000000 : ℝ)*X 1 0+(5712494601/10000000000 : ℝ)*X 1 1+(-1552418737/5000000000 : ℝ)*X 1 2+(155241903/500000000 : ℝ)*X 2 0+(5712494601/10000000000 : ℝ)*X 2 1+(-1552418737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329024_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-3173850626483160516968682603/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (189326291681/1000000000000 : ℝ)*(base39) + (26573/62500000000 : ℝ)*(base40) + (769657448051/1000000000000 : ℝ)*(base49) + (580331581537/1000000000000 : ℝ)*(base50) + (374239/1000000000000 : ℝ)*(base53) + (45403/1000000000000 : ℝ)*(base54) + (27708731617/62500000000 : ℝ)*(base59) + (55589/25000 : ℝ)*(major_s0_0) + (55589/25000 : ℝ)*(major_s0_1) + (2923901407189/1000000000000 : ℝ)*(major_s0_2) + (3385440294003/1000000000000 : ℝ)*(sp_s0_0) + (3385440294003/1000000000000 : ℝ)*(sp_s0_1) + (3385440622839/1000000000000 : ℝ)*(sp_s0_2) + (70034182683/100000000000 : ℝ)*(sp_s0_5) + (999999954597/1000000000000 : ℝ)*(sp_s0_6) + (3385440668241/1000000000000 : ℝ)*(f.sum) + (7127721744519827/10000000000000000000000000000 : ℝ)*base63 + (2874258697787389/10000000000000000000000000000 : ℝ)*base65 + (2127346809/10000000000000000000000 : ℝ)*base67 + (118374722519827/10000000000000000000000000000 : ℝ)*base69 + (6019832535787389/10000000000000000000000000000 : ℝ)*base71 + (7872653191/10000000000000000000000 : ℝ)*base72 + (130570673/250000000000000000000 : ℝ)*base75 + (908683971/2500000000000000000000 : ℝ)*base77 + (511940957/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1/1000000000000 : ℝ)*base90 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b009 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 23 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=23 ∨ c=24 := by omega
  rcases hc with rfl|rfl
  · exact collision_c329023 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329024 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 23 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b009 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
