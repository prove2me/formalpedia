-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b006
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:06.679187+00:00
-- url     : https://prove2.me/submissions/42fbe4f1-a954-4544-af36-eb6795410c49

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
theorem collision_support_c323015_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426518609/5000000000 : ℝ)*x 0 + (-1245237757/2000000000 : ℝ)*x 1 + (120831693/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426518609/5000000000 : ℝ)^85 ≤ (21330543199509/100000000000000 : ℝ)^69 := by
    have hnat : (1426518609 : ℕ)^85*100000000000000^69 ≤ 21330543199509^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426518609 5000000000 21330543199509 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1245237757/2000000000 : ℝ)^85 ≤ (11156698809897/20000000000000 : ℝ)^69 := by
    have hnat : (1245237757 : ℕ)^85*20000000000000^69 ≤ 11156698809897^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245237757 2000000000 11156698809897 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120831693/400000000 : ℝ)^85 ≤ (22885962747919/100000000000000 : ℝ)^69 := by
    have hnat : (120831693 : ℕ)^85*100000000000000^69 ≤ 22885962747919^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120831693 400000000 22885962747919 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426518609/5000000000 : ℝ), (-1245237757/2000000000 : ℝ), (120831693/400000000 : ℝ)] ![(21330543199509/100000000000000 : ℝ), (11156698809897/20000000000000 : ℝ), (22885962747919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426518609/5000000000 : ℝ)|^85 ≤ (21330543199509/100000000000000 : ℝ)^69
        have hw : |(-1426518609/5000000000 : ℝ)|=(1426518609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1245237757/2000000000 : ℝ)|^85 ≤ (11156698809897/20000000000000 : ℝ)^69
        have hw : |(-1245237757/2000000000 : ℝ)|=(1245237757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(120831693/400000000 : ℝ)|^85 ≤ (22885962747919/100000000000000 : ℝ)^69
        have hw : |(120831693/400000000 : ℝ)|=(120831693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3752869607/10000000000 : ℝ)*x 0 + (-4342251817/10000000000 : ℝ)*x 1 + (-4196832247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3752869607/10000000000 : ℝ)^85 ≤ (14949792159809/50000000000000 : ℝ)^69 := by
    have hnat : (3752869607 : ℕ)^85*50000000000000^69 ≤ 14949792159809^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752869607 10000000000 14949792159809 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4342251817/10000000000 : ℝ)^85 ≤ (7157096725477/20000000000000 : ℝ)^69 := by
    have hnat : (4342251817 : ℕ)^85*20000000000000^69 ≤ 7157096725477^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342251817 10000000000 7157096725477 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4196832247/10000000000 : ℝ)^85 ≤ (17157466016709/50000000000000 : ℝ)^69 := by
    have hnat : (4196832247 : ℕ)^85*50000000000000^69 ≤ 17157466016709^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196832247 10000000000 17157466016709 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3752869607/10000000000 : ℝ), (-4342251817/10000000000 : ℝ), (-4196832247/10000000000 : ℝ)] ![(14949792159809/50000000000000 : ℝ), (7157096725477/20000000000000 : ℝ), (17157466016709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3752869607/10000000000 : ℝ)|^85 ≤ (14949792159809/50000000000000 : ℝ)^69
        have hw : |(3752869607/10000000000 : ℝ)|=(3752869607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4342251817/10000000000 : ℝ)|^85 ≤ (7157096725477/20000000000000 : ℝ)^69
        have hw : |(-4342251817/10000000000 : ℝ)|=(4342251817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4196832247/10000000000 : ℝ)|^85 ≤ (17157466016709/50000000000000 : ℝ)^69
        have hw : |(-4196832247/10000000000 : ℝ)|=(4196832247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-311786047/1250000000 : ℝ)*x 0 + (-7591067037/10000000000 : ℝ)*x 1 + (1631205569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311786047/1250000000 : ℝ)^85 ≤ (361524890679/2000000000000 : ℝ)^69 := by
    have hnat : (311786047 : ℕ)^85*2000000000000^69 ≤ 361524890679^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311786047 1250000000 361524890679 2000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7591067037/10000000000 : ℝ)^85 ≤ (8901372457089/12500000000000 : ℝ)^69 := by
    have hnat : (7591067037 : ℕ)^85*12500000000000^69 ≤ 8901372457089^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7591067037 10000000000 8901372457089 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1631205569/10000000000 : ℝ)^85 ≤ (1071277580469/10000000000000 : ℝ)^69 := by
    have hnat : (1631205569 : ℕ)^85*10000000000000^69 ≤ 1071277580469^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631205569 10000000000 1071277580469 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311786047/1250000000 : ℝ), (-7591067037/10000000000 : ℝ), (1631205569/10000000000 : ℝ)] ![(361524890679/2000000000000 : ℝ), (8901372457089/12500000000000 : ℝ), (1071277580469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311786047/1250000000 : ℝ)|^85 ≤ (361524890679/2000000000000 : ℝ)^69
        have hw : |(-311786047/1250000000 : ℝ)|=(311786047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7591067037/10000000000 : ℝ)|^85 ≤ (8901372457089/12500000000000 : ℝ)^69
        have hw : |(-7591067037/10000000000 : ℝ)|=(7591067037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1631205569/10000000000 : ℝ)|^85 ≤ (1071277580469/10000000000000 : ℝ)^69
        have hw : |(1631205569/10000000000 : ℝ)|=(1631205569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4990142419/10000000000 : ℝ)*x 0 + (4391798791/10000000000 : ℝ)*x 1 + (2842997421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4990142419/10000000000 : ℝ)^85 ≤ (8494545361909/20000000000000 : ℝ)^69 := by
    have hnat : (4990142419 : ℕ)^85*20000000000000^69 ≤ 8494545361909^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990142419 10000000000 8494545361909 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4391798791/10000000000 : ℝ)^85 ≤ (18144579871957/50000000000000 : ℝ)^69 := by
    have hnat : (4391798791 : ℕ)^85*50000000000000^69 ≤ 18144579871957^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391798791 10000000000 18144579871957 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842997421/10000000000 : ℝ)^85 ≤ (265476417909/1250000000000 : ℝ)^69 := by
    have hnat : (2842997421 : ℕ)^85*1250000000000^69 ≤ 265476417909^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842997421 10000000000 265476417909 1250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4990142419/10000000000 : ℝ), (4391798791/10000000000 : ℝ), (2842997421/10000000000 : ℝ)] ![(8494545361909/20000000000000 : ℝ), (18144579871957/50000000000000 : ℝ), (265476417909/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4990142419/10000000000 : ℝ)|^85 ≤ (8494545361909/20000000000000 : ℝ)^69
        have hw : |(4990142419/10000000000 : ℝ)|=(4990142419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4391798791/10000000000 : ℝ)|^85 ≤ (18144579871957/50000000000000 : ℝ)^69
        have hw : |(4391798791/10000000000 : ℝ)|=(4391798791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842997421/10000000000 : ℝ)|^85 ≤ (265476417909/1250000000000 : ℝ)^69
        have hw : |(2842997421/10000000000 : ℝ)|=(2842997421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1205085067/2500000000 : ℝ)*x 0 + (-2762524243/5000000000 : ℝ)*x 1 + (-842613173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1205085067/2500000000 : ℝ)^85 ≤ (40699443062661/100000000000000 : ℝ)^69 := by
    have hnat : (1205085067 : ℕ)^85*100000000000000^69 ≤ 40699443062661^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205085067 2500000000 40699443062661 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762524243/5000000000 : ℝ)^85 ≤ (48149074240959/100000000000000 : ℝ)^69 := by
    have hnat : (2762524243 : ℕ)^85*100000000000000^69 ≤ 48149074240959^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762524243 5000000000 48149074240959 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842613173/5000000000 : ℝ)^85 ≤ (11151482689379/100000000000000 : ℝ)^69 := by
    have hnat : (842613173 : ℕ)^85*100000000000000^69 ≤ 11151482689379^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842613173 5000000000 11151482689379 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1205085067/2500000000 : ℝ), (-2762524243/5000000000 : ℝ), (-842613173/5000000000 : ℝ)] ![(40699443062661/100000000000000 : ℝ), (48149074240959/100000000000000 : ℝ), (11151482689379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1205085067/2500000000 : ℝ)|^85 ≤ (40699443062661/100000000000000 : ℝ)^69
        have hw : |(1205085067/2500000000 : ℝ)|=(1205085067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2762524243/5000000000 : ℝ)|^85 ≤ (48149074240959/100000000000000 : ℝ)^69
        have hw : |(-2762524243/5000000000 : ℝ)|=(2762524243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-842613173/5000000000 : ℝ)|^85 ≤ (11151482689379/100000000000000 : ℝ)^69
        have hw : |(-842613173/5000000000 : ℝ)|=(842613173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (75485547/625000000 : ℝ)*x 0 + (69279/2000000000 : ℝ)*x 1 + (2348781579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75485547/625000000 : ℝ)^85 ≤ (1849483552789/25000000000000 : ℝ)^69 := by
    have hnat : (75485547 : ℕ)^85*25000000000000^69 ≤ 1849483552789^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75485547 625000000 1849483552789 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69279/2000000000 : ℝ)^85 ≤ (320087991/100000000000000 : ℝ)^69 := by
    have hnat : (69279 : ℕ)^85*100000000000000^69 ≤ 320087991^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69279 2000000000 320087991 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2348781579/2500000000 : ℝ)^85 ≤ (2315043642107/2500000000000 : ℝ)^69 := by
    have hnat : (2348781579 : ℕ)^85*2500000000000^69 ≤ 2315043642107^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348781579 2500000000 2315043642107 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(75485547/625000000 : ℝ), (69279/2000000000 : ℝ), (2348781579/2500000000 : ℝ)] ![(1849483552789/25000000000000 : ℝ), (320087991/100000000000000 : ℝ), (2315043642107/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(75485547/625000000 : ℝ)|^85 ≤ (1849483552789/25000000000000 : ℝ)^69
        have hw : |(75485547/625000000 : ℝ)|=(75485547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69279/2000000000 : ℝ)|^85 ≤ (320087991/100000000000000 : ℝ)^69
        have hw : |(69279/2000000000 : ℝ)|=(69279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2348781579/2500000000 : ℝ)|^85 ≤ (2315043642107/2500000000000 : ℝ)^69
        have hw : |(2348781579/2500000000 : ℝ)|=(2348781579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4036257953/10000000000 : ℝ)*x 0 + (-1299237503/2500000000 : ℝ)*x 1 + (2994816723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036257953/10000000000 : ℝ)^85 ≤ (32704815642493/100000000000000 : ℝ)^69 := by
    have hnat : (4036257953 : ℕ)^85*100000000000000^69 ≤ 32704815642493^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036257953 10000000000 32704815642493 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299237503/2500000000 : ℝ)^85 ≤ (44651407919859/100000000000000 : ℝ)^69 := by
    have hnat : (1299237503 : ℕ)^85*100000000000000^69 ≤ 44651407919859^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299237503 2500000000 44651407919859 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2994816723/10000000000 : ℝ)^85 ≤ (5660944105629/25000000000000 : ℝ)^69 := by
    have hnat : (2994816723 : ℕ)^85*25000000000000^69 ≤ 5660944105629^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994816723 10000000000 5660944105629 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4036257953/10000000000 : ℝ), (-1299237503/2500000000 : ℝ), (2994816723/10000000000 : ℝ)] ![(32704815642493/100000000000000 : ℝ), (44651407919859/100000000000000 : ℝ), (5660944105629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4036257953/10000000000 : ℝ)|^85 ≤ (32704815642493/100000000000000 : ℝ)^69
        have hw : |(-4036257953/10000000000 : ℝ)|=(4036257953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1299237503/2500000000 : ℝ)|^85 ≤ (44651407919859/100000000000000 : ℝ)^69
        have hw : |(-1299237503/2500000000 : ℝ)|=(1299237503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2994816723/10000000000 : ℝ)|^85 ≤ (5660944105629/25000000000000 : ℝ)^69
        have hw : |(2994816723/10000000000 : ℝ)|=(2994816723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1445612183/2000000000 : ℝ)*x 0 + (2654315137/10000000000 : ℝ)*x 1 + (1961546827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445612183/2000000000 : ℝ)^85 ≤ (1047493251713/1562500000000 : ℝ)^69 := by
    have hnat : (1445612183 : ℕ)^85*1562500000000^69 ≤ 1047493251713^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445612183 2000000000 1047493251713 1562500000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2654315137/10000000000 : ℝ)^85 ≤ (4878836416263/25000000000000 : ℝ)^69 := by
    have hnat : (2654315137 : ℕ)^85*25000000000000^69 ≤ 4878836416263^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654315137 10000000000 4878836416263 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961546827/10000000000 : ℝ)^85 ≤ (13445086221747/100000000000000 : ℝ)^69 := by
    have hnat : (1961546827 : ℕ)^85*100000000000000^69 ≤ 13445086221747^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961546827 10000000000 13445086221747 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1445612183/2000000000 : ℝ), (2654315137/10000000000 : ℝ), (1961546827/10000000000 : ℝ)] ![(1047493251713/1562500000000 : ℝ), (4878836416263/25000000000000 : ℝ), (13445086221747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1445612183/2000000000 : ℝ)|^85 ≤ (1047493251713/1562500000000 : ℝ)^69
        have hw : |(1445612183/2000000000 : ℝ)|=(1445612183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2654315137/10000000000 : ℝ)|^85 ≤ (4878836416263/25000000000000 : ℝ)^69
        have hw : |(2654315137/10000000000 : ℝ)|=(2654315137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1961546827/10000000000 : ℝ)|^85 ≤ (13445086221747/100000000000000 : ℝ)^69
        have hw : |(1961546827/10000000000 : ℝ)|=(1961546827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (35248243/125000000 : ℝ)*x 0 + (-7057956421/10000000000 : ℝ)*x 1 + (-201210547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35248243/125000000 : ℝ)^85 ≤ (21025385797659/100000000000000 : ℝ)^69 := by
    have hnat : (35248243 : ℕ)^85*100000000000000^69 ≤ 21025385797659^69*125000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35248243 125000000 21025385797659 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7057956421/10000000000 : ℝ)^85 ≤ (65101356596949/100000000000000 : ℝ)^69 := by
    have hnat : (7057956421 : ℕ)^85*100000000000000^69 ≤ 65101356596949^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7057956421 10000000000 65101356596949 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201210547/1000000000 : ℝ)^85 ≤ (1387325758597/10000000000000 : ℝ)^69 := by
    have hnat : (201210547 : ℕ)^85*10000000000000^69 ≤ 1387325758597^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201210547 1000000000 1387325758597 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35248243/125000000 : ℝ), (-7057956421/10000000000 : ℝ), (-201210547/1000000000 : ℝ)] ![(21025385797659/100000000000000 : ℝ), (65101356596949/100000000000000 : ℝ), (1387325758597/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35248243/125000000 : ℝ)|^85 ≤ (21025385797659/100000000000000 : ℝ)^69
        have hw : |(35248243/125000000 : ℝ)|=(35248243/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7057956421/10000000000 : ℝ)|^85 ≤ (65101356596949/100000000000000 : ℝ)^69
        have hw : |(-7057956421/10000000000 : ℝ)|=(7057956421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201210547/1000000000 : ℝ)|^85 ≤ (1387325758597/10000000000000 : ℝ)^69
        have hw : |(-201210547/1000000000 : ℝ)|=(201210547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (356974599/5000000000 : ℝ)*x 0 + (-161/5000000000 : ℝ)*x 1 + (75660803/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356974599/5000000000 : ℝ)^85 ≤ (3871248357957/100000000000000 : ℝ)^69 := by
    have hnat : (356974599 : ℕ)^85*100000000000000^69 ≤ 3871248357957^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356974599 5000000000 3871248357957 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161/5000000000 : ℝ)^85 ≤ (58959/100000000000000 : ℝ)^69 := by
    have hnat : (161 : ℕ)^85*100000000000000^69 ≤ 58959^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161 5000000000 58959 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75660803/78125000 : ℝ)^85 ≤ (96128751572779/100000000000000 : ℝ)^69 := by
    have hnat : (75660803 : ℕ)^85*100000000000000^69 ≤ 96128751572779^69*78125000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75660803 78125000 96128751572779 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(356974599/5000000000 : ℝ), (-161/5000000000 : ℝ), (75660803/78125000 : ℝ)] ![(3871248357957/100000000000000 : ℝ), (58959/100000000000000 : ℝ), (96128751572779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(356974599/5000000000 : ℝ)|^85 ≤ (3871248357957/100000000000000 : ℝ)^69
        have hw : |(356974599/5000000000 : ℝ)|=(356974599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161/5000000000 : ℝ)|^85 ≤ (58959/100000000000000 : ℝ)^69
        have hw : |(-161/5000000000 : ℝ)|=(161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75660803/78125000 : ℝ)|^85 ≤ (96128751572779/100000000000000 : ℝ)^69
        have hw : |(75660803/78125000 : ℝ)|=(75660803/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1640286711/10000000000 : ℝ)*x 0 + (-3614377453/5000000000 : ℝ)*x 1 + (588688307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640286711/10000000000 : ℝ)^85 ≤ (10786292073229/100000000000000 : ℝ)^69 := by
    have hnat : (1640286711 : ℕ)^85*100000000000000^69 ≤ 10786292073229^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640286711 10000000000 10786292073229 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3614377453/5000000000 : ℝ)^85 ≤ (3352374873277/5000000000000 : ℝ)^69 := by
    have hnat : (3614377453 : ℕ)^85*5000000000000^69 ≤ 3352374873277^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3614377453 5000000000 3352374873277 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588688307/2000000000 : ℝ)^85 ≤ (2216621043733/10000000000000 : ℝ)^69 := by
    have hnat : (588688307 : ℕ)^85*10000000000000^69 ≤ 2216621043733^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588688307 2000000000 2216621043733 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1640286711/10000000000 : ℝ), (-3614377453/5000000000 : ℝ), (588688307/2000000000 : ℝ)] ![(10786292073229/100000000000000 : ℝ), (3352374873277/5000000000000 : ℝ), (2216621043733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1640286711/10000000000 : ℝ)|^85 ≤ (10786292073229/100000000000000 : ℝ)^69
        have hw : |(-1640286711/10000000000 : ℝ)|=(1640286711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3614377453/5000000000 : ℝ)|^85 ≤ (3352374873277/5000000000000 : ℝ)^69
        have hw : |(-3614377453/5000000000 : ℝ)|=(3614377453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(588688307/2000000000 : ℝ)|^85 ≤ (2216621043733/10000000000000 : ℝ)^69
        have hw : |(588688307/2000000000 : ℝ)|=(588688307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6751600667/10000000000 : ℝ)*x 0 + (1257448253/5000000000 : ℝ)*x 1 + (2718856791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6751600667/10000000000 : ℝ)^85 ≤ (12327610026959/20000000000000 : ℝ)^69 := by
    have hnat : (6751600667 : ℕ)^85*20000000000000^69 ≤ 12327610026959^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6751600667 10000000000 12327610026959 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257448253/5000000000 : ℝ)^85 ≤ (9130200063377/50000000000000 : ℝ)^69 := by
    have hnat : (1257448253 : ℕ)^85*50000000000000^69 ≤ 9130200063377^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257448253 5000000000 9130200063377 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718856791/10000000000 : ℝ)^85 ≤ (2512693714823/12500000000000 : ℝ)^69 := by
    have hnat : (2718856791 : ℕ)^85*12500000000000^69 ≤ 2512693714823^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718856791 10000000000 2512693714823 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6751600667/10000000000 : ℝ), (1257448253/5000000000 : ℝ), (2718856791/10000000000 : ℝ)] ![(12327610026959/20000000000000 : ℝ), (9130200063377/50000000000000 : ℝ), (2512693714823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6751600667/10000000000 : ℝ)|^85 ≤ (12327610026959/20000000000000 : ℝ)^69
        have hw : |(6751600667/10000000000 : ℝ)|=(6751600667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1257448253/5000000000 : ℝ)|^85 ≤ (9130200063377/50000000000000 : ℝ)^69
        have hw : |(1257448253/5000000000 : ℝ)|=(1257448253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718856791/10000000000 : ℝ)|^85 ≤ (2512693714823/12500000000000 : ℝ)^69
        have hw : |(2718856791/10000000000 : ℝ)|=(2718856791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (158298311/625000000 : ℝ)*x 0 + (-2163628713/5000000000 : ℝ)*x 1 + (-265947893/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158298311/625000000 : ℝ)^85 ≤ (4605107300541/25000000000000 : ℝ)^69 := by
    have hnat : (158298311 : ℕ)^85*25000000000000^69 ≤ 4605107300541^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158298311 625000000 4605107300541 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163628713/5000000000 : ℝ)^85 ≤ (35633318025833/100000000000000 : ℝ)^69 := by
    have hnat : (2163628713 : ℕ)^85*100000000000000^69 ≤ 35633318025833^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163628713 5000000000 35633318025833 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265947893/500000000 : ℝ)^85 ≤ (11486563188001/25000000000000 : ℝ)^69 := by
    have hnat : (265947893 : ℕ)^85*25000000000000^69 ≤ 11486563188001^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265947893 500000000 11486563188001 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(158298311/625000000 : ℝ), (-2163628713/5000000000 : ℝ), (-265947893/500000000 : ℝ)] ![(4605107300541/25000000000000 : ℝ), (35633318025833/100000000000000 : ℝ), (11486563188001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(158298311/625000000 : ℝ)|^85 ≤ (4605107300541/25000000000000 : ℝ)^69
        have hw : |(158298311/625000000 : ℝ)|=(158298311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2163628713/5000000000 : ℝ)|^85 ≤ (35633318025833/100000000000000 : ℝ)^69
        have hw : |(-2163628713/5000000000 : ℝ)|=(2163628713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265947893/500000000 : ℝ)|^85 ≤ (11486563188001/25000000000000 : ℝ)^69
        have hw : |(-265947893/500000000 : ℝ)|=(265947893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3369731837/10000000000 : ℝ)*x 0 + (-890489983/2000000000 : ℝ)*x 1 + (4452449719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3369731837/10000000000 : ℝ)^85 ≤ (13092489556717/50000000000000 : ℝ)^69 := by
    have hnat : (3369731837 : ℕ)^85*50000000000000^69 ≤ 13092489556717^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3369731837 10000000000 13092489556717 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890489983/2000000000 : ℝ)^85 ≤ (36907511429951/100000000000000 : ℝ)^69 := by
    have hnat : (890489983 : ℕ)^85*100000000000000^69 ≤ 36907511429951^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890489983 2000000000 36907511429951 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4452449719/10000000000 : ℝ)^85 ≤ (7381501885703/20000000000000 : ℝ)^69 := by
    have hnat : (4452449719 : ℕ)^85*20000000000000^69 ≤ 7381501885703^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452449719 10000000000 7381501885703 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3369731837/10000000000 : ℝ), (-890489983/2000000000 : ℝ), (4452449719/10000000000 : ℝ)] ![(13092489556717/50000000000000 : ℝ), (36907511429951/100000000000000 : ℝ), (7381501885703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3369731837/10000000000 : ℝ)|^85 ≤ (13092489556717/50000000000000 : ℝ)^69
        have hw : |(-3369731837/10000000000 : ℝ)|=(3369731837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890489983/2000000000 : ℝ)|^85 ≤ (36907511429951/100000000000000 : ℝ)^69
        have hw : |(-890489983/2000000000 : ℝ)|=(890489983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4452449719/10000000000 : ℝ)|^85 ≤ (7381501885703/20000000000000 : ℝ)^69
        have hw : |(4452449719/10000000000 : ℝ)|=(4452449719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5152669017/10000000000 : ℝ)*x 0 + (3548683183/10000000000 : ℝ)*x 1 + (3548683027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152669017/10000000000 : ℝ)^85 ≤ (44183194739591/100000000000000 : ℝ)^69 := by
    have hnat : (5152669017 : ℕ)^85*100000000000000^69 ≤ 44183194739591^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152669017 10000000000 44183194739591 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3548683183/10000000000 : ℝ)^85 ≤ (697710084523/2500000000000 : ℝ)^69 := by
    have hnat : (3548683183 : ℕ)^85*2500000000000^69 ≤ 697710084523^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548683183 10000000000 697710084523 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3548683027/10000000000 : ℝ)^85 ≤ (1395420093479/5000000000000 : ℝ)^69 := by
    have hnat : (3548683027 : ℕ)^85*5000000000000^69 ≤ 1395420093479^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548683027 10000000000 1395420093479 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152669017/10000000000 : ℝ), (3548683183/10000000000 : ℝ), (3548683027/10000000000 : ℝ)] ![(44183194739591/100000000000000 : ℝ), (697710084523/2500000000000 : ℝ), (1395420093479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152669017/10000000000 : ℝ)|^85 ≤ (44183194739591/100000000000000 : ℝ)^69
        have hw : |(5152669017/10000000000 : ℝ)|=(5152669017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3548683183/10000000000 : ℝ)|^85 ≤ (697710084523/2500000000000 : ℝ)^69
        have hw : |(3548683183/10000000000 : ℝ)|=(3548683183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3548683027/10000000000 : ℝ)|^85 ≤ (1395420093479/5000000000000 : ℝ)^69
        have hw : |(3548683027/10000000000 : ℝ)|=(3548683027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3369731837/10000000000 : ℝ)*x 0 + (-890489983/2000000000 : ℝ)*x 1 + (-4452449719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3369731837/10000000000 : ℝ)^85 ≤ (13092489556717/50000000000000 : ℝ)^69 := by
    have hnat : (3369731837 : ℕ)^85*50000000000000^69 ≤ 13092489556717^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3369731837 10000000000 13092489556717 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890489983/2000000000 : ℝ)^85 ≤ (36907511429951/100000000000000 : ℝ)^69 := by
    have hnat : (890489983 : ℕ)^85*100000000000000^69 ≤ 36907511429951^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890489983 2000000000 36907511429951 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4452449719/10000000000 : ℝ)^85 ≤ (7381501885703/20000000000000 : ℝ)^69 := by
    have hnat : (4452449719 : ℕ)^85*20000000000000^69 ≤ 7381501885703^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452449719 10000000000 7381501885703 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3369731837/10000000000 : ℝ), (-890489983/2000000000 : ℝ), (-4452449719/10000000000 : ℝ)] ![(13092489556717/50000000000000 : ℝ), (36907511429951/100000000000000 : ℝ), (7381501885703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3369731837/10000000000 : ℝ)|^85 ≤ (13092489556717/50000000000000 : ℝ)^69
        have hw : |(3369731837/10000000000 : ℝ)|=(3369731837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890489983/2000000000 : ℝ)|^85 ≤ (36907511429951/100000000000000 : ℝ)^69
        have hw : |(-890489983/2000000000 : ℝ)|=(890489983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4452449719/10000000000 : ℝ)|^85 ≤ (7381501885703/20000000000000 : ℝ)^69
        have hw : |(-4452449719/10000000000 : ℝ)|=(4452449719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323015_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5152669017/10000000000 : ℝ)*x 0 + (-3548683183/10000000000 : ℝ)*x 1 + (3548683027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152669017/10000000000 : ℝ)^85 ≤ (44183194739591/100000000000000 : ℝ)^69 := by
    have hnat : (5152669017 : ℕ)^85*100000000000000^69 ≤ 44183194739591^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152669017 10000000000 44183194739591 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3548683183/10000000000 : ℝ)^85 ≤ (697710084523/2500000000000 : ℝ)^69 := by
    have hnat : (3548683183 : ℕ)^85*2500000000000^69 ≤ 697710084523^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548683183 10000000000 697710084523 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3548683027/10000000000 : ℝ)^85 ≤ (1395420093479/5000000000000 : ℝ)^69 := by
    have hnat : (3548683027 : ℕ)^85*5000000000000^69 ≤ 1395420093479^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548683027 10000000000 1395420093479 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152669017/10000000000 : ℝ), (-3548683183/10000000000 : ℝ), (3548683027/10000000000 : ℝ)] ![(44183194739591/100000000000000 : ℝ), (697710084523/2500000000000 : ℝ), (1395420093479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152669017/10000000000 : ℝ)|^85 ≤ (44183194739591/100000000000000 : ℝ)^69
        have hw : |(5152669017/10000000000 : ℝ)|=(5152669017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3548683183/10000000000 : ℝ)|^85 ≤ (697710084523/2500000000000 : ℝ)^69
        have hw : |(-3548683183/10000000000 : ℝ)|=(3548683183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3548683027/10000000000 : ℝ)|^85 ≤ (1395420093479/5000000000000 : ℝ)^69
        have hw : |(3548683027/10000000000 : ℝ)|=(3548683027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323015 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
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
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1426518609/5000000000 : ℝ)*X 0 0+(-1245237757/2000000000 : ℝ)*X 0 1+(120831693/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3752869607/10000000000 : ℝ)*X 2 0+(-4342251817/10000000000 : ℝ)*X 2 1+(-4196832247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-311786047/1250000000 : ℝ)*X 0 0+(-7591067037/10000000000 : ℝ)*X 0 1+(1631205569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4990142419/10000000000 : ℝ)*X 1 0+(4391798791/10000000000 : ℝ)*X 1 1+(2842997421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1205085067/2500000000 : ℝ)*X 2 0+(-2762524243/5000000000 : ℝ)*X 2 1+(-842613173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((75485547/625000000 : ℝ)*X 0 0+(69279/2000000000 : ℝ)*X 0 1+(2348781579/2500000000 : ℝ)*X 0 2+(75485547/625000000 : ℝ)*X 1 0+(69279/2000000000 : ℝ)*X 1 1+(2348781579/2500000000 : ℝ)*X 1 2+(75485547/625000000 : ℝ)*X 2 0+(69279/2000000000 : ℝ)*X 2 1+(2348781579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4036257953/10000000000 : ℝ)*X 0 0+(-1299237503/2500000000 : ℝ)*X 0 1+(2994816723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1445612183/2000000000 : ℝ)*X 1 0+(2654315137/10000000000 : ℝ)*X 1 1+(1961546827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((35248243/125000000 : ℝ)*X 2 0+(-7057956421/10000000000 : ℝ)*X 2 1+(-201210547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((356974599/5000000000 : ℝ)*X 0 0+(-161/5000000000 : ℝ)*X 0 1+(75660803/78125000 : ℝ)*X 0 2+(356974599/5000000000 : ℝ)*X 1 0+(-161/5000000000 : ℝ)*X 1 1+(75660803/78125000 : ℝ)*X 1 2+(356974599/5000000000 : ℝ)*X 2 0+(-161/5000000000 : ℝ)*X 2 1+(75660803/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1640286711/10000000000 : ℝ)*X 0 0+(-3614377453/5000000000 : ℝ)*X 0 1+(588688307/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6751600667/10000000000 : ℝ)*X 1 0+(1257448253/5000000000 : ℝ)*X 1 1+(2718856791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((158298311/625000000 : ℝ)*X 2 0+(-2163628713/5000000000 : ℝ)*X 2 1+(-265947893/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((7711/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7711/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1017780407712066203181/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62749331479/125000000000 : ℝ)*(base3) + (415383784467/500000000000 : ℝ)*(base7) + (80643/40000000000 : ℝ)*(base40) + (461931510809/1000000000000 : ℝ)*(base50) + (48724890151/40000000000 : ℝ)*(base54) + (83188284903/40000000000 : ℝ)*(major_s0_0) + (83188284903/40000000000 : ℝ)*(major_s0_1) + (538490543/625000000 : ℝ)*(major_s0_2) + (1778431/1000000000000 : ℝ)*(sp_s0_0) + (2634219530157/1000000000000 : ℝ)*(sp_s0_7) + (3136215960419/1000000000000 : ℝ)*(sp_s0_8) + (44252909837/31250000000 : ℝ)*(sp_s0_9) + (17371082801/100000000000 : ℝ)*(sp_s0_13) + (1485007/250000000000 : ℝ)*(sp_s0_16) + (531530082341/500000000000 : ℝ)*(f.failure) + (2634221308587/1000000000000 : ℝ)*(f.sum) + (2476880459027/80000000000000000000000000 : ℝ)*base63 + (722956547529/6250000000000000000000000 : ℝ)*base65 + (103265021767641/400000000000000000000000000 : ℝ)*base66 + (22716272179/78125000000000000000000 : ℝ)*base69 + (56225289423201/400000000000000000000000000 : ℝ)*base71 + (58380741407641/400000000000000000000000000 : ℝ)*base72 + (29523869723731/80000000000000000000000000 : ℝ)*base75 + (33979206443731/80000000000000000000000000 : ℝ)*base76 + (109566293767641/200000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (25403/25000000000000000 : ℝ)*base86 + (25403/25000000000000000 : ℝ)*base88 + (25403/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-48507/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-48507/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6105957005940984308583/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (354071909679/1000000000000 : ℝ)*(base7) + (182845773439/500000000000 : ℝ)*(base33) + (340127315857/1000000000000 : ℝ)*(base40) + (670827/500000000000 : ℝ)*(base50) + (1108398072617/1000000000000 : ℝ)*(base54) + (54129397697/31250000000 : ℝ)*(major_s0_0) + (1048916136591/500000000000 : ℝ)*(major_s0_1) + (494717100283/500000000000 : ℝ)*(major_s0_2) + (9273847/250000000000 : ℝ)*(sp_s0_9) + (75324361/1000000000000 : ℝ)*(sp_s0_13) + (2926378345759/1000000000000 : ℝ)*(sp_s0_14) + (2560686798881/1000000000000 : ℝ)*(sp_s0_15) + (1452251630877/1000000000000 : ℝ)*(sp_s0_16) + (317923503849/1000000000000 : ℝ)*(sp_s0_20) + (268081247787/250000000000 : ℝ)*(f.failure) + (2926378345759/1000000000000 : ℝ)*(f.sum) + (6976256476271/250000000000000000000000000 : ℝ)*base62 + (1518606505817499/5000000000000000000000000000 : ℝ)*base65 + (2381203427931823/5000000000000000000000000000 : ℝ)*base67 + (258487966035991/1000000000000000000000000000 : ℝ)*base68 + (511765506479979/5000000000000000000000000000 : ℝ)*base71 + (190794178006691/312500000000000000000000000 : ℝ)*base73 + (692462147869093/1000000000000000000000000000 : ℝ)*base74 + (33823021089531/62500000000000000000000000 : ℝ)*base77 + (632629013038879/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (5979/12500000000000000 : ℝ)*base87 + (5979/12500000000000000 : ℝ)*base89 + (6521/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55293/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(55293/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (147284692683716978607/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (87344182413/31250000000 : ℝ)*(base3) + (1261834745009/1000000000000 : ℝ)*(base7) + (29436398459/31250000000 : ℝ)*(base40) + (1617361033999/1000000000000 : ℝ)*(base50) + (93731862039/31250000000 : ℝ)*(major_s0_0) + (93731862039/31250000000 : ℝ)*(major_s0_1) + (93731862039/31250000000 : ℝ)*(major_s0_2) + (9649607/1000000000000 : ℝ)*(sp_s0_2) + (528119/500000000000 : ℝ)*(sp_s0_7) + (3655311/1000000000000 : ℝ)*(sp_s0_15) + (2100541/1000000000000 : ℝ)*(sp_s0_16) + (3763736951613/1000000000000 : ℝ)*(sp_s0_21) + (1639687047439/250000000000 : ℝ)*(sp_s0_22) + (3763726257703/1000000000000 : ℝ)*(sp_s0_23) + (1533179092207/1000000000000 : ℝ)*(f.failure) + (3763738007851/1000000000000 : ℝ)*(f.sum) + (2619604331/10000000000000000000000 : ℝ)*base63 + (92945631270567/312500000000000000000000000 : ℝ)*base65 + (7926082489317/312500000000000000000000000 : ℝ)*base67 + (6338785131853/62500000000000000000000000 : ℝ)*base68 + (58547405163099/156250000000000000000000000 : ℝ)*base70 + (87496525739317/312500000000000000000000000 : ℝ)*base73 + (1107605080647/62500000000000000000000000 : ℝ)*base74 + (12041916538103/62500000000000000000000000 : ℝ)*base76 + (52528686033721/78125000000000000000000000 : ℝ)*base79 + (12119/50000000000000000 : ℝ)*base87 + (12119/50000000000000000 : ℝ)*base89 + (12119/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (7711/12500 : ℝ) ^ (83/16 : ℝ) ≤ (509971724637939141/6250000000000000000 : ℝ) := by
    have hpowers : (7711/12500 : ℝ)^83 ≤ (509971724637939141/6250000000000000000 : ℝ)^16 := by
      have hnat : (7711 : ℕ)^83*6250000000000000000^16 ≤ 509971724637939141^16*12500^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7711 12500 509971724637939141 6250000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7711/12500 : ℝ)) (X := (509971724637939141/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (6759971724637939141/6250000000000000000 : ℝ) ≤ (10152353245735813/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (6759971724637939141/6250000000000000000 : ℝ)^16 ≤ (10152353245735813/10000000000000000 : ℝ)^83 := by
      have hnat : (6759971724637939141 : ℕ)^16*10000000000000000^83 ≤ 10152353245735813^83*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6759971724637939141 6250000000000000000 10152353245735813 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10152353245735813/10000000000000000 : ℝ)) (X := (6759971724637939141/6250000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3634971724637939141/3125000000000000000 : ℝ) ≤ (10295693787883579/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3634971724637939141/3125000000000000000 : ℝ)^16 ≤ (10295693787883579/10000000000000000 : ℝ)^83 := by
      have hnat : (3634971724637939141 : ℕ)^16*10000000000000000^83 ≤ 10295693787883579^83*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3634971724637939141 3125000000000000000 10295693787883579 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10295693787883579/10000000000000000 : ℝ)) (X := (3634971724637939141/3125000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(152353245735813/6168800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(71670271073883/3084400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (7711/12500 : ℝ)) (alpha := (152353245735813/6168800000000000 : ℝ)) (beta := (71670271073883/3084400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7711/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(152353245735813/6168800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(71670271073883/3084400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (48507/100000 : ℝ) ^ (83/16 : ℝ) ≤ (2344824843068584151/100000000000000000000 : ℝ) := by
    have hpowers : (48507/100000 : ℝ)^83 ≤ (2344824843068584151/100000000000000000000 : ℝ)^16 := by
      have hnat : (48507 : ℕ)^83*100000000000000000000^16 ≤ 2344824843068584151^16*100000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48507 100000 2344824843068584151 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48507/100000 : ℝ)) (X := (2344824843068584151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (102344824843068584151/100000000000000000000 : ℝ) ≤ (10044779598962497/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (102344824843068584151/100000000000000000000 : ℝ)^16 ≤ (10044779598962497/10000000000000000 : ℝ)^83 := by
      have hnat : (102344824843068584151 : ℕ)^16*10000000000000000^83 ≤ 10044779598962497^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102344824843068584151 100000000000000000000 10044779598962497 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10044779598962497/10000000000000000 : ℝ)) (X := (102344824843068584151/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (52344824843068584151/50000000000000000000 : ℝ) ≤ (2522184633921271/2500000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (52344824843068584151/50000000000000000000 : ℝ)^16 ≤ (2522184633921271/2500000000000000 : ℝ)^83 := by
      have hnat : (52344824843068584151 : ℕ)^16*2500000000000000^83 ≤ 2522184633921271^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52344824843068584151 50000000000000000000 2522184633921271 2500000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522184633921271/2500000000000000 : ℝ)) (X := (52344824843068584151/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(14926532987499/1616900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(14652978907529/1616900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (48507/100000 : ℝ)) (alpha := (14926532987499/1616900000000000 : ℝ)) (beta := (14652978907529/1616900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (48507/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(14926532987499/1616900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(14652978907529/1616900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (55293/100000 : ℝ) ^ (83/16 : ℝ) ≤ (4624890162493788823/100000000000000000000 : ℝ) := by
    have hpowers : (55293/100000 : ℝ)^83 ≤ (4624890162493788823/100000000000000000000 : ℝ)^16 := by
      have hnat : (55293 : ℕ)^83*100000000000000000000^16 ≤ 4624890162493788823^16*100000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55293 100000 4624890162493788823 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55293/100000 : ℝ)) (X := (4624890162493788823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (104624890162493788823/100000000000000000000 : ℝ) ≤ (5043767599560369/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (104624890162493788823/100000000000000000000 : ℝ)^16 ≤ (5043767599560369/5000000000000000 : ℝ)^83 := by
      have hnat : (104624890162493788823 : ℕ)^16*5000000000000000^83 ≤ 5043767599560369^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104624890162493788823 100000000000000000000 5043767599560369 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043767599560369/5000000000000000 : ℝ)) (X := (104624890162493788823/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (54624890162493788823/50000000000000000000 : ℝ) ≤ (10172000559670993/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (54624890162493788823/50000000000000000000 : ℝ)^16 ≤ (10172000559670993/10000000000000000 : ℝ)^83 := by
      have hnat : (54624890162493788823 : ℕ)^16*10000000000000000^83 ≤ 10172000559670993^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54624890162493788823 50000000000000000000 10172000559670993 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10172000559670993/10000000000000000 : ℝ)) (X := (54624890162493788823/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(43767599560369/2764650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16893072110051/1105860000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (55293/100000 : ℝ)) (alpha := (43767599560369/2764650000000000 : ℝ)) (beta := (16893072110051/1105860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (55293/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(43767599560369/2764650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16893072110051/1105860000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3369731837/10000000000 : ℝ)*X 0 0+(-890489983/2000000000 : ℝ)*X 0 1+(4452449719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5152669017/10000000000 : ℝ)*X 1 0+(3548683183/10000000000 : ℝ)*X 1 1+(3548683027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3369731837/10000000000 : ℝ)*X 2 0+(-890489983/2000000000 : ℝ)*X 2 1+(-4452449719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5152669017/10000000000 : ℝ)*X 0 0+(-3548683183/10000000000 : ℝ)*X 0 1+(3548683027/10000000000 : ℝ)*X 0 2+(5152669017/10000000000 : ℝ)*X 1 0+(-3548683183/10000000000 : ℝ)*X 1 1+(3548683027/10000000000 : ℝ)*X 1 2+(5152669017/10000000000 : ℝ)*X 2 0+(-3548683183/10000000000 : ℝ)*X 2 1+(3548683027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323015_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-5342859627204117776971808492331/623395795000000000000000000000 : ℝ) := by norm_num
    linear_combination (5441/250000000000 : ℝ)*(base1) + (991826584633/1000000000000 : ℝ)*(base3) + (105483/500000000000 : ℝ)*(base10) + (633121510607/1000000000000 : ℝ)*(base40) + (34027137637/125000000000 : ℝ)*(base49) + (971384079501/1000000000000 : ℝ)*(base50) + (191561/1000000000000 : ℝ)*(base54) + (651552819337/1000000000000 : ℝ)*(base59) + (97817/50000 : ℝ)*(major_s1_0) + (97817/50000 : ℝ)*(major_s1_1) + (1956339808439/1000000000000 : ℝ)*(major_s1_2) + (1428428861249/500000000000 : ℝ)*(sp_s1_0) + (962171124083/250000000000 : ℝ)*(sp_s1_1) + (1428428860069/500000000000 : ℝ)*(sp_s1_2) + (4086601021/500000000000 : ℝ)*(sp_s1_6) + (2856857911699/1000000000000 : ℝ)*(f.sum) + (10221971900532850001/44701625850000000000000000000000 : ℝ)*base62 + (143808599846201/221172000000000000000000000 : ℝ)*base65 + (25201515295031/40422500000000000000000000 : ℝ)*base66 + (320029347909521/2764650000000000000000000000 : ℝ)*base69 + (2007988076029335641/8527286460000000000000000000000 : ℝ)*base70 + (6223508933161/38555000000000000000000000 : ℝ)*base73 + (1747681730559/8084500000000000000000000 : ℝ)*base74 + (11780625365321/19277500000000000000000000 : ℝ)*base76 + (1523900171458249/155848948750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c323016_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2320355619/5000000000 : ℝ)*x 0 + (2891594649/10000000000 : ℝ)*x 1 + (-4702235937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2320355619/5000000000 : ℝ)^85 ≤ (38839248429997/100000000000000 : ℝ)^69 := by
    have hnat : (2320355619 : ℕ)^85*100000000000000^69 ≤ 38839248429997^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320355619 5000000000 38839248429997 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2891594649/10000000000 : ℝ)^85 ≤ (10843107744293/50000000000000 : ℝ)^69 := by
    have hnat : (2891594649 : ℕ)^85*50000000000000^69 ≤ 10843107744293^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891594649 10000000000 10843107744293 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4702235937/10000000000 : ℝ)^85 ≤ (9868634016083/25000000000000 : ℝ)^69 := by
    have hnat : (4702235937 : ℕ)^85*25000000000000^69 ≤ 9868634016083^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702235937 10000000000 9868634016083 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2320355619/5000000000 : ℝ), (2891594649/10000000000 : ℝ), (-4702235937/10000000000 : ℝ)] ![(38839248429997/100000000000000 : ℝ), (10843107744293/50000000000000 : ℝ), (9868634016083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2320355619/5000000000 : ℝ)|^85 ≤ (38839248429997/100000000000000 : ℝ)^69
        have hw : |(-2320355619/5000000000 : ℝ)|=(2320355619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2891594649/10000000000 : ℝ)|^85 ≤ (10843107744293/50000000000000 : ℝ)^69
        have hw : |(2891594649/10000000000 : ℝ)|=(2891594649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4702235937/10000000000 : ℝ)|^85 ≤ (9868634016083/25000000000000 : ℝ)^69
        have hw : |(-4702235937/10000000000 : ℝ)|=(4702235937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323016_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4733626457/10000000000 : ℝ)*x 0 + (-2949489471/10000000000 : ℝ)*x 1 + (-4557024789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4733626457/10000000000 : ℝ)^85 ≤ (39799411144889/100000000000000 : ℝ)^69 := by
    have hnat : (4733626457 : ℕ)^85*100000000000000^69 ≤ 39799411144889^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4733626457 10000000000 39799411144889 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2949489471/10000000000 : ℝ)^85 ≤ (22222330281203/100000000000000 : ℝ)^69 := by
    have hnat : (2949489471 : ℕ)^85*100000000000000^69 ≤ 22222330281203^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949489471 10000000000 22222330281203 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4557024789/10000000000 : ℝ)^85 ≤ (11868205801/31250000000 : ℝ)^69 := by
    have hnat : (4557024789 : ℕ)^85*31250000000^69 ≤ 11868205801^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557024789 10000000000 11868205801 31250000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4733626457/10000000000 : ℝ), (-2949489471/10000000000 : ℝ), (-4557024789/10000000000 : ℝ)] ![(39799411144889/100000000000000 : ℝ), (22222330281203/100000000000000 : ℝ), (11868205801/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4733626457/10000000000 : ℝ)|^85 ≤ (39799411144889/100000000000000 : ℝ)^69
        have hw : |(4733626457/10000000000 : ℝ)|=(4733626457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2949489471/10000000000 : ℝ)|^85 ≤ (22222330281203/100000000000000 : ℝ)^69
        have hw : |(-2949489471/10000000000 : ℝ)|=(2949489471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4557024789/10000000000 : ℝ)|^85 ≤ (11868205801/31250000000 : ℝ)^69
        have hw : |(-4557024789/10000000000 : ℝ)|=(4557024789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323016_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1583615193/5000000000 : ℝ)*x 0 + (5796340183/10000000000 : ℝ)*x 1 + (320972581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583615193/5000000000 : ℝ)^85 ≤ (12130123761417/50000000000000 : ℝ)^69 := by
    have hnat : (1583615193 : ℕ)^85*50000000000000^69 ≤ 12130123761417^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583615193 5000000000 12130123761417 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5796340183/10000000000 : ℝ)^85 ≤ (51077898798599/100000000000000 : ℝ)^69 := by
    have hnat : (5796340183 : ℕ)^85*100000000000000^69 ≤ 51077898798599^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5796340183 10000000000 51077898798599 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320972581/1000000000 : ℝ)^85 ≤ (3082731707679/12500000000000 : ℝ)^69 := by
    have hnat : (320972581 : ℕ)^85*12500000000000^69 ≤ 3082731707679^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320972581 1000000000 3082731707679 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1583615193/5000000000 : ℝ), (5796340183/10000000000 : ℝ), (320972581/1000000000 : ℝ)] ![(12130123761417/50000000000000 : ℝ), (51077898798599/100000000000000 : ℝ), (3082731707679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1583615193/5000000000 : ℝ)|^85 ≤ (12130123761417/50000000000000 : ℝ)^69
        have hw : |(1583615193/5000000000 : ℝ)|=(1583615193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5796340183/10000000000 : ℝ)|^85 ≤ (51077898798599/100000000000000 : ℝ)^69
        have hw : |(5796340183/10000000000 : ℝ)|=(5796340183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320972581/1000000000 : ℝ)|^85 ≤ (3082731707679/12500000000000 : ℝ)^69
        have hw : |(320972581/1000000000 : ℝ)|=(320972581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323016_s0_5 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (0 : ℝ)*x 1 + (-1 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^85 ≤ (0 : ℝ)^69 := by
    have hnat : (0 : ℕ)^85*1^69 ≤ 0^69*1^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^85 ≤ (0 : ℝ)^69 := by
    have hnat : (0 : ℕ)^85*1^69 ≤ 0^69*1^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1 : ℝ)^85 ≤ (1 : ℝ)^69 := by
    have hnat : (1 : ℕ)^85*1^69 ≤ 1^69*1^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^85 ≤ (0 : ℝ)^69
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^85 ≤ (0 : ℝ)^69
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1 : ℝ)|^85 ≤ (1 : ℝ)^69
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323016_s0_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3126547907/10000000000 : ℝ)*x 0 + (5721887283/10000000000 : ℝ)*x 1 + (-416865393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3126547907/10000000000 : ℝ)^85 ≤ (23876943464917/100000000000000 : ℝ)^69 := by
    have hnat : (3126547907 : ℕ)^85*100000000000000^69 ≤ 23876943464917^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126547907 10000000000 23876943464917 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5721887283/10000000000 : ℝ)^85 ≤ (50270884533223/100000000000000 : ℝ)^69 := by
    have hnat : (5721887283 : ℕ)^85*100000000000000^69 ≤ 50270884533223^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5721887283 10000000000 50270884533223 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416865393/1250000000 : ℝ)^85 ≤ (25852171992481/100000000000000 : ℝ)^69 := by
    have hnat : (416865393 : ℕ)^85*100000000000000^69 ≤ 25852171992481^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416865393 1250000000 25852171992481 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3126547907/10000000000 : ℝ), (5721887283/10000000000 : ℝ), (-416865393/1250000000 : ℝ)] ![(23876943464917/100000000000000 : ℝ), (50270884533223/100000000000000 : ℝ), (25852171992481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3126547907/10000000000 : ℝ)|^85 ≤ (23876943464917/100000000000000 : ℝ)^69
        have hw : |(3126547907/10000000000 : ℝ)|=(3126547907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5721887283/10000000000 : ℝ)|^85 ≤ (50270884533223/100000000000000 : ℝ)^69
        have hw : |(5721887283/10000000000 : ℝ)|=(5721887283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416865393/1250000000 : ℝ)|^85 ≤ (25852171992481/100000000000000 : ℝ)^69
        have hw : |(-416865393/1250000000 : ℝ)|=(416865393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323016 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]]) : False := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2320355619/5000000000 : ℝ)*X 0 0+(2891594649/10000000000 : ℝ)*X 0 1+(-4702235937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323016_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4733626457/10000000000 : ℝ)*X 1 0+(-2949489471/10000000000 : ℝ)*X 1 1+(-4557024789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323016_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1583615193/5000000000 : ℝ)*X 2 0+(5796340183/10000000000 : ℝ)*X 2 1+(320972581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323016_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_5 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323016_s0_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3126547907/10000000000 : ℝ)*X 0 0+(5721887283/10000000000 : ℝ)*X 0 1+(-416865393/1250000000 : ℝ)*X 0 2+(3126547907/10000000000 : ℝ)*X 1 0+(5721887283/10000000000 : ℝ)*X 1 1+(-416865393/1250000000 : ℝ)*X 1 2+(3126547907/10000000000 : ℝ)*X 2 0+(5721887283/10000000000 : ℝ)*X 2 1+(-416865393/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323016_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-10764275406220676916363/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (1341097/500000000000 : ℝ)*(base8) + (636859/1000000000000 : ℝ)*(base11) + (122503/250000000000 : ℝ)*(base15) + (66491799967/500000000000 : ℝ)*(base39) + (353871/1000000000000 : ℝ)*(base40) + (227433854399/500000000000 : ℝ)*(base50) + (73787971669/200000000000 : ℝ)*(base59) + (97817/50000 : ℝ)*(major_s0_0) + (97817/50000 : ℝ)*(major_s0_1) + (1992977729613/1000000000000 : ℝ)*(major_s0_2) + (717617530651/250000000000 : ℝ)*(sp_s0_0) + (574094590329/200000000000 : ℝ)*(sp_s0_1) + (2870473441657/1000000000000 : ℝ)*(sp_s0_2) + (36637729613/1000000000000 : ℝ)*(sp_s0_5) + (1 : ℝ)*(sp_s0_6) + (2870473441657/1000000000000 : ℝ)*(f.sum) + (177943896236401/2000000000000000000000000000 : ℝ)*base63 + (657508648446989/10000000000000000000000000000 : ℝ)*base64 + (216727009/1250000000000000000000 : ℝ)*base66 + (418069387163599/2000000000000000000000000000 : ℝ)*base68 + (956696242553011/10000000000000000000000000000 : ℝ)*base71 + (212878557/400000000000000000000 : ℝ)*base73 + (171409351/5000000000000000000000 : ℝ)*base74 + (2480974131/10000000000000000000000 : ℝ)*base76 + (399793283/1000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p023_b006 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 15 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=15 ∨ c=16 := by omega
  rcases hc with rfl|rfl
  · exact collision_c323015 p hpa (by linarith only [hpb]) X hX
  · exact collision_c323016 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 15 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b006 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
