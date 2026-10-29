-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_positive87
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:46:13.631358+00:00
-- url     : https://prove2.me/submissions/4c2c9914-602a-430d-a14f-27faa9534393

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
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_chart_nonnegative {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true)) :
    ∀ i h, 0 ≤ pair X i h := by
  intro i h
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hh.1.trans hh.2.1).trans hh.2.2
  · exact hh.1.trans hh.2.1
  · exact hh.1
theorem positive_chart_tailratio {p k A d rho : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i)
    (hbig : ∀ i, pair X i (orders i 1) ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i := by
  intro i h hih
  rw [abs_of_nonneg (positive_chart_nonnegative hX i h)]
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hih (hm i).symm).elim
  · exact hbig i
  · exact hh.2.1.trans (hbig i)
end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c322087_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-194299833/10000000000 : ℝ)*x 0 + (5510516377/10000000000 : ℝ)*x 1 + (5847857497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194299833/10000000000 : ℝ)^83 ≤ (379070012193/50000000000000 : ℝ)^67 := by
    have hnat : (194299833 : ℕ)^83*50000000000000^67 ≤ 379070012193^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194299833 10000000000 379070012193 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510516377/10000000000 : ℝ)^83 ≤ (9559110206643/20000000000000 : ℝ)^67 := by
    have hnat : (5510516377 : ℕ)^83*20000000000000^67 ≤ 9559110206643^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510516377 10000000000 9559110206643 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5847857497/10000000000 : ℝ)^83 ≤ (51446308924749/100000000000000 : ℝ)^67 := by
    have hnat : (5847857497 : ℕ)^83*100000000000000^67 ≤ 51446308924749^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847857497 10000000000 51446308924749 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194299833/10000000000 : ℝ), (5510516377/10000000000 : ℝ), (5847857497/10000000000 : ℝ)] ![(379070012193/50000000000000 : ℝ), (9559110206643/20000000000000 : ℝ), (51446308924749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194299833/10000000000 : ℝ)|^83 ≤ (379070012193/50000000000000 : ℝ)^67
        have hw : |(-194299833/10000000000 : ℝ)|=(194299833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510516377/10000000000 : ℝ)|^83 ≤ (9559110206643/20000000000000 : ℝ)^67
        have hw : |(5510516377/10000000000 : ℝ)|=(5510516377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5847857497/10000000000 : ℝ)|^83 ≤ (51446308924749/100000000000000 : ℝ)^67
        have hw : |(5847857497/10000000000 : ℝ)|=(5847857497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5847857497/10000000000 : ℝ)*x 0 + (-194299833/10000000000 : ℝ)*x 1 + (5510516377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5847857497/10000000000 : ℝ)^83 ≤ (51446308924749/100000000000000 : ℝ)^67 := by
    have hnat : (5847857497 : ℕ)^83*100000000000000^67 ≤ 51446308924749^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847857497 10000000000 51446308924749 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194299833/10000000000 : ℝ)^83 ≤ (379070012193/50000000000000 : ℝ)^67 := by
    have hnat : (194299833 : ℕ)^83*50000000000000^67 ≤ 379070012193^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194299833 10000000000 379070012193 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510516377/10000000000 : ℝ)^83 ≤ (9559110206643/20000000000000 : ℝ)^67 := by
    have hnat : (5510516377 : ℕ)^83*20000000000000^67 ≤ 9559110206643^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510516377 10000000000 9559110206643 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5847857497/10000000000 : ℝ), (-194299833/10000000000 : ℝ), (5510516377/10000000000 : ℝ)] ![(51446308924749/100000000000000 : ℝ), (379070012193/50000000000000 : ℝ), (9559110206643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5847857497/10000000000 : ℝ)|^83 ≤ (51446308924749/100000000000000 : ℝ)^67
        have hw : |(5847857497/10000000000 : ℝ)|=(5847857497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-194299833/10000000000 : ℝ)|^83 ≤ (379070012193/50000000000000 : ℝ)^67
        have hw : |(-194299833/10000000000 : ℝ)|=(194299833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510516377/10000000000 : ℝ)|^83 ≤ (9559110206643/20000000000000 : ℝ)^67
        have hw : |(5510516377/10000000000 : ℝ)|=(5510516377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5510516377/10000000000 : ℝ)*x 0 + (5847857497/10000000000 : ℝ)*x 1 + (-194299833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510516377/10000000000 : ℝ)^83 ≤ (9559110206643/20000000000000 : ℝ)^67 := by
    have hnat : (5510516377 : ℕ)^83*20000000000000^67 ≤ 9559110206643^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510516377 10000000000 9559110206643 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5847857497/10000000000 : ℝ)^83 ≤ (51446308924749/100000000000000 : ℝ)^67 := by
    have hnat : (5847857497 : ℕ)^83*100000000000000^67 ≤ 51446308924749^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847857497 10000000000 51446308924749 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194299833/10000000000 : ℝ)^83 ≤ (379070012193/50000000000000 : ℝ)^67 := by
    have hnat : (194299833 : ℕ)^83*50000000000000^67 ≤ 379070012193^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194299833 10000000000 379070012193 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510516377/10000000000 : ℝ), (5847857497/10000000000 : ℝ), (-194299833/10000000000 : ℝ)] ![(9559110206643/20000000000000 : ℝ), (51446308924749/100000000000000 : ℝ), (379070012193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510516377/10000000000 : ℝ)|^83 ≤ (9559110206643/20000000000000 : ℝ)^67
        have hw : |(5510516377/10000000000 : ℝ)|=(5510516377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5847857497/10000000000 : ℝ)|^83 ≤ (51446308924749/100000000000000 : ℝ)^67
        have hw : |(5847857497/10000000000 : ℝ)|=(5847857497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194299833/10000000000 : ℝ)|^83 ≤ (379070012193/50000000000000 : ℝ)^67
        have hw : |(-194299833/10000000000 : ℝ)|=(194299833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-639672859/5000000000 : ℝ)*x 0 + (265437237/2500000000 : ℝ)*x 1 + (8850028197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (639672859/5000000000 : ℝ)^83 ≤ (244670339957/3125000000000 : ℝ)^67 := by
    have hnat : (639672859 : ℕ)^83*3125000000000^67 ≤ 244670339957^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639672859 5000000000 244670339957 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265437237/2500000000 : ℝ)^83 ≤ (1553710313091/25000000000000 : ℝ)^67 := by
    have hnat : (265437237 : ℕ)^83*25000000000000^67 ≤ 1553710313091^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265437237 2500000000 1553710313091 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8850028197/10000000000 : ℝ)^83 ≤ (85955707852989/100000000000000 : ℝ)^67 := by
    have hnat : (8850028197 : ℕ)^83*100000000000000^67 ≤ 85955707852989^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8850028197 10000000000 85955707852989 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-639672859/5000000000 : ℝ), (265437237/2500000000 : ℝ), (8850028197/10000000000 : ℝ)] ![(244670339957/3125000000000 : ℝ), (1553710313091/25000000000000 : ℝ), (85955707852989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-639672859/5000000000 : ℝ)|^83 ≤ (244670339957/3125000000000 : ℝ)^67
        have hw : |(-639672859/5000000000 : ℝ)|=(639672859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265437237/2500000000 : ℝ)|^83 ≤ (1553710313091/25000000000000 : ℝ)^67
        have hw : |(265437237/2500000000 : ℝ)|=(265437237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8850028197/10000000000 : ℝ)|^83 ≤ (85955707852989/100000000000000 : ℝ)^67
        have hw : |(8850028197/10000000000 : ℝ)|=(8850028197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (81658469/200000000 : ℝ)*x 0 + (-147012003/5000000000 : ℝ)*x 1 + (7130043069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81658469/200000000 : ℝ)^83 ≤ (2060387297691/6250000000000 : ℝ)^67 := by
    have hnat : (81658469 : ℕ)^83*6250000000000^67 ≤ 2060387297691^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81658469 200000000 2060387297691 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147012003/5000000000 : ℝ)^83 ≤ (1266553259201/100000000000000 : ℝ)^67 := by
    have hnat : (147012003 : ℕ)^83*100000000000000^67 ≤ 1266553259201^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147012003 5000000000 1266553259201 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7130043069/10000000000 : ℝ)^83 ≤ (32883624980661/50000000000000 : ℝ)^67 := by
    have hnat : (7130043069 : ℕ)^83*50000000000000^67 ≤ 32883624980661^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7130043069 10000000000 32883624980661 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81658469/200000000 : ℝ), (-147012003/5000000000 : ℝ), (7130043069/10000000000 : ℝ)] ![(2060387297691/6250000000000 : ℝ), (1266553259201/100000000000000 : ℝ), (32883624980661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81658469/200000000 : ℝ)|^83 ≤ (2060387297691/6250000000000 : ℝ)^67
        have hw : |(81658469/200000000 : ℝ)|=(81658469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147012003/5000000000 : ℝ)|^83 ≤ (1266553259201/100000000000000 : ℝ)^67
        have hw : |(-147012003/5000000000 : ℝ)|=(147012003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7130043069/10000000000 : ℝ)|^83 ≤ (32883624980661/50000000000000 : ℝ)^67
        have hw : |(7130043069/10000000000 : ℝ)|=(7130043069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1065079733/5000000000 : ℝ)*x 0 + (4396467147/5000000000 : ℝ)*x 1 + (-830521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065079733/5000000000 : ℝ)^83 ≤ (588969644261/4000000000000 : ℝ)^67 := by
    have hnat : (1065079733 : ℕ)^83*4000000000000^67 ≤ 588969644261^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065079733 5000000000 588969644261 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396467147/5000000000 : ℝ)^83 ≤ (85269291101767/100000000000000 : ℝ)^67 := by
    have hnat : (4396467147 : ℕ)^83*100000000000000^67 ≤ 85269291101767^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396467147 5000000000 85269291101767 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830521/2000000000 : ℝ)^83 ≤ (6467782369/100000000000000 : ℝ)^67 := by
    have hnat : (830521 : ℕ)^83*100000000000000^67 ≤ 6467782369^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830521 2000000000 6467782369 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065079733/5000000000 : ℝ), (4396467147/5000000000 : ℝ), (-830521/2000000000 : ℝ)] ![(588969644261/4000000000000 : ℝ), (85269291101767/100000000000000 : ℝ), (6467782369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065079733/5000000000 : ℝ)|^83 ≤ (588969644261/4000000000000 : ℝ)^67
        have hw : |(1065079733/5000000000 : ℝ)|=(1065079733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396467147/5000000000 : ℝ)|^83 ≤ (85269291101767/100000000000000 : ℝ)^67
        have hw : |(4396467147/5000000000 : ℝ)|=(4396467147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-830521/2000000000 : ℝ)|^83 ≤ (6467782369/100000000000000 : ℝ)^67
        have hw : |(-830521/2000000000 : ℝ)|=(830521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (400843941/2000000000 : ℝ)*x 0 + (1436563833/2000000000 : ℝ)*x 1 + (2724854853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400843941/2000000000 : ℝ)^83 ≤ (13653553753213/100000000000000 : ℝ)^67 := by
    have hnat : (400843941 : ℕ)^83*100000000000000^67 ≤ 13653553753213^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400843941 2000000000 13653553753213 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1436563833/2000000000 : ℝ)^83 ≤ (66370838559671/100000000000000 : ℝ)^67 := by
    have hnat : (1436563833 : ℕ)^83*100000000000000^67 ≤ 66370838559671^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436563833 2000000000 66370838559671 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724854853/10000000000 : ℝ)^83 ≤ (9987803837283/50000000000000 : ℝ)^67 := by
    have hnat : (2724854853 : ℕ)^83*50000000000000^67 ≤ 9987803837283^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724854853 10000000000 9987803837283 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(400843941/2000000000 : ℝ), (1436563833/2000000000 : ℝ), (2724854853/10000000000 : ℝ)] ![(13653553753213/100000000000000 : ℝ), (66370838559671/100000000000000 : ℝ), (9987803837283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(400843941/2000000000 : ℝ)|^83 ≤ (13653553753213/100000000000000 : ℝ)^67
        have hw : |(400843941/2000000000 : ℝ)|=(400843941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1436563833/2000000000 : ℝ)|^83 ≤ (66370838559671/100000000000000 : ℝ)^67
        have hw : |(1436563833/2000000000 : ℝ)|=(1436563833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724854853/10000000000 : ℝ)|^83 ≤ (9987803837283/50000000000000 : ℝ)^67
        have hw : |(2724854853/10000000000 : ℝ)|=(2724854853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-830521/2000000000 : ℝ)*x 0 + (1065079733/5000000000 : ℝ)*x 1 + (4396467147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830521/2000000000 : ℝ)^83 ≤ (6467782369/100000000000000 : ℝ)^67 := by
    have hnat : (830521 : ℕ)^83*100000000000000^67 ≤ 6467782369^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830521 2000000000 6467782369 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065079733/5000000000 : ℝ)^83 ≤ (588969644261/4000000000000 : ℝ)^67 := by
    have hnat : (1065079733 : ℕ)^83*4000000000000^67 ≤ 588969644261^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065079733 5000000000 588969644261 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396467147/5000000000 : ℝ)^83 ≤ (85269291101767/100000000000000 : ℝ)^67 := by
    have hnat : (4396467147 : ℕ)^83*100000000000000^67 ≤ 85269291101767^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396467147 5000000000 85269291101767 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-830521/2000000000 : ℝ), (1065079733/5000000000 : ℝ), (4396467147/5000000000 : ℝ)] ![(6467782369/100000000000000 : ℝ), (588969644261/4000000000000 : ℝ), (85269291101767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-830521/2000000000 : ℝ)|^83 ≤ (6467782369/100000000000000 : ℝ)^67
        have hw : |(-830521/2000000000 : ℝ)|=(830521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065079733/5000000000 : ℝ)|^83 ≤ (588969644261/4000000000000 : ℝ)^67
        have hw : |(1065079733/5000000000 : ℝ)|=(1065079733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4396467147/5000000000 : ℝ)|^83 ≤ (85269291101767/100000000000000 : ℝ)^67
        have hw : |(4396467147/5000000000 : ℝ)|=(4396467147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8850028197/10000000000 : ℝ)*x 0 + (-639672859/5000000000 : ℝ)*x 1 + (265437237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8850028197/10000000000 : ℝ)^83 ≤ (85955707852989/100000000000000 : ℝ)^67 := by
    have hnat : (8850028197 : ℕ)^83*100000000000000^67 ≤ 85955707852989^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8850028197 10000000000 85955707852989 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639672859/5000000000 : ℝ)^83 ≤ (244670339957/3125000000000 : ℝ)^67 := by
    have hnat : (639672859 : ℕ)^83*3125000000000^67 ≤ 244670339957^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639672859 5000000000 244670339957 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265437237/2500000000 : ℝ)^83 ≤ (1553710313091/25000000000000 : ℝ)^67 := by
    have hnat : (265437237 : ℕ)^83*25000000000000^67 ≤ 1553710313091^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265437237 2500000000 1553710313091 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8850028197/10000000000 : ℝ), (-639672859/5000000000 : ℝ), (265437237/2500000000 : ℝ)] ![(85955707852989/100000000000000 : ℝ), (244670339957/3125000000000 : ℝ), (1553710313091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8850028197/10000000000 : ℝ)|^83 ≤ (85955707852989/100000000000000 : ℝ)^67
        have hw : |(8850028197/10000000000 : ℝ)|=(8850028197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639672859/5000000000 : ℝ)|^83 ≤ (244670339957/3125000000000 : ℝ)^67
        have hw : |(-639672859/5000000000 : ℝ)|=(639672859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265437237/2500000000 : ℝ)|^83 ≤ (1553710313091/25000000000000 : ℝ)^67
        have hw : |(265437237/2500000000 : ℝ)|=(265437237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7130043069/10000000000 : ℝ)*x 0 + (81658469/200000000 : ℝ)*x 1 + (-147012003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7130043069/10000000000 : ℝ)^83 ≤ (32883624980661/50000000000000 : ℝ)^67 := by
    have hnat : (7130043069 : ℕ)^83*50000000000000^67 ≤ 32883624980661^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7130043069 10000000000 32883624980661 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81658469/200000000 : ℝ)^83 ≤ (2060387297691/6250000000000 : ℝ)^67 := by
    have hnat : (81658469 : ℕ)^83*6250000000000^67 ≤ 2060387297691^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81658469 200000000 2060387297691 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147012003/5000000000 : ℝ)^83 ≤ (1266553259201/100000000000000 : ℝ)^67 := by
    have hnat : (147012003 : ℕ)^83*100000000000000^67 ≤ 1266553259201^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147012003 5000000000 1266553259201 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7130043069/10000000000 : ℝ), (81658469/200000000 : ℝ), (-147012003/5000000000 : ℝ)] ![(32883624980661/50000000000000 : ℝ), (2060387297691/6250000000000 : ℝ), (1266553259201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7130043069/10000000000 : ℝ)|^83 ≤ (32883624980661/50000000000000 : ℝ)^67
        have hw : |(7130043069/10000000000 : ℝ)|=(7130043069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81658469/200000000 : ℝ)|^83 ≤ (2060387297691/6250000000000 : ℝ)^67
        have hw : |(81658469/200000000 : ℝ)|=(81658469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147012003/5000000000 : ℝ)|^83 ≤ (1266553259201/100000000000000 : ℝ)^67
        have hw : |(-147012003/5000000000 : ℝ)|=(147012003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2724854853/10000000000 : ℝ)*x 0 + (400843941/2000000000 : ℝ)*x 1 + (1436563833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2724854853/10000000000 : ℝ)^83 ≤ (9987803837283/50000000000000 : ℝ)^67 := by
    have hnat : (2724854853 : ℕ)^83*50000000000000^67 ≤ 9987803837283^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724854853 10000000000 9987803837283 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400843941/2000000000 : ℝ)^83 ≤ (13653553753213/100000000000000 : ℝ)^67 := by
    have hnat : (400843941 : ℕ)^83*100000000000000^67 ≤ 13653553753213^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400843941 2000000000 13653553753213 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1436563833/2000000000 : ℝ)^83 ≤ (66370838559671/100000000000000 : ℝ)^67 := by
    have hnat : (1436563833 : ℕ)^83*100000000000000^67 ≤ 66370838559671^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436563833 2000000000 66370838559671 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2724854853/10000000000 : ℝ), (400843941/2000000000 : ℝ), (1436563833/2000000000 : ℝ)] ![(9987803837283/50000000000000 : ℝ), (13653553753213/100000000000000 : ℝ), (66370838559671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2724854853/10000000000 : ℝ)|^83 ≤ (9987803837283/50000000000000 : ℝ)^67
        have hw : |(2724854853/10000000000 : ℝ)|=(2724854853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400843941/2000000000 : ℝ)|^83 ≤ (13653553753213/100000000000000 : ℝ)^67
        have hw : |(400843941/2000000000 : ℝ)|=(400843941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1436563833/2000000000 : ℝ)|^83 ≤ (66370838559671/100000000000000 : ℝ)^67
        have hw : |(1436563833/2000000000 : ℝ)|=(1436563833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-147012003/5000000000 : ℝ)*x 0 + (7130043069/10000000000 : ℝ)*x 1 + (81658469/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147012003/5000000000 : ℝ)^83 ≤ (1266553259201/100000000000000 : ℝ)^67 := by
    have hnat : (147012003 : ℕ)^83*100000000000000^67 ≤ 1266553259201^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147012003 5000000000 1266553259201 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7130043069/10000000000 : ℝ)^83 ≤ (32883624980661/50000000000000 : ℝ)^67 := by
    have hnat : (7130043069 : ℕ)^83*50000000000000^67 ≤ 32883624980661^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7130043069 10000000000 32883624980661 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81658469/200000000 : ℝ)^83 ≤ (2060387297691/6250000000000 : ℝ)^67 := by
    have hnat : (81658469 : ℕ)^83*6250000000000^67 ≤ 2060387297691^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81658469 200000000 2060387297691 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-147012003/5000000000 : ℝ), (7130043069/10000000000 : ℝ), (81658469/200000000 : ℝ)] ![(1266553259201/100000000000000 : ℝ), (32883624980661/50000000000000 : ℝ), (2060387297691/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-147012003/5000000000 : ℝ)|^83 ≤ (1266553259201/100000000000000 : ℝ)^67
        have hw : |(-147012003/5000000000 : ℝ)|=(147012003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7130043069/10000000000 : ℝ)|^83 ≤ (32883624980661/50000000000000 : ℝ)^67
        have hw : |(7130043069/10000000000 : ℝ)|=(7130043069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81658469/200000000 : ℝ)|^83 ≤ (2060387297691/6250000000000 : ℝ)^67
        have hw : |(81658469/200000000 : ℝ)|=(81658469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4396467147/5000000000 : ℝ)*x 0 + (-830521/2000000000 : ℝ)*x 1 + (1065079733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4396467147/5000000000 : ℝ)^83 ≤ (85269291101767/100000000000000 : ℝ)^67 := by
    have hnat : (4396467147 : ℕ)^83*100000000000000^67 ≤ 85269291101767^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396467147 5000000000 85269291101767 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830521/2000000000 : ℝ)^83 ≤ (6467782369/100000000000000 : ℝ)^67 := by
    have hnat : (830521 : ℕ)^83*100000000000000^67 ≤ 6467782369^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830521 2000000000 6467782369 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065079733/5000000000 : ℝ)^83 ≤ (588969644261/4000000000000 : ℝ)^67 := by
    have hnat : (1065079733 : ℕ)^83*4000000000000^67 ≤ 588969644261^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065079733 5000000000 588969644261 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4396467147/5000000000 : ℝ), (-830521/2000000000 : ℝ), (1065079733/5000000000 : ℝ)] ![(85269291101767/100000000000000 : ℝ), (6467782369/100000000000000 : ℝ), (588969644261/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4396467147/5000000000 : ℝ)|^83 ≤ (85269291101767/100000000000000 : ℝ)^67
        have hw : |(4396467147/5000000000 : ℝ)|=(4396467147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-830521/2000000000 : ℝ)|^83 ≤ (6467782369/100000000000000 : ℝ)^67
        have hw : |(-830521/2000000000 : ℝ)|=(830521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1065079733/5000000000 : ℝ)|^83 ≤ (588969644261/4000000000000 : ℝ)^67
        have hw : |(1065079733/5000000000 : ℝ)|=(1065079733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (265437237/2500000000 : ℝ)*x 0 + (8850028197/10000000000 : ℝ)*x 1 + (-639672859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265437237/2500000000 : ℝ)^83 ≤ (1553710313091/25000000000000 : ℝ)^67 := by
    have hnat : (265437237 : ℕ)^83*25000000000000^67 ≤ 1553710313091^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265437237 2500000000 1553710313091 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8850028197/10000000000 : ℝ)^83 ≤ (85955707852989/100000000000000 : ℝ)^67 := by
    have hnat : (8850028197 : ℕ)^83*100000000000000^67 ≤ 85955707852989^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8850028197 10000000000 85955707852989 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639672859/5000000000 : ℝ)^83 ≤ (244670339957/3125000000000 : ℝ)^67 := by
    have hnat : (639672859 : ℕ)^83*3125000000000^67 ≤ 244670339957^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639672859 5000000000 244670339957 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265437237/2500000000 : ℝ), (8850028197/10000000000 : ℝ), (-639672859/5000000000 : ℝ)] ![(1553710313091/25000000000000 : ℝ), (85955707852989/100000000000000 : ℝ), (244670339957/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265437237/2500000000 : ℝ)|^83 ≤ (1553710313091/25000000000000 : ℝ)^67
        have hw : |(265437237/2500000000 : ℝ)|=(265437237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8850028197/10000000000 : ℝ)|^83 ≤ (85955707852989/100000000000000 : ℝ)^67
        have hw : |(8850028197/10000000000 : ℝ)|=(8850028197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-639672859/5000000000 : ℝ)|^83 ≤ (244670339957/3125000000000 : ℝ)^67
        have hw : |(-639672859/5000000000 : ℝ)|=(639672859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s0_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1436563833/2000000000 : ℝ)*x 0 + (2724854853/10000000000 : ℝ)*x 1 + (400843941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1436563833/2000000000 : ℝ)^83 ≤ (66370838559671/100000000000000 : ℝ)^67 := by
    have hnat : (1436563833 : ℕ)^83*100000000000000^67 ≤ 66370838559671^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436563833 2000000000 66370838559671 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724854853/10000000000 : ℝ)^83 ≤ (9987803837283/50000000000000 : ℝ)^67 := by
    have hnat : (2724854853 : ℕ)^83*50000000000000^67 ≤ 9987803837283^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724854853 10000000000 9987803837283 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400843941/2000000000 : ℝ)^83 ≤ (13653553753213/100000000000000 : ℝ)^67 := by
    have hnat : (400843941 : ℕ)^83*100000000000000^67 ≤ 13653553753213^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400843941 2000000000 13653553753213 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1436563833/2000000000 : ℝ), (2724854853/10000000000 : ℝ), (400843941/2000000000 : ℝ)] ![(66370838559671/100000000000000 : ℝ), (9987803837283/50000000000000 : ℝ), (13653553753213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1436563833/2000000000 : ℝ)|^83 ≤ (66370838559671/100000000000000 : ℝ)^67
        have hw : |(1436563833/2000000000 : ℝ)|=(1436563833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724854853/10000000000 : ℝ)|^83 ≤ (9987803837283/50000000000000 : ℝ)^67
        have hw : |(2724854853/10000000000 : ℝ)|=(2724854853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400843941/2000000000 : ℝ)|^83 ≤ (13653553753213/100000000000000 : ℝ)^67
        have hw : |(400843941/2000000000 : ℝ)|=(400843941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-239460727/2500000000 : ℝ)*x 0 + (5450209429/10000000000 : ℝ)*x 1 + (5471917243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239460727/2500000000 : ℝ)^83 ≤ (1367606923789/25000000000000 : ℝ)^67 := by
    have hnat : (239460727 : ℕ)^83*25000000000000^67 ≤ 1367606923789^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239460727 2500000000 1367606923789 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450209429/10000000000 : ℝ)^83 ≤ (23574206930039/50000000000000 : ℝ)^67 := by
    have hnat : (5450209429 : ℕ)^83*50000000000000^67 ≤ 23574206930039^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450209429 10000000000 23574206930039 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471917243/10000000000 : ℝ)^83 ≤ (379049267449/800000000000 : ℝ)^67 := by
    have hnat : (5471917243 : ℕ)^83*800000000000^67 ≤ 379049267449^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471917243 10000000000 379049267449 800000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239460727/2500000000 : ℝ), (5450209429/10000000000 : ℝ), (5471917243/10000000000 : ℝ)] ![(1367606923789/25000000000000 : ℝ), (23574206930039/50000000000000 : ℝ), (379049267449/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239460727/2500000000 : ℝ)|^83 ≤ (1367606923789/25000000000000 : ℝ)^67
        have hw : |(-239460727/2500000000 : ℝ)|=(239460727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450209429/10000000000 : ℝ)|^83 ≤ (23574206930039/50000000000000 : ℝ)^67
        have hw : |(5450209429/10000000000 : ℝ)|=(5450209429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471917243/10000000000 : ℝ)|^83 ≤ (379049267449/800000000000 : ℝ)^67
        have hw : |(5471917243/10000000000 : ℝ)|=(5471917243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1367979303/2500000000 : ℝ)*x 0 + (-957842961/10000000000 : ℝ)*x 1 + (2725104713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1367979303/2500000000 : ℝ)^83 ≤ (23690579049297/50000000000000 : ℝ)^67 := by
    have hnat : (1367979303 : ℕ)^83*50000000000000^67 ≤ 23690579049297^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367979303 2500000000 23690579049297 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957842961/10000000000 : ℝ)^83 ≤ (1094085614027/20000000000000 : ℝ)^67 := by
    have hnat : (957842961 : ℕ)^83*20000000000000^67 ≤ 1094085614027^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957842961 10000000000 1094085614027 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725104713/5000000000 : ℝ)^83 ≤ (5893551728491/12500000000000 : ℝ)^67 := by
    have hnat : (2725104713 : ℕ)^83*12500000000000^67 ≤ 5893551728491^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725104713 5000000000 5893551728491 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1367979303/2500000000 : ℝ), (-957842961/10000000000 : ℝ), (2725104713/5000000000 : ℝ)] ![(23690579049297/50000000000000 : ℝ), (1094085614027/20000000000000 : ℝ), (5893551728491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1367979303/2500000000 : ℝ)|^83 ≤ (23690579049297/50000000000000 : ℝ)^67
        have hw : |(1367979303/2500000000 : ℝ)|=(1367979303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-957842961/10000000000 : ℝ)|^83 ≤ (1094085614027/20000000000000 : ℝ)^67
        have hw : |(-957842961/10000000000 : ℝ)|=(957842961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725104713/5000000000 : ℝ)|^83 ≤ (5893551728491/12500000000000 : ℝ)^67
        have hw : |(2725104713/5000000000 : ℝ)|=(2725104713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2725104773/5000000000 : ℝ)*x 0 + (683989639/1250000000 : ℝ)*x 1 + (-95784293/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2725104773/5000000000 : ℝ)^83 ≤ (47148415113921/100000000000000 : ℝ)^67 := by
    have hnat : (2725104773 : ℕ)^83*100000000000000^67 ≤ 47148415113921^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725104773 5000000000 47148415113921 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683989639/1250000000 : ℝ)^83 ≤ (11845289256479/25000000000000 : ℝ)^67 := by
    have hnat : (683989639 : ℕ)^83*25000000000000^67 ≤ 11845289256479^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683989639 1250000000 11845289256479 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95784293/1000000000 : ℝ)^83 ≤ (683803481351/12500000000000 : ℝ)^67 := by
    have hnat : (95784293 : ℕ)^83*12500000000000^67 ≤ 683803481351^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95784293 1000000000 683803481351 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2725104773/5000000000 : ℝ), (683989639/1250000000 : ℝ), (-95784293/1000000000 : ℝ)] ![(47148415113921/100000000000000 : ℝ), (11845289256479/25000000000000 : ℝ), (683803481351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2725104773/5000000000 : ℝ)|^83 ≤ (47148415113921/100000000000000 : ℝ)^67
        have hw : |(2725104773/5000000000 : ℝ)|=(2725104773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683989639/1250000000 : ℝ)|^83 ≤ (11845289256479/25000000000000 : ℝ)^67
        have hw : |(683989639/1250000000 : ℝ)|=(683989639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95784293/1000000000 : ℝ)|^83 ≤ (683803481351/12500000000000 : ℝ)^67
        have hw : |(-95784293/1000000000 : ℝ)|=(95784293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-832513557/10000000000 : ℝ)*x 0 + (2248190843/5000000000 : ℝ)*x 1 + (6464704711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832513557/10000000000 : ℝ)^83 ≤ (183922264849/4000000000000 : ℝ)^67 := by
    have hnat : (832513557 : ℕ)^83*4000000000000^67 ≤ 183922264849^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832513557 10000000000 183922264849 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248190843/5000000000 : ℝ)^83 ≤ (1160953551723/3125000000000 : ℝ)^67 := by
    have hnat : (2248190843 : ℕ)^83*3125000000000^67 ≤ 1160953551723^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248190843 5000000000 1160953551723 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6464704711/10000000000 : ℝ)^83 ≤ (2330057188299/4000000000000 : ℝ)^67 := by
    have hnat : (6464704711 : ℕ)^83*4000000000000^67 ≤ 2330057188299^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6464704711 10000000000 2330057188299 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-832513557/10000000000 : ℝ), (2248190843/5000000000 : ℝ), (6464704711/10000000000 : ℝ)] ![(183922264849/4000000000000 : ℝ), (1160953551723/3125000000000 : ℝ), (2330057188299/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-832513557/10000000000 : ℝ)|^83 ≤ (183922264849/4000000000000 : ℝ)^67
        have hw : |(-832513557/10000000000 : ℝ)|=(832513557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248190843/5000000000 : ℝ)|^83 ≤ (1160953551723/3125000000000 : ℝ)^67
        have hw : |(2248190843/5000000000 : ℝ)|=(2248190843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6464704711/10000000000 : ℝ)|^83 ≤ (2330057188299/4000000000000 : ℝ)^67
        have hw : |(6464704711/10000000000 : ℝ)|=(6464704711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (22691129/40000000 : ℝ)*x 0 + (-122010013/10000000000 : ℝ)*x 1 + (2858722931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22691129/40000000 : ℝ)^83 ≤ (9909030180271/20000000000000 : ℝ)^67 := by
    have hnat : (22691129 : ℕ)^83*20000000000000^67 ≤ 9909030180271^67*40000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22691129 40000000 9909030180271 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122010013/10000000000 : ℝ)^83 ≤ (17040223209/4000000000000 : ℝ)^67 := by
    have hnat : (122010013 : ℕ)^83*4000000000000^67 ≤ 17040223209^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122010013 10000000000 17040223209 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858722931/5000000000 : ℝ)^83 ≤ (12507210876989/25000000000000 : ℝ)^67 := by
    have hnat : (2858722931 : ℕ)^83*25000000000000^67 ≤ 12507210876989^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858722931 5000000000 12507210876989 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22691129/40000000 : ℝ), (-122010013/10000000000 : ℝ), (2858722931/5000000000 : ℝ)] ![(9909030180271/20000000000000 : ℝ), (17040223209/4000000000000 : ℝ), (12507210876989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22691129/40000000 : ℝ)|^83 ≤ (9909030180271/20000000000000 : ℝ)^67
        have hw : |(22691129/40000000 : ℝ)|=(22691129/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122010013/10000000000 : ℝ)|^83 ≤ (17040223209/4000000000000 : ℝ)^67
        have hw : |(-122010013/10000000000 : ℝ)|=(122010013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858722931/5000000000 : ℝ)|^83 ≤ (12507210876989/25000000000000 : ℝ)^67
        have hw : |(2858722931/5000000000 : ℝ)|=(2858722931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (66462049/156250000 : ℝ)*x 0 + (7075100159/10000000000 : ℝ)*x 1 + (-1889161/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66462049/156250000 : ℝ)^83 ≤ (17340749789803/50000000000000 : ℝ)^67 := by
    have hnat : (66462049 : ℕ)^83*50000000000000^67 ≤ 17340749789803^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66462049 156250000 17340749789803 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7075100159/10000000000 : ℝ)^83 ≤ (6514001260767/10000000000000 : ℝ)^67 := by
    have hnat : (7075100159 : ℕ)^83*10000000000000^67 ≤ 6514001260767^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7075100159 10000000000 6514001260767 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889161/312500000 : ℝ)^83 ≤ (178487805373/100000000000000 : ℝ)^67 := by
    have hnat : (1889161 : ℕ)^83*100000000000000^67 ≤ 178487805373^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889161 312500000 178487805373 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66462049/156250000 : ℝ), (7075100159/10000000000 : ℝ), (-1889161/312500000 : ℝ)] ![(17340749789803/50000000000000 : ℝ), (6514001260767/10000000000000 : ℝ), (178487805373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66462049/156250000 : ℝ)|^83 ≤ (17340749789803/50000000000000 : ℝ)^67
        have hw : |(66462049/156250000 : ℝ)|=(66462049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7075100159/10000000000 : ℝ)|^83 ≤ (6514001260767/10000000000000 : ℝ)^67
        have hw : |(7075100159/10000000000 : ℝ)|=(7075100159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889161/312500000 : ℝ)|^83 ≤ (178487805373/100000000000000 : ℝ)^67
        have hw : |(-1889161/312500000 : ℝ)|=(1889161/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3568170357/10000000000 : ℝ)*x 0 + (515695159/1000000000 : ℝ)*x 1 + (358660211/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3568170357/10000000000 : ℝ)^83 ≤ (6974401135481/25000000000000 : ℝ)^67 := by
    have hnat : (3568170357 : ℕ)^83*25000000000000^67 ≤ 6974401135481^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3568170357 10000000000 6974401135481 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515695159/1000000000 : ℝ)^83 ≤ (2751634945289/6250000000000 : ℝ)^67 := by
    have hnat : (515695159 : ℕ)^83*6250000000000^67 ≤ 2751634945289^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515695159 1000000000 2751634945289 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358660211/1000000000 : ℝ)^83 ≤ (28076236311097/100000000000000 : ℝ)^67 := by
    have hnat : (358660211 : ℕ)^83*100000000000000^67 ≤ 28076236311097^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358660211 1000000000 28076236311097 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3568170357/10000000000 : ℝ), (515695159/1000000000 : ℝ), (358660211/1000000000 : ℝ)] ![(6974401135481/25000000000000 : ℝ), (2751634945289/6250000000000 : ℝ), (28076236311097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3568170357/10000000000 : ℝ)|^83 ≤ (6974401135481/25000000000000 : ℝ)^67
        have hw : |(3568170357/10000000000 : ℝ)|=(3568170357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515695159/1000000000 : ℝ)|^83 ≤ (2751634945289/6250000000000 : ℝ)^67
        have hw : |(515695159/1000000000 : ℝ)|=(515695159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(358660211/1000000000 : ℝ)|^83 ≤ (28076236311097/100000000000000 : ℝ)^67
        have hw : |(358660211/1000000000 : ℝ)|=(358660211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1889161/312500000 : ℝ)*x 0 + (66462049/156250000 : ℝ)*x 1 + (7075100159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1889161/312500000 : ℝ)^83 ≤ (178487805373/100000000000000 : ℝ)^67 := by
    have hnat : (1889161 : ℕ)^83*100000000000000^67 ≤ 178487805373^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889161 312500000 178487805373 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66462049/156250000 : ℝ)^83 ≤ (17340749789803/50000000000000 : ℝ)^67 := by
    have hnat : (66462049 : ℕ)^83*50000000000000^67 ≤ 17340749789803^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66462049 156250000 17340749789803 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7075100159/10000000000 : ℝ)^83 ≤ (6514001260767/10000000000000 : ℝ)^67 := by
    have hnat : (7075100159 : ℕ)^83*10000000000000^67 ≤ 6514001260767^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7075100159 10000000000 6514001260767 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1889161/312500000 : ℝ), (66462049/156250000 : ℝ), (7075100159/10000000000 : ℝ)] ![(178487805373/100000000000000 : ℝ), (17340749789803/50000000000000 : ℝ), (6514001260767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1889161/312500000 : ℝ)|^83 ≤ (178487805373/100000000000000 : ℝ)^67
        have hw : |(-1889161/312500000 : ℝ)|=(1889161/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66462049/156250000 : ℝ)|^83 ≤ (17340749789803/50000000000000 : ℝ)^67
        have hw : |(66462049/156250000 : ℝ)|=(66462049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7075100159/10000000000 : ℝ)|^83 ≤ (6514001260767/10000000000000 : ℝ)^67
        have hw : |(7075100159/10000000000 : ℝ)|=(7075100159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6464704711/10000000000 : ℝ)*x 0 + (-832513557/10000000000 : ℝ)*x 1 + (2248190843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6464704711/10000000000 : ℝ)^83 ≤ (2330057188299/4000000000000 : ℝ)^67 := by
    have hnat : (6464704711 : ℕ)^83*4000000000000^67 ≤ 2330057188299^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6464704711 10000000000 2330057188299 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832513557/10000000000 : ℝ)^83 ≤ (183922264849/4000000000000 : ℝ)^67 := by
    have hnat : (832513557 : ℕ)^83*4000000000000^67 ≤ 183922264849^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832513557 10000000000 183922264849 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248190843/5000000000 : ℝ)^83 ≤ (1160953551723/3125000000000 : ℝ)^67 := by
    have hnat : (2248190843 : ℕ)^83*3125000000000^67 ≤ 1160953551723^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248190843 5000000000 1160953551723 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6464704711/10000000000 : ℝ), (-832513557/10000000000 : ℝ), (2248190843/5000000000 : ℝ)] ![(2330057188299/4000000000000 : ℝ), (183922264849/4000000000000 : ℝ), (1160953551723/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6464704711/10000000000 : ℝ)|^83 ≤ (2330057188299/4000000000000 : ℝ)^67
        have hw : |(6464704711/10000000000 : ℝ)|=(6464704711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832513557/10000000000 : ℝ)|^83 ≤ (183922264849/4000000000000 : ℝ)^67
        have hw : |(-832513557/10000000000 : ℝ)|=(832513557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248190843/5000000000 : ℝ)|^83 ≤ (1160953551723/3125000000000 : ℝ)^67
        have hw : |(2248190843/5000000000 : ℝ)|=(2248190843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2858722931/5000000000 : ℝ)*x 0 + (22691129/40000000 : ℝ)*x 1 + (-122010013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2858722931/5000000000 : ℝ)^83 ≤ (12507210876989/25000000000000 : ℝ)^67 := by
    have hnat : (2858722931 : ℕ)^83*25000000000000^67 ≤ 12507210876989^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858722931 5000000000 12507210876989 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22691129/40000000 : ℝ)^83 ≤ (9909030180271/20000000000000 : ℝ)^67 := by
    have hnat : (22691129 : ℕ)^83*20000000000000^67 ≤ 9909030180271^67*40000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22691129 40000000 9909030180271 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122010013/10000000000 : ℝ)^83 ≤ (17040223209/4000000000000 : ℝ)^67 := by
    have hnat : (122010013 : ℕ)^83*4000000000000^67 ≤ 17040223209^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122010013 10000000000 17040223209 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2858722931/5000000000 : ℝ), (22691129/40000000 : ℝ), (-122010013/10000000000 : ℝ)] ![(12507210876989/25000000000000 : ℝ), (9909030180271/20000000000000 : ℝ), (17040223209/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2858722931/5000000000 : ℝ)|^83 ≤ (12507210876989/25000000000000 : ℝ)^67
        have hw : |(2858722931/5000000000 : ℝ)|=(2858722931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22691129/40000000 : ℝ)|^83 ≤ (9909030180271/20000000000000 : ℝ)^67
        have hw : |(22691129/40000000 : ℝ)|=(22691129/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122010013/10000000000 : ℝ)|^83 ≤ (17040223209/4000000000000 : ℝ)^67
        have hw : |(-122010013/10000000000 : ℝ)|=(122010013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (358660211/1000000000 : ℝ)*x 0 + (3568170357/10000000000 : ℝ)*x 1 + (515695159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358660211/1000000000 : ℝ)^83 ≤ (28076236311097/100000000000000 : ℝ)^67 := by
    have hnat : (358660211 : ℕ)^83*100000000000000^67 ≤ 28076236311097^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358660211 1000000000 28076236311097 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3568170357/10000000000 : ℝ)^83 ≤ (6974401135481/25000000000000 : ℝ)^67 := by
    have hnat : (3568170357 : ℕ)^83*25000000000000^67 ≤ 6974401135481^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3568170357 10000000000 6974401135481 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515695159/1000000000 : ℝ)^83 ≤ (2751634945289/6250000000000 : ℝ)^67 := by
    have hnat : (515695159 : ℕ)^83*6250000000000^67 ≤ 2751634945289^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515695159 1000000000 2751634945289 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(358660211/1000000000 : ℝ), (3568170357/10000000000 : ℝ), (515695159/1000000000 : ℝ)] ![(28076236311097/100000000000000 : ℝ), (6974401135481/25000000000000 : ℝ), (2751634945289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(358660211/1000000000 : ℝ)|^83 ≤ (28076236311097/100000000000000 : ℝ)^67
        have hw : |(358660211/1000000000 : ℝ)|=(358660211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3568170357/10000000000 : ℝ)|^83 ≤ (6974401135481/25000000000000 : ℝ)^67
        have hw : |(3568170357/10000000000 : ℝ)|=(3568170357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515695159/1000000000 : ℝ)|^83 ≤ (2751634945289/6250000000000 : ℝ)^67
        have hw : |(515695159/1000000000 : ℝ)|=(515695159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-122010013/10000000000 : ℝ)*x 0 + (2858722931/5000000000 : ℝ)*x 1 + (22691129/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122010013/10000000000 : ℝ)^83 ≤ (17040223209/4000000000000 : ℝ)^67 := by
    have hnat : (122010013 : ℕ)^83*4000000000000^67 ≤ 17040223209^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122010013 10000000000 17040223209 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2858722931/5000000000 : ℝ)^83 ≤ (12507210876989/25000000000000 : ℝ)^67 := by
    have hnat : (2858722931 : ℕ)^83*25000000000000^67 ≤ 12507210876989^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858722931 5000000000 12507210876989 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22691129/40000000 : ℝ)^83 ≤ (9909030180271/20000000000000 : ℝ)^67 := by
    have hnat : (22691129 : ℕ)^83*20000000000000^67 ≤ 9909030180271^67*40000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22691129 40000000 9909030180271 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122010013/10000000000 : ℝ), (2858722931/5000000000 : ℝ), (22691129/40000000 : ℝ)] ![(17040223209/4000000000000 : ℝ), (12507210876989/25000000000000 : ℝ), (9909030180271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122010013/10000000000 : ℝ)|^83 ≤ (17040223209/4000000000000 : ℝ)^67
        have hw : |(-122010013/10000000000 : ℝ)|=(122010013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2858722931/5000000000 : ℝ)|^83 ≤ (12507210876989/25000000000000 : ℝ)^67
        have hw : |(2858722931/5000000000 : ℝ)|=(2858722931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22691129/40000000 : ℝ)|^83 ≤ (9909030180271/20000000000000 : ℝ)^67
        have hw : |(22691129/40000000 : ℝ)|=(22691129/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7075100159/10000000000 : ℝ)*x 0 + (-1889161/312500000 : ℝ)*x 1 + (66462049/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7075100159/10000000000 : ℝ)^83 ≤ (6514001260767/10000000000000 : ℝ)^67 := by
    have hnat : (7075100159 : ℕ)^83*10000000000000^67 ≤ 6514001260767^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7075100159 10000000000 6514001260767 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889161/312500000 : ℝ)^83 ≤ (178487805373/100000000000000 : ℝ)^67 := by
    have hnat : (1889161 : ℕ)^83*100000000000000^67 ≤ 178487805373^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889161 312500000 178487805373 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66462049/156250000 : ℝ)^83 ≤ (17340749789803/50000000000000 : ℝ)^67 := by
    have hnat : (66462049 : ℕ)^83*50000000000000^67 ≤ 17340749789803^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66462049 156250000 17340749789803 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7075100159/10000000000 : ℝ), (-1889161/312500000 : ℝ), (66462049/156250000 : ℝ)] ![(6514001260767/10000000000000 : ℝ), (178487805373/100000000000000 : ℝ), (17340749789803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7075100159/10000000000 : ℝ)|^83 ≤ (6514001260767/10000000000000 : ℝ)^67
        have hw : |(7075100159/10000000000 : ℝ)|=(7075100159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889161/312500000 : ℝ)|^83 ≤ (178487805373/100000000000000 : ℝ)^67
        have hw : |(-1889161/312500000 : ℝ)|=(1889161/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66462049/156250000 : ℝ)|^83 ≤ (17340749789803/50000000000000 : ℝ)^67
        have hw : |(66462049/156250000 : ℝ)|=(66462049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2248190843/5000000000 : ℝ)*x 0 + (6464704711/10000000000 : ℝ)*x 1 + (-832513557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248190843/5000000000 : ℝ)^83 ≤ (1160953551723/3125000000000 : ℝ)^67 := by
    have hnat : (2248190843 : ℕ)^83*3125000000000^67 ≤ 1160953551723^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248190843 5000000000 1160953551723 3125000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6464704711/10000000000 : ℝ)^83 ≤ (2330057188299/4000000000000 : ℝ)^67 := by
    have hnat : (6464704711 : ℕ)^83*4000000000000^67 ≤ 2330057188299^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6464704711 10000000000 2330057188299 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832513557/10000000000 : ℝ)^83 ≤ (183922264849/4000000000000 : ℝ)^67 := by
    have hnat : (832513557 : ℕ)^83*4000000000000^67 ≤ 183922264849^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832513557 10000000000 183922264849 4000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248190843/5000000000 : ℝ), (6464704711/10000000000 : ℝ), (-832513557/10000000000 : ℝ)] ![(1160953551723/3125000000000 : ℝ), (2330057188299/4000000000000 : ℝ), (183922264849/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248190843/5000000000 : ℝ)|^83 ≤ (1160953551723/3125000000000 : ℝ)^67
        have hw : |(2248190843/5000000000 : ℝ)|=(2248190843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6464704711/10000000000 : ℝ)|^83 ≤ (2330057188299/4000000000000 : ℝ)^67
        have hw : |(6464704711/10000000000 : ℝ)|=(6464704711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-832513557/10000000000 : ℝ)|^83 ≤ (183922264849/4000000000000 : ℝ)^67
        have hw : |(-832513557/10000000000 : ℝ)|=(832513557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322087_s1_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (515695159/1000000000 : ℝ)*x 0 + (358660211/1000000000 : ℝ)*x 1 + (3568170357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515695159/1000000000 : ℝ)^83 ≤ (2751634945289/6250000000000 : ℝ)^67 := by
    have hnat : (515695159 : ℕ)^83*6250000000000^67 ≤ 2751634945289^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515695159 1000000000 2751634945289 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358660211/1000000000 : ℝ)^83 ≤ (28076236311097/100000000000000 : ℝ)^67 := by
    have hnat : (358660211 : ℕ)^83*100000000000000^67 ≤ 28076236311097^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358660211 1000000000 28076236311097 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3568170357/10000000000 : ℝ)^83 ≤ (6974401135481/25000000000000 : ℝ)^67 := by
    have hnat : (3568170357 : ℕ)^83*25000000000000^67 ≤ 6974401135481^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3568170357 10000000000 6974401135481 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515695159/1000000000 : ℝ), (358660211/1000000000 : ℝ), (3568170357/10000000000 : ℝ)] ![(2751634945289/6250000000000 : ℝ), (28076236311097/100000000000000 : ℝ), (6974401135481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515695159/1000000000 : ℝ)|^83 ≤ (2751634945289/6250000000000 : ℝ)^67
        have hw : |(515695159/1000000000 : ℝ)|=(515695159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(358660211/1000000000 : ℝ)|^83 ≤ (28076236311097/100000000000000 : ℝ)^67
        have hw : |(358660211/1000000000 : ℝ)|=(358660211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3568170357/10000000000 : ℝ)|^83 ≤ (6974401135481/25000000000000 : ℝ)^67
        have hw : |(3568170357/10000000000 : ℝ)|=(3568170357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322087 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((19767/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19767/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((19767/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(19767/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19767/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19767/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (167697/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-194299833/10000000000 : ℝ)*X 0 0+(5510516377/10000000000 : ℝ)*X 0 1+(5847857497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5847857497/10000000000 : ℝ)*X 1 0+(-194299833/10000000000 : ℝ)*X 1 1+(5510516377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5510516377/10000000000 : ℝ)*X 2 0+(5847857497/10000000000 : ℝ)*X 2 1+(-194299833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-639672859/5000000000 : ℝ)*X 0 0+(265437237/2500000000 : ℝ)*X 0 1+(8850028197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((81658469/200000000 : ℝ)*X 1 0+(-147012003/5000000000 : ℝ)*X 1 1+(7130043069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1065079733/5000000000 : ℝ)*X 2 0+(4396467147/5000000000 : ℝ)*X 2 1+(-830521/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((400843941/2000000000 : ℝ)*X 0 0+(1436563833/2000000000 : ℝ)*X 0 1+(2724854853/10000000000 : ℝ)*X 0 2+(400843941/2000000000 : ℝ)*X 1 0+(1436563833/2000000000 : ℝ)*X 1 1+(2724854853/10000000000 : ℝ)*X 1 2+(400843941/2000000000 : ℝ)*X 2 0+(1436563833/2000000000 : ℝ)*X 2 1+(2724854853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-830521/2000000000 : ℝ)*X 0 0+(1065079733/5000000000 : ℝ)*X 0 1+(4396467147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8850028197/10000000000 : ℝ)*X 1 0+(-639672859/5000000000 : ℝ)*X 1 1+(265437237/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7130043069/10000000000 : ℝ)*X 2 0+(81658469/200000000 : ℝ)*X 2 1+(-147012003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2724854853/10000000000 : ℝ)*X 0 0+(400843941/2000000000 : ℝ)*X 0 1+(1436563833/2000000000 : ℝ)*X 0 2+(2724854853/10000000000 : ℝ)*X 1 0+(400843941/2000000000 : ℝ)*X 1 1+(1436563833/2000000000 : ℝ)*X 1 2+(2724854853/10000000000 : ℝ)*X 2 0+(400843941/2000000000 : ℝ)*X 2 1+(1436563833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-147012003/5000000000 : ℝ)*X 0 0+(7130043069/10000000000 : ℝ)*X 0 1+(81658469/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4396467147/5000000000 : ℝ)*X 1 0+(-830521/2000000000 : ℝ)*X 1 1+(1065079733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((265437237/2500000000 : ℝ)*X 2 0+(8850028197/10000000000 : ℝ)*X 2 1+(-639672859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1436563833/2000000000 : ℝ)*X 0 0+(2724854853/10000000000 : ℝ)*X 0 1+(400843941/2000000000 : ℝ)*X 0 2+(1436563833/2000000000 : ℝ)*X 1 0+(2724854853/10000000000 : ℝ)*X 1 1+(400843941/2000000000 : ℝ)*X 1 2+(1436563833/2000000000 : ℝ)*X 2 0+(2724854853/10000000000 : ℝ)*X 2 1+(400843941/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((13471/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13471/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32786707253059555655793/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286432766337/250000000000 : ℝ)*(base7) + (3509661/1000000000000 : ℝ)*(base19) + (17498933247/100000000000 : ℝ)*(base50) + (873971/1000000000000 : ℝ)*(base53) + (33234985713/1000000000000 : ℝ)*(base60) + (697849571117/500000000000 : ℝ)*(major_s0_0) + (697849571117/500000000000 : ℝ)*(major_s0_1) + (1395698268263/1000000000000 : ℝ)*(major_s0_2) + (1520533/1000000000000 : ℝ)*(sp_s0_0) + (356930654947/250000000000 : ℝ)*(sp_s0_7) + (1427741858127/1000000000000 : ℝ)*(sp_s0_8) + (1427746241759/1000000000000 : ℝ)*(sp_s0_9) + (467232178513/250000000000 : ℝ)*(sp_s0_13) + (21227467/1000000000000 : ℝ)*(sp_s0_14) + (11299963261/15625000000 : ℝ)*(f.failure) + (1427746241759/1000000000000 : ℝ)*(f.sum) + (4214221101833537/5000000000000000000000000000 : ℝ)*base63 + (417708719156199/2000000000000000000000000000 : ℝ)*base64 + (56433371970339/1250000000000000000000000000 : ℝ)*base67 + (1979865017663121/2500000000000000000000000000 : ℝ)*base69 + (6758179480018283/10000000000000000000000000000 : ℝ)*base70 + (585499755601459/1000000000000000000000000000 : ℝ)*base73 + (890702832101459/1000000000000000000000000000 : ℝ)*base75 + (453659130095339/1250000000000000000000000000 : ℝ)*base77 + (2411017859611349/5000000000000000000000000000 : ℝ)*base78 + (47/312500000000000 : ℝ)*base86 + (47/312500000000000 : ℝ)*base88 + (47/312500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((13471/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(13471/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32786707253059555655793/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286432766337/250000000000 : ℝ)*(base7) + (3509661/1000000000000 : ℝ)*(base21) + (873971/1000000000000 : ℝ)*(base33) + (33234985713/1000000000000 : ℝ)*(base40) + (17498933247/100000000000 : ℝ)*(base60) + (1395698268263/1000000000000 : ℝ)*(major_s0_0) + (697849571117/500000000000 : ℝ)*(major_s0_1) + (697849571117/500000000000 : ℝ)*(major_s0_2) + (1520533/1000000000000 : ℝ)*(sp_s0_1) + (1427746241759/1000000000000 : ℝ)*(sp_s0_14) + (356930654947/250000000000 : ℝ)*(sp_s0_15) + (1427741858127/1000000000000 : ℝ)*(sp_s0_16) + (467232178513/250000000000 : ℝ)*(sp_s0_20) + (21227467/1000000000000 : ℝ)*(sp_s0_22) + (11299963261/15625000000 : ℝ)*(f.failure) + (1427746241759/1000000000000 : ℝ)*(f.sum) + (2411017859611349/5000000000000000000000000000 : ℝ)*base62 + (890702832101459/1000000000000000000000000000 : ℝ)*base65 + (453659130095339/1250000000000000000000000000 : ℝ)*base67 + (56433371970339/1250000000000000000000000000 : ℝ)*base69 + (4214221101833537/5000000000000000000000000000 : ℝ)*base71 + (417708719156199/2000000000000000000000000000 : ℝ)*base72 + (585499755601459/1000000000000000000000000000 : ℝ)*base75 + (1979865017663121/2500000000000000000000000000 : ℝ)*base77 + (6758179480018283/10000000000000000000000000000 : ℝ)*base78 + (47/312500000000000 : ℝ)*base86 + (47/312500000000000 : ℝ)*base88 + (47/312500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13471/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13471/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32786707253059555655793/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286432766337/250000000000 : ℝ)*(base7) + (3509661/1000000000000 : ℝ)*(base11) + (17498933247/100000000000 : ℝ)*(base40) + (873971/1000000000000 : ℝ)*(base43) + (33234985713/1000000000000 : ℝ)*(base50) + (697849571117/500000000000 : ℝ)*(major_s0_0) + (1395698268263/1000000000000 : ℝ)*(major_s0_1) + (697849571117/500000000000 : ℝ)*(major_s0_2) + (1520533/1000000000000 : ℝ)*(sp_s0_2) + (21227467/1000000000000 : ℝ)*(sp_s0_9) + (1427741858127/1000000000000 : ℝ)*(sp_s0_21) + (1427746241759/1000000000000 : ℝ)*(sp_s0_22) + (356930654947/250000000000 : ℝ)*(sp_s0_23) + (467232178513/250000000000 : ℝ)*(sp_s0_27) + (11299963261/15625000000 : ℝ)*(f.failure) + (1427746241759/1000000000000 : ℝ)*(f.sum) + (6758179480018283/10000000000000000000000000000 : ℝ)*base62 + (585499755601459/1000000000000000000000000000 : ℝ)*base65 + (1979865017663121/2500000000000000000000000000 : ℝ)*base67 + (453659130095339/1250000000000000000000000000 : ℝ)*base69 + (2411017859611349/5000000000000000000000000000 : ℝ)*base70 + (890702832101459/1000000000000000000000000000 : ℝ)*base73 + (417708719156199/2000000000000000000000000000 : ℝ)*base74 + (56433371970339/1250000000000000000000000000 : ℝ)*base77 + (4214221101833537/5000000000000000000000000000 : ℝ)*base79 + (47/312500000000000 : ℝ)*base86 + (47/312500000000000 : ℝ)*base88 + (47/312500000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (13471/20000 : ℝ) ^ (41/8 : ℝ) ≤ (6597287900317976193/50000000000000000000 : ℝ) := by
    have hpowers : (13471/20000 : ℝ)^41 ≤ (6597287900317976193/50000000000000000000 : ℝ)^8 := by
      have hnat : (13471 : ℕ)^41*50000000000000000000^8 ≤ 6597287900317976193^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13471 20000 6597287900317976193 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13471/20000 : ℝ)) (X := (6597287900317976193/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (56597287900317976193/50000000000000000000 : ℝ) ≤ (2561194543718837/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (56597287900317976193/50000000000000000000 : ℝ)^8 ≤ (2561194543718837/2500000000000000 : ℝ)^41 := by
      have hnat : (56597287900317976193 : ℕ)^8*2500000000000000^41 ≤ 2561194543718837^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56597287900317976193 50000000000000000000 2561194543718837 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2561194543718837/2500000000000000 : ℝ)) (X := (56597287900317976193/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (31597287900317976193/25000000000000000000 : ℝ) ≤ (5233784283244681/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (31597287900317976193/25000000000000000000 : ℝ)^8 ≤ (5233784283244681/5000000000000000 : ℝ)^41 := by
      have hnat : (31597287900317976193 : ℕ)^8*5000000000000000^41 ≤ 5233784283244681^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31597287900317976193 25000000000000000000 5233784283244681 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5233784283244681/5000000000000000 : ℝ)) (X := (31597287900317976193/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(61194543718837/1683875000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(111395195807007/3367750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (13471/20000 : ℝ)) (alpha := (61194543718837/1683875000000000 : ℝ)) (beta := (111395195807007/3367750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13471/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(61194543718837/1683875000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(111395195807007/3367750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (13471/20000 : ℝ) ^ (41/8 : ℝ) ≤ (6597287900317976193/50000000000000000000 : ℝ) := by
    have hpowers : (13471/20000 : ℝ)^41 ≤ (6597287900317976193/50000000000000000000 : ℝ)^8 := by
      have hnat : (13471 : ℕ)^41*50000000000000000000^8 ≤ 6597287900317976193^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13471 20000 6597287900317976193 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13471/20000 : ℝ)) (X := (6597287900317976193/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (56597287900317976193/50000000000000000000 : ℝ) ≤ (2561194543718837/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (56597287900317976193/50000000000000000000 : ℝ)^8 ≤ (2561194543718837/2500000000000000 : ℝ)^41 := by
      have hnat : (56597287900317976193 : ℕ)^8*2500000000000000^41 ≤ 2561194543718837^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56597287900317976193 50000000000000000000 2561194543718837 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2561194543718837/2500000000000000 : ℝ)) (X := (56597287900317976193/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (31597287900317976193/25000000000000000000 : ℝ) ≤ (5233784283244681/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (31597287900317976193/25000000000000000000 : ℝ)^8 ≤ (5233784283244681/5000000000000000 : ℝ)^41 := by
      have hnat : (31597287900317976193 : ℕ)^8*5000000000000000^41 ≤ 5233784283244681^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31597287900317976193 25000000000000000000 5233784283244681 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5233784283244681/5000000000000000 : ℝ)) (X := (31597287900317976193/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(61194543718837/1683875000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(111395195807007/3367750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (13471/20000 : ℝ)) (alpha := (61194543718837/1683875000000000 : ℝ)) (beta := (111395195807007/3367750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (13471/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(61194543718837/1683875000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(111395195807007/3367750000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13471/20000 : ℝ) ^ (41/8 : ℝ) ≤ (6597287900317976193/50000000000000000000 : ℝ) := by
    have hpowers : (13471/20000 : ℝ)^41 ≤ (6597287900317976193/50000000000000000000 : ℝ)^8 := by
      have hnat : (13471 : ℕ)^41*50000000000000000000^8 ≤ 6597287900317976193^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13471 20000 6597287900317976193 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13471/20000 : ℝ)) (X := (6597287900317976193/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (56597287900317976193/50000000000000000000 : ℝ) ≤ (2561194543718837/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (56597287900317976193/50000000000000000000 : ℝ)^8 ≤ (2561194543718837/2500000000000000 : ℝ)^41 := by
      have hnat : (56597287900317976193 : ℕ)^8*2500000000000000^41 ≤ 2561194543718837^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56597287900317976193 50000000000000000000 2561194543718837 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2561194543718837/2500000000000000 : ℝ)) (X := (56597287900317976193/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (31597287900317976193/25000000000000000000 : ℝ) ≤ (5233784283244681/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (31597287900317976193/25000000000000000000 : ℝ)^8 ≤ (5233784283244681/5000000000000000 : ℝ)^41 := by
      have hnat : (31597287900317976193 : ℕ)^8*5000000000000000^41 ≤ 5233784283244681^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31597287900317976193 25000000000000000000 5233784283244681 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5233784283244681/5000000000000000 : ℝ)) (X := (31597287900317976193/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(61194543718837/1683875000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(111395195807007/3367750000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (13471/20000 : ℝ)) (alpha := (61194543718837/1683875000000000 : ℝ)) (beta := (111395195807007/3367750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13471/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(61194543718837/1683875000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(111395195807007/3367750000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-239460727/2500000000 : ℝ)*X 0 0+(5450209429/10000000000 : ℝ)*X 0 1+(5471917243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1367979303/2500000000 : ℝ)*X 1 0+(-957842961/10000000000 : ℝ)*X 1 1+(2725104713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2725104773/5000000000 : ℝ)*X 2 0+(683989639/1250000000 : ℝ)*X 2 1+(-95784293/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-832513557/10000000000 : ℝ)*X 0 0+(2248190843/5000000000 : ℝ)*X 0 1+(6464704711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((22691129/40000000 : ℝ)*X 1 0+(-122010013/10000000000 : ℝ)*X 1 1+(2858722931/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((66462049/156250000 : ℝ)*X 2 0+(7075100159/10000000000 : ℝ)*X 2 1+(-1889161/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3568170357/10000000000 : ℝ)*X 0 0+(515695159/1000000000 : ℝ)*X 0 1+(358660211/1000000000 : ℝ)*X 0 2+(3568170357/10000000000 : ℝ)*X 1 0+(515695159/1000000000 : ℝ)*X 1 1+(358660211/1000000000 : ℝ)*X 1 2+(3568170357/10000000000 : ℝ)*X 2 0+(515695159/1000000000 : ℝ)*X 2 1+(358660211/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1889161/312500000 : ℝ)*X 0 0+(66462049/156250000 : ℝ)*X 0 1+(7075100159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6464704711/10000000000 : ℝ)*X 1 0+(-832513557/10000000000 : ℝ)*X 1 1+(2248190843/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2858722931/5000000000 : ℝ)*X 2 0+(22691129/40000000 : ℝ)*X 2 1+(-122010013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((358660211/1000000000 : ℝ)*X 0 0+(3568170357/10000000000 : ℝ)*X 0 1+(515695159/1000000000 : ℝ)*X 0 2+(358660211/1000000000 : ℝ)*X 1 0+(3568170357/10000000000 : ℝ)*X 1 1+(515695159/1000000000 : ℝ)*X 1 2+(358660211/1000000000 : ℝ)*X 2 0+(3568170357/10000000000 : ℝ)*X 2 1+(515695159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-122010013/10000000000 : ℝ)*X 0 0+(2858722931/5000000000 : ℝ)*X 0 1+(22691129/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7075100159/10000000000 : ℝ)*X 1 0+(-1889161/312500000 : ℝ)*X 1 1+(66462049/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2248190843/5000000000 : ℝ)*X 2 0+(6464704711/10000000000 : ℝ)*X 2 1+(-832513557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((515695159/1000000000 : ℝ)*X 0 0+(358660211/1000000000 : ℝ)*X 0 1+(3568170357/10000000000 : ℝ)*X 0 2+(515695159/1000000000 : ℝ)*X 1 0+(358660211/1000000000 : ℝ)*X 1 1+(3568170357/10000000000 : ℝ)*X 1 2+(515695159/1000000000 : ℝ)*X 2 0+(358660211/1000000000 : ℝ)*X 2 1+(3568170357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322087_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((19767/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19767/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53725857634571999131551/3367750000000000000000000000 : ℝ) := by norm_num
    linear_combination (4181439/500000000000 : ℝ)*(base19) + (5441247/250000000000 : ℝ)*(base23) + (384789414561/1000000000000 : ℝ)*(base50) + (89131548741/250000000000 : ℝ)*(base60) + (1790266515529/500000000000 : ℝ)*(major_s1_0) + (1790266515529/500000000000 : ℝ)*(major_s1_1) + (1790266515529/500000000000 : ℝ)*(major_s1_2) + (1275703/62500000000 : ℝ)*(sp_s1_1) + (5305718751631/1000000000000 : ℝ)*(sp_s1_7) + (5305737379359/1000000000000 : ℝ)*(sp_s1_8) + (1326433936017/250000000000 : ℝ)*(sp_s1_9) + (1855294590941/1000000000000 : ℝ)*(sp_s1_13) + (47401853/1000000000000 : ℝ)*(sp_s1_14) + (8644429/1000000000000 : ℝ)*(sp_s1_23) + (1855294590941/1000000000000 : ℝ)*(f.failure) + (1061153230697/200000000000 : ℝ)*(f.sum) + (84788223105331/420968750000000000000000000 : ℝ)*base63 + (1501627865972403/1683875000000000000000000000 : ℝ)*base65 + (658716491846571/1683875000000000000000000000 : ℝ)*base67 + (1504337549642733/3367750000000000000000000000 : ℝ)*base68 + (1883652007406373/3367750000000000000000000000 : ℝ)*base71 + (500062290772503/1683875000000000000000000000 : ℝ)*base73 + (1059325294608181/3367750000000000000000000000 : ℝ)*base75 + (737996696256817/3367750000000000000000000000 : ℝ)*base77 + (499556495349777/3367750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (9641/10000000000000000 : ℝ)*base86 + (9641/10000000000000000 : ℝ)*base88 + (9641/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((19767/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(19767/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53725897957675753356513/3367750000000000000000000000 : ℝ) := by norm_num
    linear_combination (5441247/250000000000 : ℝ)*(base13) + (4181439/500000000000 : ℝ)*(base21) + (89131548741/250000000000 : ℝ)*(base40) + (384789414561/1000000000000 : ℝ)*(base60) + (1790266515529/500000000000 : ℝ)*(major_s1_0) + (1790266515529/500000000000 : ℝ)*(major_s1_1) + (1790266515529/500000000000 : ℝ)*(major_s1_2) + (20411249/1000000000000 : ℝ)*(sp_s1_2) + (8644429/1000000000000 : ℝ)*(sp_s1_7) + (1326433936017/250000000000 : ℝ)*(sp_s1_14) + (5305718751631/1000000000000 : ℝ)*(sp_s1_15) + (2652868689679/500000000000 : ℝ)*(sp_s1_16) + (927647295471/500000000000 : ℝ)*(sp_s1_20) + (47401853/1000000000000 : ℝ)*(sp_s1_22) + (927647295471/500000000000 : ℝ)*(f.failure) + (1061153230697/200000000000 : ℝ)*(f.sum) + (1707434420945027/3367750000000000000000000000 : ℝ)*base62 + (71172638685247/1683875000000000000000000000 : ℝ)*base64 + (998735675465433/3367750000000000000000000000 : ℝ)*base66 + (27388764524473/841937500000000000000000000 : ℝ)*base69 + (523364787136027/3367750000000000000000000000 : ℝ)*base70 + (316630840055639/841937500000000000000000000 : ℝ)*base73 + (14728665611771/52621093750000000000000000 : ℝ)*base74 + (975480980125729/1683875000000000000000000000 : ℝ)*base76 + (107656663452799/1683875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (4829/5000000000000000 : ℝ)*base87 + (4829/5000000000000000 : ℝ)*base89 + (4829/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19767/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19767/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10745172723892936550457/673550000000000000000000000 : ℝ) := by norm_num
    linear_combination (8362879/1000000000000 : ℝ)*(base11) + (5441247/250000000000 : ℝ)*(base15) + (384789414561/1000000000000 : ℝ)*(base40) + (89131548741/250000000000 : ℝ)*(base50) + (1790266515529/500000000000 : ℝ)*(major_s1_0) + (1790266515529/500000000000 : ℝ)*(major_s1_1) + (1790266515529/500000000000 : ℝ)*(major_s1_2) + (20411249/1000000000000 : ℝ)*(sp_s1_0) + (47401853/1000000000000 : ℝ)*(sp_s1_9) + (8644429/1000000000000 : ℝ)*(sp_s1_15) + (5305737379357/1000000000000 : ℝ)*(sp_s1_21) + (1326433936017/250000000000 : ℝ)*(sp_s1_22) + (5305718751631/1000000000000 : ℝ)*(sp_s1_23) + (1855294590941/1000000000000 : ℝ)*(sp_s1_27) + (1855294590941/1000000000000 : ℝ)*(f.failure) + (1061153230697/200000000000 : ℝ)*(f.sum) + (1759727812096323/3367750000000000000000000000 : ℝ)*base63 + (372756032691969/3367750000000000000000000000 : ℝ)*base64 + (130333032966121/1683875000000000000000000000 : ℝ)*base67 + (737996696256817/3367750000000000000000000000 : ℝ)*base69 + (499556495349777/3367750000000000000000000000 : ℝ)*base70 + (1059325294608181/3367750000000000000000000000 : ℝ)*base73 + (1501627865972403/1683875000000000000000000000 : ℝ)*base75 + (658716491846571/1683875000000000000000000000 : ℝ)*base77 + (84788223105331/420968750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (9641/10000000000000000 : ℝ)*base86 + (9641/10000000000000000 : ℝ)*base88 + (9641/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p022_positive87 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 87=![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c322087 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
  apply positive_chart_tailratio hX (by decide)
  intro j
  have hn := positive_chart_nonnegative hX j j
  fin_cases j
  · change 0 ≤ pair X 0 0 at hn
    change pair X 0 1 ≤ (2/5:ℝ)*pair X 0 0
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.1,hn]
  · change 0 ≤ pair X 1 1 at hn
    change pair X 1 2 ≤ (2/5:ℝ)*pair X 1 1
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.1,hn]
  · change 0 ≤ pair X 2 2 at hn
    change pair X 2 0 ≤ (2/5:ℝ)*pair X 2 2
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.2,hn]

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_positive87 p hpa hpb X hX

#print axioms solution
