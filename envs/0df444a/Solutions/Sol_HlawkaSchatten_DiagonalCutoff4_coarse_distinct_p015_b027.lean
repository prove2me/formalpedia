-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:02.802221+00:00
-- url     : https://prove2.me/submissions/cbec7380-84da-4abf-a081-85024176836f

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
theorem collision_support_c315068_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3781665503/5000000000 : ℝ)*x 0 + (2732703129/10000000000 : ℝ)*x 1 + (-841195419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3781665503/5000000000 : ℝ)^19 ≤ (35102652965897/50000000000000 : ℝ)^15 := by
    have hnat : (3781665503 : ℕ)^19*50000000000000^15 ≤ 35102652965897^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781665503 5000000000 35102652965897 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732703129/10000000000 : ℝ)^19 ≤ (773411157651/4000000000000 : ℝ)^15 := by
    have hnat : (2732703129 : ℕ)^19*4000000000000^15 ≤ 773411157651^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732703129 10000000000 773411157651 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (841195419/5000000000 : ℝ)^19 ≤ (10459415118103/100000000000000 : ℝ)^15 := by
    have hnat : (841195419 : ℕ)^19*100000000000000^15 ≤ 10459415118103^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841195419 5000000000 10459415118103 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3781665503/5000000000 : ℝ), (2732703129/10000000000 : ℝ), (-841195419/5000000000 : ℝ)] ![(35102652965897/50000000000000 : ℝ), (773411157651/4000000000000 : ℝ), (10459415118103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3781665503/5000000000 : ℝ)|^19 ≤ (35102652965897/50000000000000 : ℝ)^15
        have hw : |(3781665503/5000000000 : ℝ)|=(3781665503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732703129/10000000000 : ℝ)|^19 ≤ (773411157651/4000000000000 : ℝ)^15
        have hw : |(2732703129/10000000000 : ℝ)|=(2732703129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-841195419/5000000000 : ℝ)|^19 ≤ (10459415118103/100000000000000 : ℝ)^15
        have hw : |(-841195419/5000000000 : ℝ)|=(841195419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4082929353/10000000000 : ℝ)*x 0 + (-273661387/625000000 : ℝ)*x 1 + (82782729/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4082929353/10000000000 : ℝ)^19 ≤ (32153705485151/100000000000000 : ℝ)^15 := by
    have hnat : (4082929353 : ℕ)^19*100000000000000^15 ≤ 32153705485151^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082929353 10000000000 32153705485151 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273661387/625000000 : ℝ)^19 ≤ (8782721607419/25000000000000 : ℝ)^15 := by
    have hnat : (273661387 : ℕ)^19*25000000000000^15 ≤ 8782721607419^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273661387 625000000 8782721607419 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82782729/200000000 : ℝ)^19 ≤ (1022356502213/3125000000000 : ℝ)^15 := by
    have hnat : (82782729 : ℕ)^19*3125000000000^15 ≤ 1022356502213^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82782729 200000000 1022356502213 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4082929353/10000000000 : ℝ), (-273661387/625000000 : ℝ), (82782729/200000000 : ℝ)] ![(32153705485151/100000000000000 : ℝ), (8782721607419/25000000000000 : ℝ), (1022356502213/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4082929353/10000000000 : ℝ)|^19 ≤ (32153705485151/100000000000000 : ℝ)^15
        have hw : |(4082929353/10000000000 : ℝ)|=(4082929353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273661387/625000000 : ℝ)|^19 ≤ (8782721607419/25000000000000 : ℝ)^15
        have hw : |(-273661387/625000000 : ℝ)|=(273661387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82782729/200000000 : ℝ)|^19 ≤ (1022356502213/3125000000000 : ℝ)^15
        have hw : |(82782729/200000000 : ℝ)|=(82782729/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-581797243/10000000000 : ℝ)*x 0 + (-1380936071/2500000000 : ℝ)*x 1 + (-724602561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (581797243/10000000000 : ℝ)^19 ≤ (2725068569021/100000000000000 : ℝ)^15 := by
    have hnat : (581797243 : ℕ)^19*100000000000000^15 ≤ 2725068569021^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581797243 10000000000 2725068569021 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380936071/2500000000 : ℝ)^19 ≤ (11787884119427/25000000000000 : ℝ)^15 := by
    have hnat : (1380936071 : ℕ)^19*25000000000000^15 ≤ 11787884119427^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380936071 2500000000 11787884119427 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (724602561/1250000000 : ℝ)^19 ≤ (12530848733529/25000000000000 : ℝ)^15 := by
    have hnat : (724602561 : ℕ)^19*25000000000000^15 ≤ 12530848733529^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724602561 1250000000 12530848733529 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-581797243/10000000000 : ℝ), (-1380936071/2500000000 : ℝ), (-724602561/1250000000 : ℝ)] ![(2725068569021/100000000000000 : ℝ), (11787884119427/25000000000000 : ℝ), (12530848733529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-581797243/10000000000 : ℝ)|^19 ≤ (2725068569021/100000000000000 : ℝ)^15
        have hw : |(-581797243/10000000000 : ℝ)|=(581797243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1380936071/2500000000 : ℝ)|^19 ≤ (11787884119427/25000000000000 : ℝ)^15
        have hw : |(-1380936071/2500000000 : ℝ)|=(1380936071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-724602561/1250000000 : ℝ)|^19 ≤ (12530848733529/25000000000000 : ℝ)^15
        have hw : |(-724602561/1250000000 : ℝ)|=(724602561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1526009091/2000000000 : ℝ)*x 0 + (3188555499/10000000000 : ℝ)*x 1 + (-506516509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526009091/2000000000 : ℝ)^19 ≤ (3549531458921/5000000000000 : ℝ)^15 := by
    have hnat : (1526009091 : ℕ)^19*5000000000000^15 ≤ 3549531458921^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526009091 2000000000 3549531458921 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188555499/10000000000 : ℝ)^19 ≤ (23508181876311/100000000000000 : ℝ)^15 := by
    have hnat : (3188555499 : ℕ)^19*100000000000000^15 ≤ 23508181876311^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188555499 10000000000 23508181876311 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506516509/5000000000 : ℝ)^19 ≤ (2750594467677/50000000000000 : ℝ)^15 := by
    have hnat : (506516509 : ℕ)^19*50000000000000^15 ≤ 2750594467677^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506516509 5000000000 2750594467677 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1526009091/2000000000 : ℝ), (3188555499/10000000000 : ℝ), (-506516509/5000000000 : ℝ)] ![(3549531458921/5000000000000 : ℝ), (23508181876311/100000000000000 : ℝ), (2750594467677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1526009091/2000000000 : ℝ)|^19 ≤ (3549531458921/5000000000000 : ℝ)^15
        have hw : |(1526009091/2000000000 : ℝ)|=(1526009091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3188555499/10000000000 : ℝ)|^19 ≤ (23508181876311/100000000000000 : ℝ)^15
        have hw : |(3188555499/10000000000 : ℝ)|=(3188555499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506516509/5000000000 : ℝ)|^19 ≤ (2750594467677/50000000000000 : ℝ)^15
        have hw : |(-506516509/5000000000 : ℝ)|=(506516509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (916411181/2000000000 : ℝ)*x 0 + (-3083099773/10000000000 : ℝ)*x 1 + (4876017179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (916411181/2000000000 : ℝ)^19 ≤ (37211440803589/100000000000000 : ℝ)^15 := by
    have hnat : (916411181 : ℕ)^19*100000000000000^15 ≤ 37211440803589^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916411181 2000000000 37211440803589 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3083099773/10000000000 : ℝ)^19 ≤ (11263869358187/50000000000000 : ℝ)^15 := by
    have hnat : (3083099773 : ℕ)^19*50000000000000^15 ≤ 11263869358187^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3083099773 10000000000 11263869358187 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4876017179/10000000000 : ℝ)^19 ≤ (20130410227711/50000000000000 : ℝ)^15 := by
    have hnat : (4876017179 : ℕ)^19*50000000000000^15 ≤ 20130410227711^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876017179 10000000000 20130410227711 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(916411181/2000000000 : ℝ), (-3083099773/10000000000 : ℝ), (4876017179/10000000000 : ℝ)] ![(37211440803589/100000000000000 : ℝ), (11263869358187/50000000000000 : ℝ), (20130410227711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(916411181/2000000000 : ℝ)|^19 ≤ (37211440803589/100000000000000 : ℝ)^15
        have hw : |(916411181/2000000000 : ℝ)|=(916411181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3083099773/10000000000 : ℝ)|^19 ≤ (11263869358187/50000000000000 : ℝ)^15
        have hw : |(-3083099773/10000000000 : ℝ)|=(3083099773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4876017179/10000000000 : ℝ)|^19 ≤ (20130410227711/50000000000000 : ℝ)^15
        have hw : |(4876017179/10000000000 : ℝ)|=(4876017179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-222343787/10000000000 : ℝ)*x 0 + (-2179182013/5000000000 : ℝ)*x 1 + (-56430047/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222343787/10000000000 : ℝ)^19 ≤ (805808166781/100000000000000 : ℝ)^15 := by
    have hnat : (222343787 : ℕ)^19*100000000000000^15 ≤ 805808166781^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222343787 10000000000 805808166781 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179182013/5000000000 : ℝ)^19 ≤ (34925537740377/100000000000000 : ℝ)^15 := by
    have hnat : (2179182013 : ℕ)^19*100000000000000^15 ≤ 34925537740377^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179182013 5000000000 34925537740377 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56430047/80000000 : ℝ)^19 ≤ (64268654083831/100000000000000 : ℝ)^15 := by
    have hnat : (56430047 : ℕ)^19*100000000000000^15 ≤ 64268654083831^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56430047 80000000 64268654083831 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222343787/10000000000 : ℝ), (-2179182013/5000000000 : ℝ), (-56430047/80000000 : ℝ)] ![(805808166781/100000000000000 : ℝ), (34925537740377/100000000000000 : ℝ), (64268654083831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222343787/10000000000 : ℝ)|^19 ≤ (805808166781/100000000000000 : ℝ)^15
        have hw : |(-222343787/10000000000 : ℝ)|=(222343787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179182013/5000000000 : ℝ)|^19 ≤ (34925537740377/100000000000000 : ℝ)^15
        have hw : |(-2179182013/5000000000 : ℝ)|=(2179182013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56430047/80000000 : ℝ)|^19 ≤ (64268654083831/100000000000000 : ℝ)^15
        have hw : |(-56430047/80000000 : ℝ)|=(56430047/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8742459141/10000000000 : ℝ)*x 0 + (247497897/1250000000 : ℝ)*x 1 + (-593907481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8742459141/10000000000 : ℝ)^19 ≤ (10543365299663/12500000000000 : ℝ)^15 := by
    have hnat : (8742459141 : ℕ)^19*12500000000000^15 ≤ 10543365299663^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8742459141 10000000000 10543365299663 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247497897/1250000000 : ℝ)^19 ≤ (12855961605801/100000000000000 : ℝ)^15 := by
    have hnat : (247497897 : ℕ)^19*100000000000000^15 ≤ 12855961605801^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247497897 1250000000 12855961605801 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593907481/10000000000 : ℝ)^19 ≤ (2797115981767/100000000000000 : ℝ)^15 := by
    have hnat : (593907481 : ℕ)^19*100000000000000^15 ≤ 2797115981767^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593907481 10000000000 2797115981767 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8742459141/10000000000 : ℝ), (247497897/1250000000 : ℝ), (-593907481/10000000000 : ℝ)] ![(10543365299663/12500000000000 : ℝ), (12855961605801/100000000000000 : ℝ), (2797115981767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8742459141/10000000000 : ℝ)|^19 ≤ (10543365299663/12500000000000 : ℝ)^15
        have hw : |(8742459141/10000000000 : ℝ)|=(8742459141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(247497897/1250000000 : ℝ)|^19 ≤ (12855961605801/100000000000000 : ℝ)^15
        have hw : |(247497897/1250000000 : ℝ)|=(247497897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-593907481/10000000000 : ℝ)|^19 ≤ (2797115981767/100000000000000 : ℝ)^15
        have hw : |(-593907481/10000000000 : ℝ)|=(593907481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4511522413/10000000000 : ℝ)*x 0 + (-566928681/1250000000 : ℝ)*x 1 + (706811551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4511522413/10000000000 : ℝ)^19 ≤ (4560921849333/12500000000000 : ℝ)^15 := by
    have hnat : (4511522413 : ℕ)^19*12500000000000^15 ≤ 4560921849333^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511522413 10000000000 4560921849333 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566928681/1250000000 : ℝ)^19 ≤ (4591557274767/12500000000000 : ℝ)^15 := by
    have hnat : (566928681 : ℕ)^19*12500000000000^15 ≤ 4591557274767^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566928681 1250000000 4591557274767 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706811551/2000000000 : ℝ)^19 ≤ (836880218281/3125000000000 : ℝ)^15 := by
    have hnat : (706811551 : ℕ)^19*3125000000000^15 ≤ 836880218281^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706811551 2000000000 836880218281 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4511522413/10000000000 : ℝ), (-566928681/1250000000 : ℝ), (706811551/2000000000 : ℝ)] ![(4560921849333/12500000000000 : ℝ), (4591557274767/12500000000000 : ℝ), (836880218281/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4511522413/10000000000 : ℝ)|^19 ≤ (4560921849333/12500000000000 : ℝ)^15
        have hw : |(4511522413/10000000000 : ℝ)|=(4511522413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566928681/1250000000 : ℝ)|^19 ≤ (4591557274767/12500000000000 : ℝ)^15
        have hw : |(-566928681/1250000000 : ℝ)|=(566928681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706811551/2000000000 : ℝ)|^19 ≤ (836880218281/3125000000000 : ℝ)^15
        have hw : |(706811551/2000000000 : ℝ)|=(706811551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2563836571/10000000000 : ℝ)*x 0 + (-2570908299/10000000000 : ℝ)*x 1 + (-56430047/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2563836571/10000000000 : ℝ)^19 ≤ (3566901287483/20000000000000 : ℝ)^15 := by
    have hnat : (2563836571 : ℕ)^19*20000000000000^15 ≤ 3566901287483^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563836571 10000000000 3566901287483 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570908299/10000000000 : ℝ)^19 ≤ (17896839466139/100000000000000 : ℝ)^15 := by
    have hnat : (2570908299 : ℕ)^19*100000000000000^15 ≤ 17896839466139^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570908299 10000000000 17896839466139 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56430047/80000000 : ℝ)^19 ≤ (64268654083831/100000000000000 : ℝ)^15 := by
    have hnat : (56430047 : ℕ)^19*100000000000000^15 ≤ 64268654083831^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56430047 80000000 64268654083831 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2563836571/10000000000 : ℝ), (-2570908299/10000000000 : ℝ), (-56430047/80000000 : ℝ)] ![(3566901287483/20000000000000 : ℝ), (17896839466139/100000000000000 : ℝ), (64268654083831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2563836571/10000000000 : ℝ)|^19 ≤ (3566901287483/20000000000000 : ℝ)^15
        have hw : |(2563836571/10000000000 : ℝ)|=(2563836571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2570908299/10000000000 : ℝ)|^19 ≤ (17896839466139/100000000000000 : ℝ)^15
        have hw : |(-2570908299/10000000000 : ℝ)|=(2570908299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56430047/80000000 : ℝ)|^19 ≤ (64268654083831/100000000000000 : ℝ)^15
        have hw : |(-56430047/80000000 : ℝ)|=(56430047/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-190685059/10000000000 : ℝ)*x 0 + (-6246736243/10000000000 : ℝ)*x 1 + (-2626126029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190685059/10000000000 : ℝ)^19 ≤ (331668668543/50000000000000 : ℝ)^15 := by
    have hnat : (190685059 : ℕ)^19*50000000000000^15 ≤ 331668668543^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190685059 10000000000 331668668543 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6246736243/10000000000 : ℝ)^19 ≤ (55101152259553/100000000000000 : ℝ)^15 := by
    have hnat : (6246736243 : ℕ)^19*100000000000000^15 ≤ 55101152259553^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6246736243 10000000000 55101152259553 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626126029/5000000000 : ℝ)^19 ≤ (8847102078409/20000000000000 : ℝ)^15 := by
    have hnat : (2626126029 : ℕ)^19*20000000000000^15 ≤ 8847102078409^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626126029 5000000000 8847102078409 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190685059/10000000000 : ℝ), (-6246736243/10000000000 : ℝ), (-2626126029/5000000000 : ℝ)] ![(331668668543/50000000000000 : ℝ), (55101152259553/100000000000000 : ℝ), (8847102078409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190685059/10000000000 : ℝ)|^19 ≤ (331668668543/50000000000000 : ℝ)^15
        have hw : |(-190685059/10000000000 : ℝ)|=(190685059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6246736243/10000000000 : ℝ)|^19 ≤ (55101152259553/100000000000000 : ℝ)^15
        have hw : |(-6246736243/10000000000 : ℝ)|=(6246736243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2626126029/5000000000 : ℝ)|^19 ≤ (8847102078409/20000000000000 : ℝ)^15
        have hw : |(-2626126029/5000000000 : ℝ)|=(2626126029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8913988613/10000000000 : ℝ)*x 0 + (1722455847/10000000000 : ℝ)*x 1 + (-3689239/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8913988613/10000000000 : ℝ)^19 ≤ (86448599439483/100000000000000 : ℝ)^15 := by
    have hnat : (8913988613 : ℕ)^19*100000000000000^15 ≤ 86448599439483^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8913988613 10000000000 86448599439483 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722455847/10000000000 : ℝ)^19 ≤ (5387958748029/50000000000000 : ℝ)^15 := by
    have hnat : (1722455847 : ℕ)^19*50000000000000^15 ≤ 5387958748029^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722455847 10000000000 5387958748029 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3689239/62500000 : ℝ)^19 ≤ (2775483053811/100000000000000 : ℝ)^15 := by
    have hnat : (3689239 : ℕ)^19*100000000000000^15 ≤ 2775483053811^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689239 62500000 2775483053811 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8913988613/10000000000 : ℝ), (1722455847/10000000000 : ℝ), (-3689239/62500000 : ℝ)] ![(86448599439483/100000000000000 : ℝ), (5387958748029/50000000000000 : ℝ), (2775483053811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8913988613/10000000000 : ℝ)|^19 ≤ (86448599439483/100000000000000 : ℝ)^15
        have hw : |(8913988613/10000000000 : ℝ)|=(8913988613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1722455847/10000000000 : ℝ)|^19 ≤ (5387958748029/50000000000000 : ℝ)^15
        have hw : |(1722455847/10000000000 : ℝ)|=(1722455847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3689239/62500000 : ℝ)|^19 ≤ (2775483053811/100000000000000 : ℝ)^15
        have hw : |(-3689239/62500000 : ℝ)|=(3689239/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3493359747/10000000000 : ℝ)*x 0 + (-1137299547/2500000000 : ℝ)*x 1 + (283486557/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3493359747/10000000000 : ℝ)^19 ≤ (5278025982269/20000000000000 : ℝ)^15 := by
    have hnat : (3493359747 : ℕ)^19*20000000000000^15 ≤ 5278025982269^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493359747 10000000000 5278025982269 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137299547/2500000000 : ℝ)^19 ≤ (18436882610177/50000000000000 : ℝ)^15 := by
    have hnat : (1137299547 : ℕ)^19*50000000000000^15 ≤ 18436882610177^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137299547 2500000000 18436882610177 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283486557/625000000 : ℝ)^19 ≤ (36736104848127/100000000000000 : ℝ)^15 := by
    have hnat : (283486557 : ℕ)^19*100000000000000^15 ≤ 36736104848127^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283486557 625000000 36736104848127 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3493359747/10000000000 : ℝ), (-1137299547/2500000000 : ℝ), (283486557/625000000 : ℝ)] ![(5278025982269/20000000000000 : ℝ), (18436882610177/50000000000000 : ℝ), (36736104848127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3493359747/10000000000 : ℝ)|^19 ≤ (5278025982269/20000000000000 : ℝ)^15
        have hw : |(3493359747/10000000000 : ℝ)|=(3493359747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1137299547/2500000000 : ℝ)|^19 ≤ (18436882610177/50000000000000 : ℝ)^15
        have hw : |(-1137299547/2500000000 : ℝ)|=(1137299547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283486557/625000000 : ℝ)|^19 ≤ (36736104848127/100000000000000 : ℝ)^15
        have hw : |(283486557/625000000 : ℝ)|=(283486557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s0_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9347191/25000000 : ℝ)*x 0 + (-444661761/1250000000 : ℝ)*x 1 + (-2626126029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9347191/25000000 : ℝ)^19 ≤ (28761094168727/100000000000000 : ℝ)^15 := by
    have hnat : (9347191 : ℕ)^19*100000000000000^15 ≤ 28761094168727^15*25000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9347191 25000000 28761094168727 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444661761/1250000000 : ℝ)^19 ≤ (27003395425443/100000000000000 : ℝ)^15 := by
    have hnat : (444661761 : ℕ)^19*100000000000000^15 ≤ 27003395425443^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444661761 1250000000 27003395425443 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626126029/5000000000 : ℝ)^19 ≤ (8847102078409/20000000000000 : ℝ)^15 := by
    have hnat : (2626126029 : ℕ)^19*20000000000000^15 ≤ 8847102078409^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626126029 5000000000 8847102078409 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9347191/25000000 : ℝ), (-444661761/1250000000 : ℝ), (-2626126029/5000000000 : ℝ)] ![(28761094168727/100000000000000 : ℝ), (27003395425443/100000000000000 : ℝ), (8847102078409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9347191/25000000 : ℝ)|^19 ≤ (28761094168727/100000000000000 : ℝ)^15
        have hw : |(9347191/25000000 : ℝ)|=(9347191/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444661761/1250000000 : ℝ)|^19 ≤ (27003395425443/100000000000000 : ℝ)^15
        have hw : |(-444661761/1250000000 : ℝ)|=(444661761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2626126029/5000000000 : ℝ)|^19 ≤ (8847102078409/20000000000000 : ℝ)^15
        have hw : |(-2626126029/5000000000 : ℝ)|=(2626126029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2265451539/10000000000 : ℝ)*x 0 + (-4809223997/10000000000 : ℝ)*x 1 + (-5341434417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2265451539/10000000000 : ℝ)^19 ≤ (15247409004961/100000000000000 : ℝ)^15 := by
    have hnat : (2265451539 : ℕ)^19*100000000000000^15 ≤ 15247409004961^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265451539 10000000000 15247409004961 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4809223997/10000000000 : ℝ)^19 ≤ (1582541101519/4000000000000 : ℝ)^15 := by
    have hnat : (4809223997 : ℕ)^19*4000000000000^15 ≤ 1582541101519^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809223997 10000000000 1582541101519 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5341434417/10000000000 : ℝ)^19 ≤ (22594531721373/50000000000000 : ℝ)^15 := by
    have hnat : (5341434417 : ℕ)^19*50000000000000^15 ≤ 22594531721373^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341434417 10000000000 22594531721373 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2265451539/10000000000 : ℝ), (-4809223997/10000000000 : ℝ), (-5341434417/10000000000 : ℝ)] ![(15247409004961/100000000000000 : ℝ), (1582541101519/4000000000000 : ℝ), (22594531721373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2265451539/10000000000 : ℝ)|^19 ≤ (15247409004961/100000000000000 : ℝ)^15
        have hw : |(-2265451539/10000000000 : ℝ)|=(2265451539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4809223997/10000000000 : ℝ)|^19 ≤ (1582541101519/4000000000000 : ℝ)^15
        have hw : |(-4809223997/10000000000 : ℝ)|=(4809223997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5341434417/10000000000 : ℝ)|^19 ≤ (22594531721373/50000000000000 : ℝ)^15
        have hw : |(-5341434417/10000000000 : ℝ)|=(5341434417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (246966461/400000000 : ℝ)*x 0 + (817406109/2500000000 : ℝ)*x 1 + (-185314763/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246966461/400000000 : ℝ)^19 ≤ (13572883630949/25000000000000 : ℝ)^15 := by
    have hnat : (246966461 : ℕ)^19*25000000000000^15 ≤ 13572883630949^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246966461 400000000 13572883630949 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (817406109/2500000000 : ℝ)^19 ≤ (24267812786917/100000000000000 : ℝ)^15 := by
    have hnat : (817406109 : ℕ)^19*100000000000000^15 ≤ 24267812786917^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817406109 2500000000 24267812786917 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185314763/625000000 : ℝ)^19 ≤ (21440652671129/100000000000000 : ℝ)^15 := by
    have hnat : (185314763 : ℕ)^19*100000000000000^15 ≤ 21440652671129^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185314763 625000000 21440652671129 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(246966461/400000000 : ℝ), (817406109/2500000000 : ℝ), (-185314763/625000000 : ℝ)] ![(13572883630949/25000000000000 : ℝ), (24267812786917/100000000000000 : ℝ), (21440652671129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(246966461/400000000 : ℝ)|^19 ≤ (13572883630949/25000000000000 : ℝ)^15
        have hw : |(246966461/400000000 : ℝ)|=(246966461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(817406109/2500000000 : ℝ)|^19 ≤ (24267812786917/100000000000000 : ℝ)^15
        have hw : |(817406109/2500000000 : ℝ)|=(817406109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-185314763/625000000 : ℝ)|^19 ≤ (21440652671129/100000000000000 : ℝ)^15
        have hw : |(-185314763/625000000 : ℝ)|=(185314763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (519308767/1250000000 : ℝ)*x 0 + (-885751569/2000000000 : ℝ)*x 1 + (31376471/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519308767/1250000000 : ℝ)^19 ≤ (1027156221041/3125000000000 : ℝ)^15 := by
    have hnat : (519308767 : ℕ)^19*3125000000000^15 ≤ 1027156221041^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519308767 1250000000 1027156221041 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885751569/2000000000 : ℝ)^19 ≤ (35641593872697/100000000000000 : ℝ)^15 := by
    have hnat : (885751569 : ℕ)^19*100000000000000^15 ≤ 35641593872697^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885751569 2000000000 35641593872697 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31376471/78125000 : ℝ)^19 ≤ (15744703519759/50000000000000 : ℝ)^15 := by
    have hnat : (31376471 : ℕ)^19*50000000000000^15 ≤ 15744703519759^15*78125000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31376471 78125000 15744703519759 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519308767/1250000000 : ℝ), (-885751569/2000000000 : ℝ), (31376471/78125000 : ℝ)] ![(1027156221041/3125000000000 : ℝ), (35641593872697/100000000000000 : ℝ), (15744703519759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519308767/1250000000 : ℝ)|^19 ≤ (1027156221041/3125000000000 : ℝ)^15
        have hw : |(519308767/1250000000 : ℝ)|=(519308767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885751569/2000000000 : ℝ)|^19 ≤ (35641593872697/100000000000000 : ℝ)^15
        have hw : |(-885751569/2000000000 : ℝ)|=(885751569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31376471/78125000 : ℝ)|^19 ≤ (15744703519759/50000000000000 : ℝ)^15
        have hw : |(31376471/78125000 : ℝ)|=(31376471/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315068_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3904365133/10000000000 : ℝ)*x 0 + (-2058705617/5000000000 : ℝ)*x 1 + (-4573062533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3904365133/10000000000 : ℝ)^19 ≤ (1898937000041/6250000000000 : ℝ)^15 := by
    have hnat : (3904365133 : ℕ)^19*6250000000000^15 ≤ 1898937000041^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3904365133 10000000000 1898937000041 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058705617/5000000000 : ℝ)^19 ≤ (8124513896059/25000000000000 : ℝ)^15 := by
    have hnat : (2058705617 : ℕ)^19*25000000000000^15 ≤ 8124513896059^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058705617 5000000000 8124513896059 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4573062533/10000000000 : ℝ)^19 ≤ (3711895240103/10000000000000 : ℝ)^15 := by
    have hnat : (4573062533 : ℕ)^19*10000000000000^15 ≤ 3711895240103^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573062533 10000000000 3711895240103 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3904365133/10000000000 : ℝ), (-2058705617/5000000000 : ℝ), (-4573062533/10000000000 : ℝ)] ![(1898937000041/6250000000000 : ℝ), (8124513896059/25000000000000 : ℝ), (3711895240103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3904365133/10000000000 : ℝ)|^19 ≤ (1898937000041/6250000000000 : ℝ)^15
        have hw : |(3904365133/10000000000 : ℝ)|=(3904365133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058705617/5000000000 : ℝ)|^19 ≤ (8124513896059/25000000000000 : ℝ)^15
        have hw : |(-2058705617/5000000000 : ℝ)|=(2058705617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4573062533/10000000000 : ℝ)|^19 ≤ (3711895240103/10000000000000 : ℝ)^15
        have hw : |(-4573062533/10000000000 : ℝ)|=(4573062533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315068 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3781665503/5000000000 : ℝ)*X 1 0+(2732703129/10000000000 : ℝ)*X 1 1+(-841195419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4082929353/10000000000 : ℝ)*X 2 0+(-273661387/625000000 : ℝ)*X 2 1+(82782729/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-581797243/10000000000 : ℝ)*X 0 0+(-1380936071/2500000000 : ℝ)*X 0 1+(-724602561/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1526009091/2000000000 : ℝ)*X 1 0+(3188555499/10000000000 : ℝ)*X 1 1+(-506516509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((916411181/2000000000 : ℝ)*X 2 0+(-3083099773/10000000000 : ℝ)*X 2 1+(4876017179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-222343787/10000000000 : ℝ)*X 0 0+(-2179182013/5000000000 : ℝ)*X 0 1+(-56430047/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8742459141/10000000000 : ℝ)*X 1 0+(247497897/1250000000 : ℝ)*X 1 1+(-593907481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4511522413/10000000000 : ℝ)*X 2 0+(-566928681/1250000000 : ℝ)*X 2 1+(706811551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2563836571/10000000000 : ℝ)*X 0 0+(-2570908299/10000000000 : ℝ)*X 0 1+(-56430047/80000000 : ℝ)*X 0 2+(2563836571/10000000000 : ℝ)*X 1 0+(-2570908299/10000000000 : ℝ)*X 1 1+(-56430047/80000000 : ℝ)*X 1 2+(2563836571/10000000000 : ℝ)*X 2 0+(-2570908299/10000000000 : ℝ)*X 2 1+(-56430047/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-190685059/10000000000 : ℝ)*X 0 0+(-6246736243/10000000000 : ℝ)*X 0 1+(-2626126029/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8913988613/10000000000 : ℝ)*X 1 0+(1722455847/10000000000 : ℝ)*X 1 1+(-3689239/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3493359747/10000000000 : ℝ)*X 2 0+(-1137299547/2500000000 : ℝ)*X 2 1+(283486557/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((9347191/25000000 : ℝ)*X 0 0+(-444661761/1250000000 : ℝ)*X 0 1+(-2626126029/5000000000 : ℝ)*X 0 2+(9347191/25000000 : ℝ)*X 1 0+(-444661761/1250000000 : ℝ)*X 1 1+(-2626126029/5000000000 : ℝ)*X 1 2+(9347191/25000000 : ℝ)*X 2 0+(-444661761/1250000000 : ℝ)*X 2 1+(-2626126029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((17529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (886259079319433642673/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (142944582101/100000000000 : ℝ)*(base1) + (117131195191/62500000000 : ℝ)*(base39) + (213432128707/500000000000 : ℝ)*(base49) + (42701/25000000000 : ℝ)*(base60) + (2496655776517/1000000000000 : ℝ)*(major_s0_0) + (2496655776517/1000000000000 : ℝ)*(major_s0_1) + (2496655776517/1000000000000 : ℝ)*(major_s0_2) + (5562259/125000000000 : ℝ)*(sp_s0_1) + (4993287008727/1000000000000 : ℝ)*(sp_s0_7) + (1781909671631/500000000000 : ℝ)*(sp_s0_8) + (142553334789/40000000000 : ℝ)*(sp_s0_9) + (173617/20000000000 : ℝ)*(sp_s0_14) + (13972767/1000000000000 : ℝ)*(sp_s0_21) + (30471609/1000000000000 : ℝ)*(sp_s0_23) + (142944582101/100000000000 : ℝ)*(f.failure) + (1781931920667/500000000000 : ℝ)*(f.sum) + (103789727512039/156250000000000000000000000 : ℝ)*base62 + (1476207223155847/5000000000000000000000000000 : ℝ)*base64 + (976534520729401/5000000000000000000000000000 : ℝ)*base67 + (1549133335729401/5000000000000000000000000000 : ℝ)*base68 + (60918975793289/156250000000000000000000000 : ℝ)*base70 + (2344533223655847/5000000000000000000000000000 : ℝ)*base73 + (678588221655847/5000000000000000000000000000 : ℝ)*base74 + (352327556229401/5000000000000000000000000000 : ℝ)*base76 + (2825283321177/4882812500000000000000000 : ℝ)*base79 + (8559/10000000000000000 : ℝ)*base87 + (8559/10000000000000000 : ℝ)*base89 + (8559/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-12273/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-12273/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (537109881280452047307/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1197310852111/1000000000000 : ℝ)*(base1) + (4325969/1000000000000 : ℝ)*(base21) + (2462037574129/1000000000000 : ℝ)*(base39) + (722504146481/1000000000000 : ℝ)*(base49) + (629328860281/1000000000000 : ℝ)*(base60) + (497241349229/125000000000 : ℝ)*(major_s0_0) + (497241349229/125000000000 : ℝ)*(major_s0_1) + (497241349229/125000000000 : ℝ)*(major_s0_2) + (111107/6250000000 : ℝ)*(sp_s0_8) + (6524679/250000000000 : ℝ)*(sp_s0_9) + (687562888551/100000000000 : ℝ)*(sp_s0_14) + (5678300256279/1000000000000 : ℝ)*(sp_s0_15) + (2839143804357/500000000000 : ℝ)*(sp_s0_16) + (540115205241/500000000000 : ℝ)*(sp_s0_20) + (2277541262593/1000000000000 : ℝ)*(f.failure) + (5678318033399/1000000000000 : ℝ)*(f.sum) + (22353591328089/39062500000000000000000000 : ℝ)*base63 + (27392542571561/625000000000000000000000000 : ℝ)*base65 + (72990620552863/625000000000000000000000000 : ℝ)*base66 + (335204985490363/625000000000000000000000000 : ℝ)*base69 + (20645901296803/78125000000000000000000000 : ℝ)*base71 + (129882862865939/625000000000000000000000000 : ℝ)*base73 + (474504076196561/625000000000000000000000000 : ℝ)*base75 + (74725350822137/625000000000000000000000000 : ℝ)*base76 + (9581766734411/39062500000000000000000000 : ℝ)*base79 + (30787/100000000000000000 : ℝ)*base87 + (30787/100000000000000000 : ℝ)*base89 + (30787/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-34677/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-34677/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5180922554304713309397/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (277637847/2500000000 : ℝ)*(base1) + (1336218224817/1000000000000 : ℝ)*(base39) + (622639838109/1000000000000 : ℝ)*(base49) + (1798347/125000000000 : ℝ)*(base60) + (397984962617/125000000000 : ℝ)*(major_s0_0) + (397984962617/125000000000 : ℝ)*(major_s0_1) + (397984962617/125000000000 : ℝ)*(major_s0_2) + (76101849/1000000000000 : ℝ)*(sp_s0_2) + (14488479/200000000000 : ℝ)*(sp_s0_9) + (1155374451/1000000000000 : ℝ)*(sp_s0_15) + (581987138899/125000000000 : ℝ)*(sp_s0_21) + (4543686597941/1000000000000 : ℝ)*(sp_s0_22) + (1136173357037/250000000000 : ℝ)*(sp_s0_23) + (855928382179/500000000000 : ℝ)*(sp_s0_27) + (911455951579/500000000000 : ℝ)*(f.failure) + (568105246549/125000000000 : ℝ)*(f.sum) + (5485648236307/9765625000000000000000000 : ℝ)*base62 + (180973105669053/625000000000000000000000000 : ℝ)*base65 + (310946084542701/625000000000000000000000000 : ℝ)*base67 + (356572442292701/625000000000000000000000000 : ℝ)*base68 + (49333825327787/156250000000000000000000000 : ℝ)*base70 + (173306374731553/625000000000000000000000000 : ℝ)*base72 + (357709587330947/625000000000000000000000000 : ℝ)*base74 + (143144076144799/625000000000000000000000000 : ℝ)*base77 + (88095641328463/156250000000000000000000000 : ℝ)*base78 + (36561/50000000000000000 : ℝ)*base87 + (36561/50000000000000000 : ℝ)*base89 + (36561/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (17529/100000 : ℝ) ^ (75/16 : ℝ) ≤ (28517509741809361/100000000000000000000 : ℝ) := by
    have hpowers : (17529/100000 : ℝ)^75 ≤ (28517509741809361/100000000000000000000 : ℝ)^16 := by
      have hnat : (17529 : ℕ)^75*100000000000000000000^16 ≤ 28517509741809361^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17529 100000 28517509741809361 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17529/100000 : ℝ)) (X := (28517509741809361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100028517509741809361/100000000000000000000 : ℝ) ≤ (10000608305312173/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (100028517509741809361/100000000000000000000 : ℝ)^16 ≤ (10000608305312173/10000000000000000 : ℝ)^75 := by
      have hnat : (100028517509741809361 : ℕ)^16*10000000000000000^75 ≤ 10000608305312173^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028517509741809361 100000000000000000000 10000608305312173 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000608305312173/10000000000000000 : ℝ)) (X := (100028517509741809361/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50028517509741809361/50000000000000000000 : ℝ) ≤ (2000243294842541/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (50028517509741809361/50000000000000000000 : ℝ)^16 ≤ (2000243294842541/2000000000000000 : ℝ)^75 := by
      have hnat : (50028517509741809361 : ℕ)^16*2000000000000000^75 ≤ 2000243294842541^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028517509741809361 50000000000000000000 2000243294842541 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000243294842541/2000000000000000 : ℝ)) (X := (50028517509741809361/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(202768437391/584300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(50680741711/146075000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (17529/100000 : ℝ)) (alpha := (202768437391/584300000000000 : ℝ)) (beta := (50680741711/146075000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17529/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(202768437391/584300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(50680741711/146075000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (12273/25000 : ℝ) ^ (75/16 : ℝ) ≤ (712266914917176693/20000000000000000000 : ℝ) := by
    have hpowers : (12273/25000 : ℝ)^75 ≤ (712266914917176693/20000000000000000000 : ℝ)^16 := by
      have hnat : (12273 : ℕ)^75*20000000000000000000^16 ≤ 712266914917176693^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12273 25000 712266914917176693 20000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12273/25000 : ℝ)) (X := (712266914917176693/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20712266914917176693/20000000000000000000 : ℝ) ≤ (2518733227854363/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (20712266914917176693/20000000000000000000 : ℝ)^16 ≤ (2518733227854363/2500000000000000 : ℝ)^75 := by
      have hnat : (20712266914917176693 : ℕ)^16*2500000000000000^75 ≤ 2518733227854363^75*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20712266914917176693 20000000000000000000 2518733227854363 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2518733227854363/2500000000000000 : ℝ)) (X := (20712266914917176693/20000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10712266914917176693/10000000000000000000 : ℝ) ≤ (10147865338776391/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (10712266914917176693/10000000000000000000 : ℝ)^16 ≤ (10147865338776391/10000000000000000 : ℝ)^75 := by
      have hnat : (10712266914917176693 : ℕ)^16*10000000000000000^75 ≤ 10147865338776391^75*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10712266914917176693 10000000000000000000 10147865338776391 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10147865338776391/10000000000000000 : ℝ)) (X := (10712266914917176693/10000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(18733227854363/1227300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(72932427358939/4909200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (12273/25000 : ℝ)) (alpha := (18733227854363/1227300000000000 : ℝ)) (beta := (72932427358939/4909200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (12273/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(18733227854363/1227300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(72932427358939/4909200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (34677/100000 : ℝ) ^ (75/16 : ℝ) ≤ (34907168475716749/5000000000000000000 : ℝ) := by
    have hpowers : (34677/100000 : ℝ)^75 ≤ (34907168475716749/5000000000000000000 : ℝ)^16 := by
      have hnat : (34677 : ℕ)^75*5000000000000000000^16 ≤ 34907168475716749^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34677 100000 34907168475716749 5000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34677/100000 : ℝ)) (X := (34907168475716749/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5034907168475716749/5000000000000000000 : ℝ) ≤ (10014852995818181/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (5034907168475716749/5000000000000000000 : ℝ)^16 ≤ (10014852995818181/10000000000000000 : ℝ)^75 := by
      have hnat : (5034907168475716749 : ℕ)^16*10000000000000000^75 ≤ 10014852995818181^75*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5034907168475716749 5000000000000000000 10014852995818181 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014852995818181/10000000000000000 : ℝ)) (X := (5034907168475716749/5000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2534907168475716749/2500000000000000000 : ℝ) ≤ (10029625203234587/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2534907168475716749/2500000000000000000 : ℝ)^16 ≤ (10029625203234587/10000000000000000 : ℝ)^75 := by
      have hnat : (2534907168475716749 : ℕ)^16*10000000000000000^75 ≤ 10029625203234587^75*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2534907168475716749 2500000000000000000 10029625203234587 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029625203234587/10000000000000000 : ℝ)) (X := (2534907168475716749/2500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(14852995818181/3467700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2462034569401/577950000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (34677/100000 : ℝ)) (alpha := (14852995818181/3467700000000000 : ℝ)) (beta := (2462034569401/577950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (34677/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(14852995818181/3467700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2462034569401/577950000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2265451539/10000000000 : ℝ)*X 0 0+(-4809223997/10000000000 : ℝ)*X 0 1+(-5341434417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((246966461/400000000 : ℝ)*X 1 0+(817406109/2500000000 : ℝ)*X 1 1+(-185314763/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((519308767/1250000000 : ℝ)*X 2 0+(-885751569/2000000000 : ℝ)*X 2 1+(31376471/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3904365133/10000000000 : ℝ)*X 0 0+(-2058705617/5000000000 : ℝ)*X 0 1+(-4573062533/10000000000 : ℝ)*X 0 2+(3904365133/10000000000 : ℝ)*X 1 0+(-2058705617/5000000000 : ℝ)*X 1 1+(-4573062533/10000000000 : ℝ)*X 1 2+(3904365133/10000000000 : ℝ)*X 2 0+(-2058705617/5000000000 : ℝ)*X 2 1+(-4573062533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-51053581961808305715543621345948827/6907575464175000000000000000000000 : ℝ) := by norm_num
    linear_combination (6163/500000000000 : ℝ)*(base8) + (153403/1000000000000 : ℝ)*(base21) + (400673525053/500000000000 : ℝ)*(base39) + (30393869881/125000000000 : ℝ)*(base40) + (67707/250000000000 : ℝ)*(base43) + (306688912931/1000000000000 : ℝ)*(base49) + (13847/200000000000 : ℝ)*(base59) + (157463855911/1000000000000 : ℝ)*(base60) + (174659/100000 : ℝ)*(major_s1_0) + (436647432293/250000000000 : ℝ)*(major_s1_1) + (174659/100000 : ℝ)*(major_s1_2) + (2463651506413/1000000000000 : ℝ)*(sp_s1_0) + (9623639803/3906250000 : ℝ)*(sp_s1_1) + (307956420667/125000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (9623639803/3906250000 : ℝ)*(f.sum) + (10964181655003746503/14186360700000000000000000000000 : ℝ)*base62 + (76460760675601/115590000000000000000000000 : ℝ)*base64 + (79032562887053/613650000000000000000000000 : ℝ)*base66 + (151858660189/216731250000000000000000 : ℝ)*base68 + (2597836119707759/10553005781250000000000000000 : ℝ)*base70 + (104949009357/228242187500000000000000 : ℝ)*base73 + (724193157887207/1227300000000000000000000000 : ℝ)*base74 + (849300551111/1460750000000000000000000 : ℝ)*base76 + (761348895476683483/1792778475000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c315069_s0_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-205235633/1000000000 : ℝ)*x 0 + (-1432871411/2000000000 : ℝ)*x 1 + (182288931/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205235633/1000000000 : ℝ)^19 ≤ (538162576471/4000000000000 : ℝ)^15 := by
    have hnat : (205235633 : ℕ)^19*4000000000000^15 ≤ 538162576471^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205235633 1000000000 538162576471 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1432871411/2000000000 : ℝ)^19 ≤ (65547753898909/100000000000000 : ℝ)^15 := by
    have hnat : (1432871411 : ℕ)^19*100000000000000^15 ≤ 65547753898909^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432871411 2000000000 65547753898909 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182288931/625000000 : ℝ)^19 ≤ (839927267137/4000000000000 : ℝ)^15 := by
    have hnat : (182288931 : ℕ)^19*4000000000000^15 ≤ 839927267137^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182288931 625000000 839927267137 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205235633/1000000000 : ℝ), (-1432871411/2000000000 : ℝ), (182288931/625000000 : ℝ)] ![(538162576471/4000000000000 : ℝ), (65547753898909/100000000000000 : ℝ), (839927267137/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205235633/1000000000 : ℝ)|^19 ≤ (538162576471/4000000000000 : ℝ)^15
        have hw : |(-205235633/1000000000 : ℝ)|=(205235633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1432871411/2000000000 : ℝ)|^19 ≤ (65547753898909/100000000000000 : ℝ)^15
        have hw : |(-1432871411/2000000000 : ℝ)|=(1432871411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182288931/625000000 : ℝ)|^19 ≤ (839927267137/4000000000000 : ℝ)^15
        have hw : |(182288931/625000000 : ℝ)|=(182288931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315069_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5801632599/10000000000 : ℝ)*x 0 + (2604737547/10000000000 : ℝ)*x 1 + (806032177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5801632599/10000000000 : ℝ)^19 ≤ (50176105376673/100000000000000 : ℝ)^15 := by
    have hnat : (5801632599 : ℕ)^19*100000000000000^15 ≤ 50176105376673^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5801632599 10000000000 50176105376673 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604737547/10000000000 : ℝ)^19 ≤ (9097827543133/50000000000000 : ℝ)^15 := by
    have hnat : (2604737547 : ℕ)^19*50000000000000^15 ≤ 9097827543133^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604737547 10000000000 9097827543133 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806032177/2000000000 : ℝ)^19 ≤ (15814119768063/50000000000000 : ℝ)^15 := by
    have hnat : (806032177 : ℕ)^19*50000000000000^15 ≤ 15814119768063^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806032177 2000000000 15814119768063 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5801632599/10000000000 : ℝ), (2604737547/10000000000 : ℝ), (806032177/2000000000 : ℝ)] ![(50176105376673/100000000000000 : ℝ), (9097827543133/50000000000000 : ℝ), (15814119768063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5801632599/10000000000 : ℝ)|^19 ≤ (50176105376673/100000000000000 : ℝ)^15
        have hw : |(5801632599/10000000000 : ℝ)|=(5801632599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2604737547/10000000000 : ℝ)|^19 ≤ (9097827543133/50000000000000 : ℝ)^15
        have hw : |(2604737547/10000000000 : ℝ)|=(2604737547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806032177/2000000000 : ℝ)|^19 ≤ (15814119768063/50000000000000 : ℝ)^15
        have hw : |(806032177/2000000000 : ℝ)|=(806032177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315069_s0_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3843551033/10000000000 : ℝ)*x 0 + (-401523871/1250000000 : ℝ)*x 1 + (-5462106547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3843551033/10000000000 : ℝ)^19 ≤ (29784800279289/100000000000000 : ℝ)^15 := by
    have hnat : (3843551033 : ℕ)^19*100000000000000^15 ≤ 29784800279289^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843551033 10000000000 29784800279289 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401523871/1250000000 : ℝ)^19 ≤ (2966140585877/12500000000000 : ℝ)^15 := by
    have hnat : (401523871 : ℕ)^19*12500000000000^15 ≤ 2966140585877^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401523871 1250000000 2966140585877 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462106547/10000000000 : ℝ)^19 ≤ (11621518756807/25000000000000 : ℝ)^15 := by
    have hnat : (5462106547 : ℕ)^19*25000000000000^15 ≤ 11621518756807^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462106547 10000000000 11621518756807 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3843551033/10000000000 : ℝ), (-401523871/1250000000 : ℝ), (-5462106547/10000000000 : ℝ)] ![(29784800279289/100000000000000 : ℝ), (2966140585877/12500000000000 : ℝ), (11621518756807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3843551033/10000000000 : ℝ)|^19 ≤ (29784800279289/100000000000000 : ℝ)^15
        have hw : |(3843551033/10000000000 : ℝ)|=(3843551033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401523871/1250000000 : ℝ)|^19 ≤ (2966140585877/12500000000000 : ℝ)^15
        have hw : |(-401523871/1250000000 : ℝ)|=(401523871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5462106547/10000000000 : ℝ)|^19 ≤ (11621518756807/25000000000000 : ℝ)^15
        have hw : |(-5462106547/10000000000 : ℝ)|=(5462106547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315069_s0_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5801632599/10000000000 : ℝ)*x 0 + (-2604737547/10000000000 : ℝ)*x 1 + (806032177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5801632599/10000000000 : ℝ)^19 ≤ (50176105376673/100000000000000 : ℝ)^15 := by
    have hnat : (5801632599 : ℕ)^19*100000000000000^15 ≤ 50176105376673^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5801632599 10000000000 50176105376673 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604737547/10000000000 : ℝ)^19 ≤ (9097827543133/50000000000000 : ℝ)^15 := by
    have hnat : (2604737547 : ℕ)^19*50000000000000^15 ≤ 9097827543133^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604737547 10000000000 9097827543133 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806032177/2000000000 : ℝ)^19 ≤ (15814119768063/50000000000000 : ℝ)^15 := by
    have hnat : (806032177 : ℕ)^19*50000000000000^15 ≤ 15814119768063^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806032177 2000000000 15814119768063 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5801632599/10000000000 : ℝ), (-2604737547/10000000000 : ℝ), (806032177/2000000000 : ℝ)] ![(50176105376673/100000000000000 : ℝ), (9097827543133/50000000000000 : ℝ), (15814119768063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5801632599/10000000000 : ℝ)|^19 ≤ (50176105376673/100000000000000 : ℝ)^15
        have hw : |(5801632599/10000000000 : ℝ)|=(5801632599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2604737547/10000000000 : ℝ)|^19 ≤ (9097827543133/50000000000000 : ℝ)^15
        have hw : |(-2604737547/10000000000 : ℝ)|=(2604737547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806032177/2000000000 : ℝ)|^19 ≤ (15814119768063/50000000000000 : ℝ)^15
        have hw : |(806032177/2000000000 : ℝ)|=(806032177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315069 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-205235633/1000000000 : ℝ)*X 0 0+(-1432871411/2000000000 : ℝ)*X 0 1+(182288931/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5801632599/10000000000 : ℝ)*X 1 0+(2604737547/10000000000 : ℝ)*X 1 1+(806032177/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3843551033/10000000000 : ℝ)*X 2 0+(-401523871/1250000000 : ℝ)*X 2 1+(-5462106547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315069_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5801632599/10000000000 : ℝ)*X 0 0+(-2604737547/10000000000 : ℝ)*X 0 1+(806032177/2000000000 : ℝ)*X 0 2+(5801632599/10000000000 : ℝ)*X 1 0+(-2604737547/10000000000 : ℝ)*X 1 1+(806032177/2000000000 : ℝ)*X 1 2+(5801632599/10000000000 : ℝ)*X 2 0+(-2604737547/10000000000 : ℝ)*X 2 1+(806032177/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315069_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-18677115209446278941163/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (168733/500000000000 : ℝ)*(base1) + (44172243453/100000000000 : ℝ)*(base3) + (28317/100000000000 : ℝ)*(base22) + (492209/500000000000 : ℝ)*(base24) + (116537/1000000000000 : ℝ)*(base39) + (52290421097/100000000000 : ℝ)*(base40) + (799522810829/1000000000000 : ℝ)*(base49) + (20677225413/40000000000 : ℝ)*(base50) + (174659/100000 : ℝ)*(major_s0_0) + (174659/100000 : ℝ)*(major_s0_1) + (174659/100000 : ℝ)*(major_s0_2) + (249028236539/100000000000 : ℝ)*(sp_s0_0) + (1466002231227/500000000000 : ℝ)*(sp_s0_1) + (155642547521/62500000000 : ℝ)*(sp_s0_2) + (139569307001/250000000000 : ℝ)*(sp_s0_6) + (622570506981/250000000000 : ℝ)*(f.sum) + (38835851/625000000000000000000 : ℝ)*base62 + (861299371/5000000000000000000000 : ℝ)*base64 + (164592639/250000000000000000000 : ℝ)*base67 + (1569441/5000000000000000000000 : ℝ)*base68 + (281441593/1000000000000000000000 : ℝ)*base71 + (55074879/200000000000000000000 : ℝ)*base72 + (13252473/312500000000000000000 : ℝ)*base75 + (203981653/312500000000000000000 : ℝ)*base77 + (63696543/2500000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p015_b027 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 ∨ c=69 := by omega
  rcases hc with rfl|rfl
  · exact collision_c315068 p hpa (by linarith only [hpb]) X hX
  · exact collision_c315069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
