-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_positive87
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:10:13.481143+00:00
-- url     : https://prove2.me/submissions/e3358c1c-4dba-4729-9467-61360711b244

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
theorem collision_support_c326087_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-93008327/5000000000 : ℝ)*x 0 + (5469809937/10000000000 : ℝ)*x 1 + (5784087087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93008327/5000000000 : ℝ)^89 ≤ (97092465533/12500000000000 : ℝ)^73 := by
    have hnat : (93008327 : ℕ)^89*12500000000000^73 ≤ 97092465533^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93008327 5000000000 97092465533 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469809937/10000000000 : ℝ)^89 ≤ (23961361836121/50000000000000 : ℝ)^73 := by
    have hnat : (5469809937 : ℕ)^89*50000000000000^73 ≤ 23961361836121^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469809937 10000000000 23961361836121 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5784087087/10000000000 : ℝ)^89 ≤ (25650268295321/50000000000000 : ℝ)^73 := by
    have hnat : (5784087087 : ℕ)^89*50000000000000^73 ≤ 25650268295321^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784087087 10000000000 25650268295321 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93008327/5000000000 : ℝ), (5469809937/10000000000 : ℝ), (5784087087/10000000000 : ℝ)] ![(97092465533/12500000000000 : ℝ), (23961361836121/50000000000000 : ℝ), (25650268295321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93008327/5000000000 : ℝ)|^89 ≤ (97092465533/12500000000000 : ℝ)^73
        have hw : |(-93008327/5000000000 : ℝ)|=(93008327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469809937/10000000000 : ℝ)|^89 ≤ (23961361836121/50000000000000 : ℝ)^73
        have hw : |(5469809937/10000000000 : ℝ)|=(5469809937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5784087087/10000000000 : ℝ)|^89 ≤ (25650268295321/50000000000000 : ℝ)^73
        have hw : |(5784087087/10000000000 : ℝ)|=(5784087087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5784087087/10000000000 : ℝ)*x 0 + (-93008327/5000000000 : ℝ)*x 1 + (5469809937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5784087087/10000000000 : ℝ)^89 ≤ (25650268295321/50000000000000 : ℝ)^73 := by
    have hnat : (5784087087 : ℕ)^89*50000000000000^73 ≤ 25650268295321^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784087087 10000000000 25650268295321 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93008327/5000000000 : ℝ)^89 ≤ (97092465533/12500000000000 : ℝ)^73 := by
    have hnat : (93008327 : ℕ)^89*12500000000000^73 ≤ 97092465533^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93008327 5000000000 97092465533 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469809937/10000000000 : ℝ)^89 ≤ (23961361836121/50000000000000 : ℝ)^73 := by
    have hnat : (5469809937 : ℕ)^89*50000000000000^73 ≤ 23961361836121^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469809937 10000000000 23961361836121 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5784087087/10000000000 : ℝ), (-93008327/5000000000 : ℝ), (5469809937/10000000000 : ℝ)] ![(25650268295321/50000000000000 : ℝ), (97092465533/12500000000000 : ℝ), (23961361836121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5784087087/10000000000 : ℝ)|^89 ≤ (25650268295321/50000000000000 : ℝ)^73
        have hw : |(5784087087/10000000000 : ℝ)|=(5784087087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93008327/5000000000 : ℝ)|^89 ≤ (97092465533/12500000000000 : ℝ)^73
        have hw : |(-93008327/5000000000 : ℝ)|=(93008327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469809937/10000000000 : ℝ)|^89 ≤ (23961361836121/50000000000000 : ℝ)^73
        have hw : |(5469809937/10000000000 : ℝ)|=(5469809937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5469809937/10000000000 : ℝ)*x 0 + (5784087087/10000000000 : ℝ)*x 1 + (-93008327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5469809937/10000000000 : ℝ)^89 ≤ (23961361836121/50000000000000 : ℝ)^73 := by
    have hnat : (5469809937 : ℕ)^89*50000000000000^73 ≤ 23961361836121^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469809937 10000000000 23961361836121 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5784087087/10000000000 : ℝ)^89 ≤ (25650268295321/50000000000000 : ℝ)^73 := by
    have hnat : (5784087087 : ℕ)^89*50000000000000^73 ≤ 25650268295321^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784087087 10000000000 25650268295321 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93008327/5000000000 : ℝ)^89 ≤ (97092465533/12500000000000 : ℝ)^73 := by
    have hnat : (93008327 : ℕ)^89*12500000000000^73 ≤ 97092465533^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93008327 5000000000 97092465533 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5469809937/10000000000 : ℝ), (5784087087/10000000000 : ℝ), (-93008327/5000000000 : ℝ)] ![(23961361836121/50000000000000 : ℝ), (25650268295321/50000000000000 : ℝ), (97092465533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5469809937/10000000000 : ℝ)|^89 ≤ (23961361836121/50000000000000 : ℝ)^73
        have hw : |(5469809937/10000000000 : ℝ)|=(5469809937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5784087087/10000000000 : ℝ)|^89 ≤ (25650268295321/50000000000000 : ℝ)^73
        have hw : |(5784087087/10000000000 : ℝ)|=(5784087087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93008327/5000000000 : ℝ)|^89 ≤ (97092465533/12500000000000 : ℝ)^73
        have hw : |(-93008327/5000000000 : ℝ)|=(93008327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-720341633/5000000000 : ℝ)*x 0 + (123099539/1250000000 : ℝ)*x 1 + (1090332733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (720341633/5000000000 : ℝ)^89 ≤ (9422044950639/100000000000000 : ℝ)^73 := by
    have hnat : (720341633 : ℕ)^89*100000000000000^73 ≤ 9422044950639^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720341633 5000000000 9422044950639 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123099539/1250000000 : ℝ)^89 ≤ (5925295460609/100000000000000 : ℝ)^73 := by
    have hnat : (123099539 : ℕ)^89*100000000000000^73 ≤ 5925295460609^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123099539 1250000000 5925295460609 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090332733/1250000000 : ℝ)^89 ≤ (84652659571841/100000000000000 : ℝ)^73 := by
    have hnat : (1090332733 : ℕ)^89*100000000000000^73 ≤ 84652659571841^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090332733 1250000000 84652659571841 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-720341633/5000000000 : ℝ), (123099539/1250000000 : ℝ), (1090332733/1250000000 : ℝ)] ![(9422044950639/100000000000000 : ℝ), (5925295460609/100000000000000 : ℝ), (84652659571841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-720341633/5000000000 : ℝ)|^89 ≤ (9422044950639/100000000000000 : ℝ)^73
        have hw : |(-720341633/5000000000 : ℝ)|=(720341633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(123099539/1250000000 : ℝ)|^89 ≤ (5925295460609/100000000000000 : ℝ)^73
        have hw : |(123099539/1250000000 : ℝ)|=(123099539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090332733/1250000000 : ℝ)|^89 ≤ (84652659571841/100000000000000 : ℝ)^73
        have hw : |(1090332733/1250000000 : ℝ)|=(1090332733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2081237569/5000000000 : ℝ)*x 0 + (-67255543/2500000000 : ℝ)*x 1 + (3486525059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081237569/5000000000 : ℝ)^89 ≤ (34349615317287/100000000000000 : ℝ)^73 := by
    have hnat : (2081237569 : ℕ)^89*100000000000000^73 ≤ 34349615317287^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081237569 5000000000 34349615317287 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67255543/2500000000 : ℝ)^89 ≤ (1217957225809/100000000000000 : ℝ)^73 := by
    have hnat : (67255543 : ℕ)^89*100000000000000^73 ≤ 1217957225809^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67255543 2500000000 1217957225809 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3486525059/5000000000 : ℝ)^89 ≤ (64432427435869/100000000000000 : ℝ)^73 := by
    have hnat : (3486525059 : ℕ)^89*100000000000000^73 ≤ 64432427435869^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486525059 5000000000 64432427435869 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081237569/5000000000 : ℝ), (-67255543/2500000000 : ℝ), (3486525059/5000000000 : ℝ)] ![(34349615317287/100000000000000 : ℝ), (1217957225809/100000000000000 : ℝ), (64432427435869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081237569/5000000000 : ℝ)|^89 ≤ (34349615317287/100000000000000 : ℝ)^73
        have hw : |(2081237569/5000000000 : ℝ)|=(2081237569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67255543/2500000000 : ℝ)|^89 ≤ (1217957225809/100000000000000 : ℝ)^73
        have hw : |(-67255543/2500000000 : ℝ)|=(67255543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3486525059/5000000000 : ℝ)|^89 ≤ (64432427435869/100000000000000 : ℝ)^73
        have hw : |(3486525059/5000000000 : ℝ)|=(3486525059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2142534117/10000000000 : ℝ)*x 0 + (4363690323/5000000000 : ℝ)*x 1 + (-3411423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142534117/10000000000 : ℝ)^89 ≤ (7642787367683/50000000000000 : ℝ)^73 := by
    have hnat : (2142534117 : ℕ)^89*50000000000000^73 ≤ 7642787367683^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142534117 10000000000 7642787367683 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4363690323/5000000000 : ℝ)^89 ≤ (4235424779073/5000000000000 : ℝ)^73 := by
    have hnat : (4363690323 : ℕ)^89*5000000000000^73 ≤ 4235424779073^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363690323 5000000000 4235424779073 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3411423/10000000000 : ℝ)^89 ≤ (23162801/390625000000 : ℝ)^73 := by
    have hnat : (3411423 : ℕ)^89*390625000000^73 ≤ 23162801^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411423 10000000000 23162801 390625000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142534117/10000000000 : ℝ), (4363690323/5000000000 : ℝ), (-3411423/10000000000 : ℝ)] ![(7642787367683/50000000000000 : ℝ), (4235424779073/5000000000000 : ℝ), (23162801/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142534117/10000000000 : ℝ)|^89 ≤ (7642787367683/50000000000000 : ℝ)^73
        have hw : |(2142534117/10000000000 : ℝ)|=(2142534117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4363690323/5000000000 : ℝ)|^89 ≤ (4235424779073/5000000000000 : ℝ)^73
        have hw : |(4363690323/5000000000 : ℝ)|=(4363690323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3411423/10000000000 : ℝ)|^89 ≤ (23162801/390625000000 : ℝ)^73
        have hw : |(-3411423/10000000000 : ℝ)|=(3411423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (995905263/5000000000 : ℝ)*x 0 + (142278981/200000000 : ℝ)*x 1 + (667549441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995905263/5000000000 : ℝ)^89 ≤ (13984873707003/100000000000000 : ℝ)^73 := by
    have hnat : (995905263 : ℕ)^89*100000000000000^73 ≤ 13984873707003^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995905263 5000000000 13984873707003 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142278981/200000000 : ℝ)^89 ≤ (13204642996381/20000000000000 : ℝ)^73 := by
    have hnat : (142278981 : ℕ)^89*20000000000000^73 ≤ 13204642996381^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142278981 200000000 13204642996381 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (667549441/2500000000 : ℝ)^89 ≤ (19991911297793/100000000000000 : ℝ)^73 := by
    have hnat : (667549441 : ℕ)^89*100000000000000^73 ≤ 19991911297793^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667549441 2500000000 19991911297793 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(995905263/5000000000 : ℝ), (142278981/200000000 : ℝ), (667549441/2500000000 : ℝ)] ![(13984873707003/100000000000000 : ℝ), (13204642996381/20000000000000 : ℝ), (19991911297793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(995905263/5000000000 : ℝ)|^89 ≤ (13984873707003/100000000000000 : ℝ)^73
        have hw : |(995905263/5000000000 : ℝ)|=(995905263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142278981/200000000 : ℝ)|^89 ≤ (13204642996381/20000000000000 : ℝ)^73
        have hw : |(142278981/200000000 : ℝ)|=(142278981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(667549441/2500000000 : ℝ)|^89 ≤ (19991911297793/100000000000000 : ℝ)^73
        have hw : |(667549441/2500000000 : ℝ)|=(667549441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3411423/10000000000 : ℝ)*x 0 + (2142534117/10000000000 : ℝ)*x 1 + (4363690323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3411423/10000000000 : ℝ)^89 ≤ (23162801/390625000000 : ℝ)^73 := by
    have hnat : (3411423 : ℕ)^89*390625000000^73 ≤ 23162801^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411423 10000000000 23162801 390625000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142534117/10000000000 : ℝ)^89 ≤ (7642787367683/50000000000000 : ℝ)^73 := by
    have hnat : (2142534117 : ℕ)^89*50000000000000^73 ≤ 7642787367683^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142534117 10000000000 7642787367683 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4363690323/5000000000 : ℝ)^89 ≤ (4235424779073/5000000000000 : ℝ)^73 := by
    have hnat : (4363690323 : ℕ)^89*5000000000000^73 ≤ 4235424779073^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363690323 5000000000 4235424779073 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3411423/10000000000 : ℝ), (2142534117/10000000000 : ℝ), (4363690323/5000000000 : ℝ)] ![(23162801/390625000000 : ℝ), (7642787367683/50000000000000 : ℝ), (4235424779073/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3411423/10000000000 : ℝ)|^89 ≤ (23162801/390625000000 : ℝ)^73
        have hw : |(-3411423/10000000000 : ℝ)|=(3411423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2142534117/10000000000 : ℝ)|^89 ≤ (7642787367683/50000000000000 : ℝ)^73
        have hw : |(2142534117/10000000000 : ℝ)|=(2142534117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4363690323/5000000000 : ℝ)|^89 ≤ (4235424779073/5000000000000 : ℝ)^73
        have hw : |(4363690323/5000000000 : ℝ)|=(4363690323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1090332733/1250000000 : ℝ)*x 0 + (-720341633/5000000000 : ℝ)*x 1 + (123099539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090332733/1250000000 : ℝ)^89 ≤ (84652659571841/100000000000000 : ℝ)^73 := by
    have hnat : (1090332733 : ℕ)^89*100000000000000^73 ≤ 84652659571841^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090332733 1250000000 84652659571841 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720341633/5000000000 : ℝ)^89 ≤ (9422044950639/100000000000000 : ℝ)^73 := by
    have hnat : (720341633 : ℕ)^89*100000000000000^73 ≤ 9422044950639^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720341633 5000000000 9422044950639 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123099539/1250000000 : ℝ)^89 ≤ (5925295460609/100000000000000 : ℝ)^73 := by
    have hnat : (123099539 : ℕ)^89*100000000000000^73 ≤ 5925295460609^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123099539 1250000000 5925295460609 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090332733/1250000000 : ℝ), (-720341633/5000000000 : ℝ), (123099539/1250000000 : ℝ)] ![(84652659571841/100000000000000 : ℝ), (9422044950639/100000000000000 : ℝ), (5925295460609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090332733/1250000000 : ℝ)|^89 ≤ (84652659571841/100000000000000 : ℝ)^73
        have hw : |(1090332733/1250000000 : ℝ)|=(1090332733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-720341633/5000000000 : ℝ)|^89 ≤ (9422044950639/100000000000000 : ℝ)^73
        have hw : |(-720341633/5000000000 : ℝ)|=(720341633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123099539/1250000000 : ℝ)|^89 ≤ (5925295460609/100000000000000 : ℝ)^73
        have hw : |(123099539/1250000000 : ℝ)|=(123099539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3486525059/5000000000 : ℝ)*x 0 + (2081237569/5000000000 : ℝ)*x 1 + (-67255543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3486525059/5000000000 : ℝ)^89 ≤ (64432427435869/100000000000000 : ℝ)^73 := by
    have hnat : (3486525059 : ℕ)^89*100000000000000^73 ≤ 64432427435869^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486525059 5000000000 64432427435869 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081237569/5000000000 : ℝ)^89 ≤ (34349615317287/100000000000000 : ℝ)^73 := by
    have hnat : (2081237569 : ℕ)^89*100000000000000^73 ≤ 34349615317287^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081237569 5000000000 34349615317287 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67255543/2500000000 : ℝ)^89 ≤ (1217957225809/100000000000000 : ℝ)^73 := by
    have hnat : (67255543 : ℕ)^89*100000000000000^73 ≤ 1217957225809^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67255543 2500000000 1217957225809 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3486525059/5000000000 : ℝ), (2081237569/5000000000 : ℝ), (-67255543/2500000000 : ℝ)] ![(64432427435869/100000000000000 : ℝ), (34349615317287/100000000000000 : ℝ), (1217957225809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3486525059/5000000000 : ℝ)|^89 ≤ (64432427435869/100000000000000 : ℝ)^73
        have hw : |(3486525059/5000000000 : ℝ)|=(3486525059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2081237569/5000000000 : ℝ)|^89 ≤ (34349615317287/100000000000000 : ℝ)^73
        have hw : |(2081237569/5000000000 : ℝ)|=(2081237569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67255543/2500000000 : ℝ)|^89 ≤ (1217957225809/100000000000000 : ℝ)^73
        have hw : |(-67255543/2500000000 : ℝ)|=(67255543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (667549441/2500000000 : ℝ)*x 0 + (995905263/5000000000 : ℝ)*x 1 + (142278981/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667549441/2500000000 : ℝ)^89 ≤ (19991911297793/100000000000000 : ℝ)^73 := by
    have hnat : (667549441 : ℕ)^89*100000000000000^73 ≤ 19991911297793^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667549441 2500000000 19991911297793 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995905263/5000000000 : ℝ)^89 ≤ (13984873707003/100000000000000 : ℝ)^73 := by
    have hnat : (995905263 : ℕ)^89*100000000000000^73 ≤ 13984873707003^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995905263 5000000000 13984873707003 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142278981/200000000 : ℝ)^89 ≤ (13204642996381/20000000000000 : ℝ)^73 := by
    have hnat : (142278981 : ℕ)^89*20000000000000^73 ≤ 13204642996381^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142278981 200000000 13204642996381 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667549441/2500000000 : ℝ), (995905263/5000000000 : ℝ), (142278981/200000000 : ℝ)] ![(19991911297793/100000000000000 : ℝ), (13984873707003/100000000000000 : ℝ), (13204642996381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667549441/2500000000 : ℝ)|^89 ≤ (19991911297793/100000000000000 : ℝ)^73
        have hw : |(667549441/2500000000 : ℝ)|=(667549441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(995905263/5000000000 : ℝ)|^89 ≤ (13984873707003/100000000000000 : ℝ)^73
        have hw : |(995905263/5000000000 : ℝ)|=(995905263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142278981/200000000 : ℝ)|^89 ≤ (13204642996381/20000000000000 : ℝ)^73
        have hw : |(142278981/200000000 : ℝ)|=(142278981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-67255543/2500000000 : ℝ)*x 0 + (3486525059/5000000000 : ℝ)*x 1 + (2081237569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67255543/2500000000 : ℝ)^89 ≤ (1217957225809/100000000000000 : ℝ)^73 := by
    have hnat : (67255543 : ℕ)^89*100000000000000^73 ≤ 1217957225809^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67255543 2500000000 1217957225809 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3486525059/5000000000 : ℝ)^89 ≤ (64432427435869/100000000000000 : ℝ)^73 := by
    have hnat : (3486525059 : ℕ)^89*100000000000000^73 ≤ 64432427435869^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486525059 5000000000 64432427435869 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081237569/5000000000 : ℝ)^89 ≤ (34349615317287/100000000000000 : ℝ)^73 := by
    have hnat : (2081237569 : ℕ)^89*100000000000000^73 ≤ 34349615317287^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081237569 5000000000 34349615317287 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67255543/2500000000 : ℝ), (3486525059/5000000000 : ℝ), (2081237569/5000000000 : ℝ)] ![(1217957225809/100000000000000 : ℝ), (64432427435869/100000000000000 : ℝ), (34349615317287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67255543/2500000000 : ℝ)|^89 ≤ (1217957225809/100000000000000 : ℝ)^73
        have hw : |(-67255543/2500000000 : ℝ)|=(67255543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3486525059/5000000000 : ℝ)|^89 ≤ (64432427435869/100000000000000 : ℝ)^73
        have hw : |(3486525059/5000000000 : ℝ)|=(3486525059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081237569/5000000000 : ℝ)|^89 ≤ (34349615317287/100000000000000 : ℝ)^73
        have hw : |(2081237569/5000000000 : ℝ)|=(2081237569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4363690323/5000000000 : ℝ)*x 0 + (-3411423/10000000000 : ℝ)*x 1 + (2142534117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363690323/5000000000 : ℝ)^89 ≤ (4235424779073/5000000000000 : ℝ)^73 := by
    have hnat : (4363690323 : ℕ)^89*5000000000000^73 ≤ 4235424779073^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363690323 5000000000 4235424779073 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3411423/10000000000 : ℝ)^89 ≤ (23162801/390625000000 : ℝ)^73 := by
    have hnat : (3411423 : ℕ)^89*390625000000^73 ≤ 23162801^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411423 10000000000 23162801 390625000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142534117/10000000000 : ℝ)^89 ≤ (7642787367683/50000000000000 : ℝ)^73 := by
    have hnat : (2142534117 : ℕ)^89*50000000000000^73 ≤ 7642787367683^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142534117 10000000000 7642787367683 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363690323/5000000000 : ℝ), (-3411423/10000000000 : ℝ), (2142534117/10000000000 : ℝ)] ![(4235424779073/5000000000000 : ℝ), (23162801/390625000000 : ℝ), (7642787367683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363690323/5000000000 : ℝ)|^89 ≤ (4235424779073/5000000000000 : ℝ)^73
        have hw : |(4363690323/5000000000 : ℝ)|=(4363690323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3411423/10000000000 : ℝ)|^89 ≤ (23162801/390625000000 : ℝ)^73
        have hw : |(-3411423/10000000000 : ℝ)|=(3411423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2142534117/10000000000 : ℝ)|^89 ≤ (7642787367683/50000000000000 : ℝ)^73
        have hw : |(2142534117/10000000000 : ℝ)|=(2142534117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (123099539/1250000000 : ℝ)*x 0 + (1090332733/1250000000 : ℝ)*x 1 + (-720341633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123099539/1250000000 : ℝ)^89 ≤ (5925295460609/100000000000000 : ℝ)^73 := by
    have hnat : (123099539 : ℕ)^89*100000000000000^73 ≤ 5925295460609^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123099539 1250000000 5925295460609 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090332733/1250000000 : ℝ)^89 ≤ (84652659571841/100000000000000 : ℝ)^73 := by
    have hnat : (1090332733 : ℕ)^89*100000000000000^73 ≤ 84652659571841^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090332733 1250000000 84652659571841 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (720341633/5000000000 : ℝ)^89 ≤ (9422044950639/100000000000000 : ℝ)^73 := by
    have hnat : (720341633 : ℕ)^89*100000000000000^73 ≤ 9422044950639^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720341633 5000000000 9422044950639 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123099539/1250000000 : ℝ), (1090332733/1250000000 : ℝ), (-720341633/5000000000 : ℝ)] ![(5925295460609/100000000000000 : ℝ), (84652659571841/100000000000000 : ℝ), (9422044950639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123099539/1250000000 : ℝ)|^89 ≤ (5925295460609/100000000000000 : ℝ)^73
        have hw : |(123099539/1250000000 : ℝ)|=(123099539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090332733/1250000000 : ℝ)|^89 ≤ (84652659571841/100000000000000 : ℝ)^73
        have hw : |(1090332733/1250000000 : ℝ)|=(1090332733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-720341633/5000000000 : ℝ)|^89 ≤ (9422044950639/100000000000000 : ℝ)^73
        have hw : |(-720341633/5000000000 : ℝ)|=(720341633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (142278981/200000000 : ℝ)*x 0 + (667549441/2500000000 : ℝ)*x 1 + (995905263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142278981/200000000 : ℝ)^89 ≤ (13204642996381/20000000000000 : ℝ)^73 := by
    have hnat : (142278981 : ℕ)^89*20000000000000^73 ≤ 13204642996381^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142278981 200000000 13204642996381 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667549441/2500000000 : ℝ)^89 ≤ (19991911297793/100000000000000 : ℝ)^73 := by
    have hnat : (667549441 : ℕ)^89*100000000000000^73 ≤ 19991911297793^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667549441 2500000000 19991911297793 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995905263/5000000000 : ℝ)^89 ≤ (13984873707003/100000000000000 : ℝ)^73 := by
    have hnat : (995905263 : ℕ)^89*100000000000000^73 ≤ 13984873707003^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995905263 5000000000 13984873707003 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(142278981/200000000 : ℝ), (667549441/2500000000 : ℝ), (995905263/5000000000 : ℝ)] ![(13204642996381/20000000000000 : ℝ), (19991911297793/100000000000000 : ℝ), (13984873707003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(142278981/200000000 : ℝ)|^89 ≤ (13204642996381/20000000000000 : ℝ)^73
        have hw : |(142278981/200000000 : ℝ)|=(142278981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667549441/2500000000 : ℝ)|^89 ≤ (19991911297793/100000000000000 : ℝ)^73
        have hw : |(667549441/2500000000 : ℝ)|=(667549441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995905263/5000000000 : ℝ)|^89 ≤ (13984873707003/100000000000000 : ℝ)^73
        have hw : |(995905263/5000000000 : ℝ)|=(995905263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-7964003/80000000 : ℝ)*x 0 + (2689346157/5000000000 : ℝ)*x 1 + (5387489493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7964003/80000000 : ℝ)^89 ≤ (6003908565837/100000000000000 : ℝ)^73 := by
    have hnat : (7964003 : ℕ)^89*100000000000000^73 ≤ 6003908565837^73*80000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7964003 80000000 6003908565837 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689346157/5000000000 : ℝ)^89 ≤ (46951226013041/100000000000000 : ℝ)^73 := by
    have hnat : (2689346157 : ℕ)^89*100000000000000^73 ≤ 46951226013041^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689346157 5000000000 46951226013041 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387489493/10000000000 : ℝ)^89 ≤ (9408973082249/20000000000000 : ℝ)^73 := by
    have hnat : (5387489493 : ℕ)^89*20000000000000^73 ≤ 9408973082249^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387489493 10000000000 9408973082249 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7964003/80000000 : ℝ), (2689346157/5000000000 : ℝ), (5387489493/10000000000 : ℝ)] ![(6003908565837/100000000000000 : ℝ), (46951226013041/100000000000000 : ℝ), (9408973082249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7964003/80000000 : ℝ)|^89 ≤ (6003908565837/100000000000000 : ℝ)^73
        have hw : |(-7964003/80000000 : ℝ)|=(7964003/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689346157/5000000000 : ℝ)|^89 ≤ (46951226013041/100000000000000 : ℝ)^73
        have hw : |(2689346157/5000000000 : ℝ)|=(2689346157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387489493/10000000000 : ℝ)|^89 ≤ (9408973082249/20000000000000 : ℝ)^73
        have hw : |(5387489493/10000000000 : ℝ)|=(5387489493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1346872599/2500000000 : ℝ)*x 0 + (-995500019/10000000000 : ℝ)*x 1 + (672336457/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346872599/2500000000 : ℝ)^89 ≤ (47044875024727/100000000000000 : ℝ)^73 := by
    have hnat : (1346872599 : ℕ)^89*100000000000000^73 ≤ 47044875024727^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346872599 2500000000 47044875024727 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995500019/10000000000 : ℝ)^89 ≤ (3001952974099/50000000000000 : ℝ)^73 := by
    have hnat : (995500019 : ℕ)^89*50000000000000^73 ≤ 3001952974099^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995500019 10000000000 3001952974099 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672336457/1250000000 : ℝ)^89 ≤ (46951219010377/100000000000000 : ℝ)^73 := by
    have hnat : (672336457 : ℕ)^89*100000000000000^73 ≤ 46951219010377^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672336457 1250000000 46951219010377 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346872599/2500000000 : ℝ), (-995500019/10000000000 : ℝ), (672336457/1250000000 : ℝ)] ![(47044875024727/100000000000000 : ℝ), (3001952974099/50000000000000 : ℝ), (46951219010377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346872599/2500000000 : ℝ)|^89 ≤ (47044875024727/100000000000000 : ℝ)^73
        have hw : |(1346872599/2500000000 : ℝ)|=(1346872599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995500019/10000000000 : ℝ)|^89 ≤ (3001952974099/50000000000000 : ℝ)^73
        have hw : |(-995500019/10000000000 : ℝ)|=(995500019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672336457/1250000000 : ℝ)|^89 ≤ (46951219010377/100000000000000 : ℝ)^73
        have hw : |(672336457/1250000000 : ℝ)|=(672336457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (43029529/80000000 : ℝ)*x 0 + (673436327/1250000000 : ℝ)*x 1 + (-995500471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43029529/80000000 : ℝ)^89 ≤ (46951213359291/100000000000000 : ℝ)^73 := by
    have hnat : (43029529 : ℕ)^89*100000000000000^73 ≤ 46951213359291^73*80000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43029529 80000000 46951213359291 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673436327/1250000000 : ℝ)^89 ≤ (23522438683441/50000000000000 : ℝ)^73 := by
    have hnat : (673436327 : ℕ)^89*50000000000000^73 ≤ 23522438683441^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673436327 1250000000 23522438683441 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995500471/10000000000 : ℝ)^89 ≤ (3001954635859/50000000000000 : ℝ)^73 := by
    have hnat : (995500471 : ℕ)^89*50000000000000^73 ≤ 3001954635859^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995500471 10000000000 3001954635859 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43029529/80000000 : ℝ), (673436327/1250000000 : ℝ), (-995500471/10000000000 : ℝ)] ![(46951213359291/100000000000000 : ℝ), (23522438683441/50000000000000 : ℝ), (3001954635859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43029529/80000000 : ℝ)|^89 ≤ (46951213359291/100000000000000 : ℝ)^73
        have hw : |(43029529/80000000 : ℝ)|=(43029529/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673436327/1250000000 : ℝ)|^89 ≤ (23522438683441/50000000000000 : ℝ)^73
        have hw : |(673436327/1250000000 : ℝ)|=(673436327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-995500471/10000000000 : ℝ)|^89 ≤ (3001954635859/50000000000000 : ℝ)^73
        have hw : |(-995500471/10000000000 : ℝ)|=(995500471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-897877121/10000000000 : ℝ)*x 0 + (8919791/20000000 : ℝ)*x 1 + (6337055397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897877121/10000000000 : ℝ)^89 ≤ (5294012887507/100000000000000 : ℝ)^73 := by
    have hnat : (897877121 : ℕ)^89*100000000000000^73 ≤ 5294012887507^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897877121 10000000000 5294012887507 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8919791/20000000 : ℝ)^89 ≤ (37364944316093/100000000000000 : ℝ)^73 := by
    have hnat : (8919791 : ℕ)^89*100000000000000^73 ≤ 37364944316093^73*20000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8919791 20000000 37364944316093 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6337055397/10000000000 : ℝ)^89 ≤ (44797689677/78125000000 : ℝ)^73 := by
    have hnat : (6337055397 : ℕ)^89*78125000000^73 ≤ 44797689677^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6337055397 10000000000 44797689677 78125000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-897877121/10000000000 : ℝ), (8919791/20000000 : ℝ), (6337055397/10000000000 : ℝ)] ![(5294012887507/100000000000000 : ℝ), (37364944316093/100000000000000 : ℝ), (44797689677/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-897877121/10000000000 : ℝ)|^89 ≤ (5294012887507/100000000000000 : ℝ)^73
        have hw : |(-897877121/10000000000 : ℝ)|=(897877121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8919791/20000000 : ℝ)|^89 ≤ (37364944316093/100000000000000 : ℝ)^73
        have hw : |(8919791/20000000 : ℝ)|=(8919791/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6337055397/10000000000 : ℝ)|^89 ≤ (44797689677/78125000000 : ℝ)^73
        have hw : |(6337055397/10000000000 : ℝ)|=(6337055397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5649293381/10000000000 : ℝ)*x 0 + (-169863193/10000000000 : ℝ)*x 1 + (2806564341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5649293381/10000000000 : ℝ)^89 ≤ (12461682635897/25000000000000 : ℝ)^73 := by
    have hnat : (5649293381 : ℕ)^89*25000000000000^73 ≤ 12461682635897^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649293381 10000000000 12461682635897 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169863193/10000000000 : ℝ)^89 ≤ (86913222321/12500000000000 : ℝ)^73 := by
    have hnat : (169863193 : ℕ)^89*12500000000000^73 ≤ 86913222321^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169863193 10000000000 86913222321 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806564341/5000000000 : ℝ)^89 ≤ (9891592733461/20000000000000 : ℝ)^73 := by
    have hnat : (2806564341 : ℕ)^89*20000000000000^73 ≤ 9891592733461^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806564341 5000000000 9891592733461 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5649293381/10000000000 : ℝ), (-169863193/10000000000 : ℝ), (2806564341/5000000000 : ℝ)] ![(12461682635897/25000000000000 : ℝ), (86913222321/12500000000000 : ℝ), (9891592733461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5649293381/10000000000 : ℝ)|^89 ≤ (12461682635897/25000000000000 : ℝ)^73
        have hw : |(5649293381/10000000000 : ℝ)|=(5649293381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169863193/10000000000 : ℝ)|^89 ≤ (86913222321/12500000000000 : ℝ)^73
        have hw : |(-169863193/10000000000 : ℝ)|=(169863193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806564341/5000000000 : ℝ)|^89 ≤ (9891592733461/20000000000000 : ℝ)^73
        have hw : |(2806564341/5000000000 : ℝ)|=(2806564341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2133523223/5000000000 : ℝ)*x 0 + (3473319959/5000000000 : ℝ)*x 1 + (-48451/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133523223/5000000000 : ℝ)^89 ≤ (35404575895253/100000000000000 : ℝ)^73 := by
    have hnat : (2133523223 : ℕ)^89*100000000000000^73 ≤ 35404575895253^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133523223 5000000000 35404575895253 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3473319959/5000000000 : ℝ)^89 ≤ (6413502805001/10000000000000 : ℝ)^73 := by
    have hnat : (3473319959 : ℕ)^89*10000000000000^73 ≤ 6413502805001^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473319959 5000000000 6413502805001 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48451/4000000 : ℝ)^89 ≤ (460396036807/100000000000000 : ℝ)^73 := by
    have hnat : (48451 : ℕ)^89*100000000000000^73 ≤ 460396036807^73*4000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48451 4000000 460396036807 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133523223/5000000000 : ℝ), (3473319959/5000000000 : ℝ), (-48451/4000000 : ℝ)] ![(35404575895253/100000000000000 : ℝ), (6413502805001/10000000000000 : ℝ), (460396036807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133523223/5000000000 : ℝ)|^89 ≤ (35404575895253/100000000000000 : ℝ)^73
        have hw : |(2133523223/5000000000 : ℝ)|=(2133523223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3473319959/5000000000 : ℝ)|^89 ≤ (6413502805001/10000000000000 : ℝ)^73
        have hw : |(3473319959/5000000000 : ℝ)|=(3473319959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48451/4000000 : ℝ)|^89 ≤ (460396036807/100000000000000 : ℝ)^73
        have hw : |(-48451/4000000 : ℝ)|=(48451/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3542218331/10000000000 : ℝ)*x 0 + (5073281261/10000000000 : ℝ)*x 1 + (352652933/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3542218331/10000000000 : ℝ)^89 ≤ (352692617843/1250000000000 : ℝ)^73 := by
    have hnat : (3542218331 : ℕ)^89*1250000000000^73 ≤ 352692617843^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3542218331 10000000000 352692617843 1250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5073281261/10000000000 : ℝ)^89 ≤ (43721467974493/100000000000000 : ℝ)^73 := by
    have hnat : (5073281261 : ℕ)^89*100000000000000^73 ≤ 43721467974493^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073281261 10000000000 43721467974493 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352652933/1000000000 : ℝ)^89 ≤ (3507890323543/12500000000000 : ℝ)^73 := by
    have hnat : (352652933 : ℕ)^89*12500000000000^73 ≤ 3507890323543^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352652933 1000000000 3507890323543 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3542218331/10000000000 : ℝ), (5073281261/10000000000 : ℝ), (352652933/1000000000 : ℝ)] ![(352692617843/1250000000000 : ℝ), (43721467974493/100000000000000 : ℝ), (3507890323543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3542218331/10000000000 : ℝ)|^89 ≤ (352692617843/1250000000000 : ℝ)^73
        have hw : |(3542218331/10000000000 : ℝ)|=(3542218331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5073281261/10000000000 : ℝ)|^89 ≤ (43721467974493/100000000000000 : ℝ)^73
        have hw : |(5073281261/10000000000 : ℝ)|=(5073281261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352652933/1000000000 : ℝ)|^89 ≤ (3507890323543/12500000000000 : ℝ)^73
        have hw : |(352652933/1000000000 : ℝ)|=(352652933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-48451/4000000 : ℝ)*x 0 + (2133523223/5000000000 : ℝ)*x 1 + (3473319959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48451/4000000 : ℝ)^89 ≤ (460396036807/100000000000000 : ℝ)^73 := by
    have hnat : (48451 : ℕ)^89*100000000000000^73 ≤ 460396036807^73*4000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48451 4000000 460396036807 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133523223/5000000000 : ℝ)^89 ≤ (35404575895253/100000000000000 : ℝ)^73 := by
    have hnat : (2133523223 : ℕ)^89*100000000000000^73 ≤ 35404575895253^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133523223 5000000000 35404575895253 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3473319959/5000000000 : ℝ)^89 ≤ (6413502805001/10000000000000 : ℝ)^73 := by
    have hnat : (3473319959 : ℕ)^89*10000000000000^73 ≤ 6413502805001^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473319959 5000000000 6413502805001 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48451/4000000 : ℝ), (2133523223/5000000000 : ℝ), (3473319959/5000000000 : ℝ)] ![(460396036807/100000000000000 : ℝ), (35404575895253/100000000000000 : ℝ), (6413502805001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48451/4000000 : ℝ)|^89 ≤ (460396036807/100000000000000 : ℝ)^73
        have hw : |(-48451/4000000 : ℝ)|=(48451/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2133523223/5000000000 : ℝ)|^89 ≤ (35404575895253/100000000000000 : ℝ)^73
        have hw : |(2133523223/5000000000 : ℝ)|=(2133523223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3473319959/5000000000 : ℝ)|^89 ≤ (6413502805001/10000000000000 : ℝ)^73
        have hw : |(3473319959/5000000000 : ℝ)|=(3473319959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6337055397/10000000000 : ℝ)*x 0 + (-897877121/10000000000 : ℝ)*x 1 + (8919791/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6337055397/10000000000 : ℝ)^89 ≤ (44797689677/78125000000 : ℝ)^73 := by
    have hnat : (6337055397 : ℕ)^89*78125000000^73 ≤ 44797689677^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6337055397 10000000000 44797689677 78125000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897877121/10000000000 : ℝ)^89 ≤ (5294012887507/100000000000000 : ℝ)^73 := by
    have hnat : (897877121 : ℕ)^89*100000000000000^73 ≤ 5294012887507^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897877121 10000000000 5294012887507 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8919791/20000000 : ℝ)^89 ≤ (37364944316093/100000000000000 : ℝ)^73 := by
    have hnat : (8919791 : ℕ)^89*100000000000000^73 ≤ 37364944316093^73*20000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8919791 20000000 37364944316093 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6337055397/10000000000 : ℝ), (-897877121/10000000000 : ℝ), (8919791/20000000 : ℝ)] ![(44797689677/78125000000 : ℝ), (5294012887507/100000000000000 : ℝ), (37364944316093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6337055397/10000000000 : ℝ)|^89 ≤ (44797689677/78125000000 : ℝ)^73
        have hw : |(6337055397/10000000000 : ℝ)|=(6337055397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-897877121/10000000000 : ℝ)|^89 ≤ (5294012887507/100000000000000 : ℝ)^73
        have hw : |(-897877121/10000000000 : ℝ)|=(897877121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8919791/20000000 : ℝ)|^89 ≤ (37364944316093/100000000000000 : ℝ)^73
        have hw : |(8919791/20000000 : ℝ)|=(8919791/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2806564341/5000000000 : ℝ)*x 0 + (5649293381/10000000000 : ℝ)*x 1 + (-169863193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2806564341/5000000000 : ℝ)^89 ≤ (9891592733461/20000000000000 : ℝ)^73 := by
    have hnat : (2806564341 : ℕ)^89*20000000000000^73 ≤ 9891592733461^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806564341 5000000000 9891592733461 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5649293381/10000000000 : ℝ)^89 ≤ (12461682635897/25000000000000 : ℝ)^73 := by
    have hnat : (5649293381 : ℕ)^89*25000000000000^73 ≤ 12461682635897^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649293381 10000000000 12461682635897 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169863193/10000000000 : ℝ)^89 ≤ (86913222321/12500000000000 : ℝ)^73 := by
    have hnat : (169863193 : ℕ)^89*12500000000000^73 ≤ 86913222321^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169863193 10000000000 86913222321 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2806564341/5000000000 : ℝ), (5649293381/10000000000 : ℝ), (-169863193/10000000000 : ℝ)] ![(9891592733461/20000000000000 : ℝ), (12461682635897/25000000000000 : ℝ), (86913222321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2806564341/5000000000 : ℝ)|^89 ≤ (9891592733461/20000000000000 : ℝ)^73
        have hw : |(2806564341/5000000000 : ℝ)|=(2806564341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5649293381/10000000000 : ℝ)|^89 ≤ (12461682635897/25000000000000 : ℝ)^73
        have hw : |(5649293381/10000000000 : ℝ)|=(5649293381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169863193/10000000000 : ℝ)|^89 ≤ (86913222321/12500000000000 : ℝ)^73
        have hw : |(-169863193/10000000000 : ℝ)|=(169863193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (352652933/1000000000 : ℝ)*x 0 + (3542218331/10000000000 : ℝ)*x 1 + (5073281261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352652933/1000000000 : ℝ)^89 ≤ (3507890323543/12500000000000 : ℝ)^73 := by
    have hnat : (352652933 : ℕ)^89*12500000000000^73 ≤ 3507890323543^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352652933 1000000000 3507890323543 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3542218331/10000000000 : ℝ)^89 ≤ (352692617843/1250000000000 : ℝ)^73 := by
    have hnat : (3542218331 : ℕ)^89*1250000000000^73 ≤ 352692617843^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3542218331 10000000000 352692617843 1250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073281261/10000000000 : ℝ)^89 ≤ (43721467974493/100000000000000 : ℝ)^73 := by
    have hnat : (5073281261 : ℕ)^89*100000000000000^73 ≤ 43721467974493^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073281261 10000000000 43721467974493 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(352652933/1000000000 : ℝ), (3542218331/10000000000 : ℝ), (5073281261/10000000000 : ℝ)] ![(3507890323543/12500000000000 : ℝ), (352692617843/1250000000000 : ℝ), (43721467974493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(352652933/1000000000 : ℝ)|^89 ≤ (3507890323543/12500000000000 : ℝ)^73
        have hw : |(352652933/1000000000 : ℝ)|=(352652933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3542218331/10000000000 : ℝ)|^89 ≤ (352692617843/1250000000000 : ℝ)^73
        have hw : |(3542218331/10000000000 : ℝ)|=(3542218331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073281261/10000000000 : ℝ)|^89 ≤ (43721467974493/100000000000000 : ℝ)^73
        have hw : |(5073281261/10000000000 : ℝ)|=(5073281261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-169863193/10000000000 : ℝ)*x 0 + (2806564341/5000000000 : ℝ)*x 1 + (5649293381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169863193/10000000000 : ℝ)^89 ≤ (86913222321/12500000000000 : ℝ)^73 := by
    have hnat : (169863193 : ℕ)^89*12500000000000^73 ≤ 86913222321^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169863193 10000000000 86913222321 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2806564341/5000000000 : ℝ)^89 ≤ (9891592733461/20000000000000 : ℝ)^73 := by
    have hnat : (2806564341 : ℕ)^89*20000000000000^73 ≤ 9891592733461^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806564341 5000000000 9891592733461 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5649293381/10000000000 : ℝ)^89 ≤ (12461682635897/25000000000000 : ℝ)^73 := by
    have hnat : (5649293381 : ℕ)^89*25000000000000^73 ≤ 12461682635897^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649293381 10000000000 12461682635897 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169863193/10000000000 : ℝ), (2806564341/5000000000 : ℝ), (5649293381/10000000000 : ℝ)] ![(86913222321/12500000000000 : ℝ), (9891592733461/20000000000000 : ℝ), (12461682635897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169863193/10000000000 : ℝ)|^89 ≤ (86913222321/12500000000000 : ℝ)^73
        have hw : |(-169863193/10000000000 : ℝ)|=(169863193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2806564341/5000000000 : ℝ)|^89 ≤ (9891592733461/20000000000000 : ℝ)^73
        have hw : |(2806564341/5000000000 : ℝ)|=(2806564341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5649293381/10000000000 : ℝ)|^89 ≤ (12461682635897/25000000000000 : ℝ)^73
        have hw : |(5649293381/10000000000 : ℝ)|=(5649293381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3473319959/5000000000 : ℝ)*x 0 + (-48451/4000000 : ℝ)*x 1 + (2133523223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3473319959/5000000000 : ℝ)^89 ≤ (6413502805001/10000000000000 : ℝ)^73 := by
    have hnat : (3473319959 : ℕ)^89*10000000000000^73 ≤ 6413502805001^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473319959 5000000000 6413502805001 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48451/4000000 : ℝ)^89 ≤ (460396036807/100000000000000 : ℝ)^73 := by
    have hnat : (48451 : ℕ)^89*100000000000000^73 ≤ 460396036807^73*4000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48451 4000000 460396036807 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133523223/5000000000 : ℝ)^89 ≤ (35404575895253/100000000000000 : ℝ)^73 := by
    have hnat : (2133523223 : ℕ)^89*100000000000000^73 ≤ 35404575895253^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133523223 5000000000 35404575895253 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3473319959/5000000000 : ℝ), (-48451/4000000 : ℝ), (2133523223/5000000000 : ℝ)] ![(6413502805001/10000000000000 : ℝ), (460396036807/100000000000000 : ℝ), (35404575895253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3473319959/5000000000 : ℝ)|^89 ≤ (6413502805001/10000000000000 : ℝ)^73
        have hw : |(3473319959/5000000000 : ℝ)|=(3473319959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48451/4000000 : ℝ)|^89 ≤ (460396036807/100000000000000 : ℝ)^73
        have hw : |(-48451/4000000 : ℝ)|=(48451/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2133523223/5000000000 : ℝ)|^89 ≤ (35404575895253/100000000000000 : ℝ)^73
        have hw : |(2133523223/5000000000 : ℝ)|=(2133523223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8919791/20000000 : ℝ)*x 0 + (6337055397/10000000000 : ℝ)*x 1 + (-897877121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8919791/20000000 : ℝ)^89 ≤ (37364944316093/100000000000000 : ℝ)^73 := by
    have hnat : (8919791 : ℕ)^89*100000000000000^73 ≤ 37364944316093^73*20000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8919791 20000000 37364944316093 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6337055397/10000000000 : ℝ)^89 ≤ (44797689677/78125000000 : ℝ)^73 := by
    have hnat : (6337055397 : ℕ)^89*78125000000^73 ≤ 44797689677^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6337055397 10000000000 44797689677 78125000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897877121/10000000000 : ℝ)^89 ≤ (5294012887507/100000000000000 : ℝ)^73 := by
    have hnat : (897877121 : ℕ)^89*100000000000000^73 ≤ 5294012887507^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897877121 10000000000 5294012887507 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8919791/20000000 : ℝ), (6337055397/10000000000 : ℝ), (-897877121/10000000000 : ℝ)] ![(37364944316093/100000000000000 : ℝ), (44797689677/78125000000 : ℝ), (5294012887507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8919791/20000000 : ℝ)|^89 ≤ (37364944316093/100000000000000 : ℝ)^73
        have hw : |(8919791/20000000 : ℝ)|=(8919791/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6337055397/10000000000 : ℝ)|^89 ≤ (44797689677/78125000000 : ℝ)^73
        have hw : |(6337055397/10000000000 : ℝ)|=(6337055397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-897877121/10000000000 : ℝ)|^89 ≤ (5294012887507/100000000000000 : ℝ)^73
        have hw : |(-897877121/10000000000 : ℝ)|=(897877121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326087_s1_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5073281261/10000000000 : ℝ)*x 0 + (352652933/1000000000 : ℝ)*x 1 + (3542218331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5073281261/10000000000 : ℝ)^89 ≤ (43721467974493/100000000000000 : ℝ)^73 := by
    have hnat : (5073281261 : ℕ)^89*100000000000000^73 ≤ 43721467974493^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073281261 10000000000 43721467974493 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352652933/1000000000 : ℝ)^89 ≤ (3507890323543/12500000000000 : ℝ)^73 := by
    have hnat : (352652933 : ℕ)^89*12500000000000^73 ≤ 3507890323543^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352652933 1000000000 3507890323543 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3542218331/10000000000 : ℝ)^89 ≤ (352692617843/1250000000000 : ℝ)^73 := by
    have hnat : (3542218331 : ℕ)^89*1250000000000^73 ≤ 352692617843^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3542218331 10000000000 352692617843 1250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5073281261/10000000000 : ℝ), (352652933/1000000000 : ℝ), (3542218331/10000000000 : ℝ)] ![(43721467974493/100000000000000 : ℝ), (3507890323543/12500000000000 : ℝ), (352692617843/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5073281261/10000000000 : ℝ)|^89 ≤ (43721467974493/100000000000000 : ℝ)^73
        have hw : |(5073281261/10000000000 : ℝ)|=(5073281261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352652933/1000000000 : ℝ)|^89 ≤ (3507890323543/12500000000000 : ℝ)^73
        have hw : |(352652933/1000000000 : ℝ)|=(352652933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3542218331/10000000000 : ℝ)|^89 ≤ (352692617843/1250000000000 : ℝ)^73
        have hw : |(3542218331/10000000000 : ℝ)|=(3542218331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326087 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((34407/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34407/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((34407/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(34407/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34407/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34407/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-93008327/5000000000 : ℝ)*X 0 0+(5469809937/10000000000 : ℝ)*X 0 1+(5784087087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5784087087/10000000000 : ℝ)*X 1 0+(-93008327/5000000000 : ℝ)*X 1 1+(5469809937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5469809937/10000000000 : ℝ)*X 2 0+(5784087087/10000000000 : ℝ)*X 2 1+(-93008327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-720341633/5000000000 : ℝ)*X 0 0+(123099539/1250000000 : ℝ)*X 0 1+(1090332733/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2081237569/5000000000 : ℝ)*X 1 0+(-67255543/2500000000 : ℝ)*X 1 1+(3486525059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2142534117/10000000000 : ℝ)*X 2 0+(4363690323/5000000000 : ℝ)*X 2 1+(-3411423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((995905263/5000000000 : ℝ)*X 0 0+(142278981/200000000 : ℝ)*X 0 1+(667549441/2500000000 : ℝ)*X 0 2+(995905263/5000000000 : ℝ)*X 1 0+(142278981/200000000 : ℝ)*X 1 1+(667549441/2500000000 : ℝ)*X 1 2+(995905263/5000000000 : ℝ)*X 2 0+(142278981/200000000 : ℝ)*X 2 1+(667549441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3411423/10000000000 : ℝ)*X 0 0+(2142534117/10000000000 : ℝ)*X 0 1+(4363690323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1090332733/1250000000 : ℝ)*X 1 0+(-720341633/5000000000 : ℝ)*X 1 1+(123099539/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3486525059/5000000000 : ℝ)*X 2 0+(2081237569/5000000000 : ℝ)*X 2 1+(-67255543/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((667549441/2500000000 : ℝ)*X 0 0+(995905263/5000000000 : ℝ)*X 0 1+(142278981/200000000 : ℝ)*X 0 2+(667549441/2500000000 : ℝ)*X 1 0+(995905263/5000000000 : ℝ)*X 1 1+(142278981/200000000 : ℝ)*X 1 2+(667549441/2500000000 : ℝ)*X 2 0+(995905263/5000000000 : ℝ)*X 2 1+(142278981/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-67255543/2500000000 : ℝ)*X 0 0+(3486525059/5000000000 : ℝ)*X 0 1+(2081237569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4363690323/5000000000 : ℝ)*X 1 0+(-3411423/10000000000 : ℝ)*X 1 1+(2142534117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((123099539/1250000000 : ℝ)*X 2 0+(1090332733/1250000000 : ℝ)*X 2 1+(-720341633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((142278981/200000000 : ℝ)*X 0 0+(667549441/2500000000 : ℝ)*X 0 1+(995905263/5000000000 : ℝ)*X 0 2+(142278981/200000000 : ℝ)*X 1 0+(667549441/2500000000 : ℝ)*X 1 1+(995905263/5000000000 : ℝ)*X 1 2+(142278981/200000000 : ℝ)*X 2 0+(667549441/2500000000 : ℝ)*X 2 1+(995905263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6293/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6293/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6354092596695932923239/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586696530791/500000000000 : ℝ)*(base7) + (706377/200000000000 : ℝ)*(base19) + (183981379319/1000000000000 : ℝ)*(base50) + (2495741/1000000000000 : ℝ)*(base53) + (19274139177/500000000000 : ℝ)*(base60) + (1364275552987/1000000000000 : ℝ)*(major_s0_0) + (1364275552987/1000000000000 : ℝ)*(major_s0_1) + (272854611449/200000000000 : ℝ)*(major_s0_2) + (555001/125000000000 : ℝ)*(sp_s0_0) + (71295991473/50000000000 : ℝ)*(sp_s0_7) + (1425945687259/1000000000000 : ℝ)*(sp_s0_8) + (285190342977/200000000000 : ℝ)*(sp_s0_9) + (73392475727/40000000000 : ℝ)*(sp_s0_13) + (6237419/250000000000 : ℝ)*(sp_s0_14) + (330709415797/500000000000 : ℝ)*(f.failure) + (285190342977/200000000000 : ℝ)*(f.sum) + (2081263915102011/10000000000000000000000000000 : ℝ)*base63 + (602582066488947/2000000000000000000000000000 : ℝ)*base65 + (110508833026841/200000000000000000000000000 : ℝ)*base66 + (12705098552893/40000000000000000000000000 : ℝ)*base69 + (146620773820537/2000000000000000000000000000 : ℝ)*base71 + (4385043267121239/10000000000000000000000000000 : ℝ)*base72 + (3346072399878761/10000000000000000000000000000 : ℝ)*base75 + (132512608413159/200000000000000000000000000 : ℝ)*base77 + (1101614530536711/10000000000000000000000000000 : ℝ)*base79 + (3641/10000000000000000 : ℝ)*base87 + (3641/10000000000000000 : ℝ)*base89 + (13641/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((6293/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6293/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25416363025068703706031/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586696530791/500000000000 : ℝ)*(base7) + (706377/200000000000 : ℝ)*(base21) + (2495741/1000000000000 : ℝ)*(base33) + (19274139177/500000000000 : ℝ)*(base40) + (183981379319/1000000000000 : ℝ)*(base60) + (272854611449/200000000000 : ℝ)*(major_s0_0) + (1364275552987/1000000000000 : ℝ)*(major_s0_1) + (1364275552987/1000000000000 : ℝ)*(major_s0_2) + (555001/125000000000 : ℝ)*(sp_s0_1) + (285190342977/200000000000 : ℝ)*(sp_s0_14) + (71295991473/50000000000 : ℝ)*(sp_s0_15) + (1425945687259/1000000000000 : ℝ)*(sp_s0_16) + (73392475727/40000000000 : ℝ)*(sp_s0_20) + (997987/40000000000 : ℝ)*(sp_s0_22) + (330709415797/500000000000 : ℝ)*(f.failure) + (285190342977/200000000000 : ℝ)*(f.sum) + (1101614530536711/10000000000000000000000000000 : ℝ)*base63 + (3346072399878761/10000000000000000000000000000 : ℝ)*base65 + (132512608413159/200000000000000000000000000 : ℝ)*base67 + (64038779893159/200000000000000000000000000 : ℝ)*base69 + (2077852492102011/10000000000000000000000000000 : ℝ)*base71 + (1031088889888947/2000000000000000000000000000 : ℝ)*base73 + (4385043267121239/10000000000000000000000000000 : ℝ)*base74 + (12705098552893/40000000000000000000000000 : ℝ)*base77 + (146620773820537/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (13641/10000000000000000 : ℝ)*base87 + (3641/10000000000000000 : ℝ)*base89 + (3641/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6293/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6293/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25416363025068703706031/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586696530791/500000000000 : ℝ)*(base7) + (706377/200000000000 : ℝ)*(base11) + (183981379319/1000000000000 : ℝ)*(base40) + (2495741/1000000000000 : ℝ)*(base43) + (19274139177/500000000000 : ℝ)*(base50) + (1364275552987/1000000000000 : ℝ)*(major_s0_0) + (272854611449/200000000000 : ℝ)*(major_s0_1) + (1364275552987/1000000000000 : ℝ)*(major_s0_2) + (555001/125000000000 : ℝ)*(sp_s0_2) + (997987/40000000000 : ℝ)*(sp_s0_9) + (1425945687259/1000000000000 : ℝ)*(sp_s0_21) + (285190342977/200000000000 : ℝ)*(sp_s0_22) + (71295991473/50000000000 : ℝ)*(sp_s0_23) + (73392475727/40000000000 : ℝ)*(sp_s0_27) + (330709415797/500000000000 : ℝ)*(f.failure) + (285190342977/200000000000 : ℝ)*(f.sum) + (146620773820537/2000000000000000000000000000 : ℝ)*base63 + (4385043267121239/10000000000000000000000000000 : ℝ)*base64 + (12705098552893/40000000000000000000000000 : ℝ)*base67 + (132512608413159/200000000000000000000000000 : ℝ)*base69 + (1101614530536711/10000000000000000000000000000 : ℝ)*base71 + (3346072399878761/10000000000000000000000000000 : ℝ)*base73 + (1031088889888947/2000000000000000000000000000 : ℝ)*base75 + (64038779893159/200000000000000000000000000 : ℝ)*base77 + (2077852492102011/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (3641/10000000000000000 : ℝ)*base87 + (13641/10000000000000000 : ℝ)*base89 + (3641/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (6293/10000 : ℝ) ^ (87/16 : ℝ) ≤ (8059144011207817923/100000000000000000000 : ℝ) := by
    have hpowers : (6293/10000 : ℝ)^87 ≤ (8059144011207817923/100000000000000000000 : ℝ)^16 := by
      have hnat : (6293 : ℕ)^87*100000000000000000000^16 ≤ 8059144011207817923^16*10000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6293 10000 8059144011207817923 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6293/10000 : ℝ)) (X := (8059144011207817923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (108059144011207817923/100000000000000000000 : ℝ) ≤ (5071782598138319/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (108059144011207817923/100000000000000000000 : ℝ)^16 ≤ (5071782598138319/5000000000000000 : ℝ)^87 := by
      have hnat : (108059144011207817923 : ℕ)^16*5000000000000000^87 ≤ 5071782598138319^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108059144011207817923 100000000000000000000 5071782598138319 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5071782598138319/5000000000000000 : ℝ)) (X := (108059144011207817923/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (58059144011207817923/50000000000000000000 : ℝ) ≤ (10278642163867677/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (58059144011207817923/50000000000000000000 : ℝ)^16 ≤ (10278642163867677/10000000000000000 : ℝ)^87 := by
      have hnat : (58059144011207817923 : ℕ)^16*10000000000000000^87 ≤ 10278642163867677^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58059144011207817923 50000000000000000000 10278642163867677 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10278642163867677/10000000000000000 : ℝ)) (X := (58059144011207817923/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(71782598138319/3146500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(135076967591039/6293000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (6293/10000 : ℝ)) (alpha := (71782598138319/3146500000000000 : ℝ)) (beta := (135076967591039/6293000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6293/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(71782598138319/3146500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(135076967591039/6293000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6293/10000 : ℝ) ^ (87/16 : ℝ) ≤ (8059144011207817923/100000000000000000000 : ℝ) := by
    have hpowers : (6293/10000 : ℝ)^87 ≤ (8059144011207817923/100000000000000000000 : ℝ)^16 := by
      have hnat : (6293 : ℕ)^87*100000000000000000000^16 ≤ 8059144011207817923^16*10000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6293 10000 8059144011207817923 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6293/10000 : ℝ)) (X := (8059144011207817923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (108059144011207817923/100000000000000000000 : ℝ) ≤ (5071782598138319/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (108059144011207817923/100000000000000000000 : ℝ)^16 ≤ (5071782598138319/5000000000000000 : ℝ)^87 := by
      have hnat : (108059144011207817923 : ℕ)^16*5000000000000000^87 ≤ 5071782598138319^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108059144011207817923 100000000000000000000 5071782598138319 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5071782598138319/5000000000000000 : ℝ)) (X := (108059144011207817923/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (58059144011207817923/50000000000000000000 : ℝ) ≤ (10278642163867677/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (58059144011207817923/50000000000000000000 : ℝ)^16 ≤ (10278642163867677/10000000000000000 : ℝ)^87 := by
      have hnat : (58059144011207817923 : ℕ)^16*10000000000000000^87 ≤ 10278642163867677^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58059144011207817923 50000000000000000000 10278642163867677 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10278642163867677/10000000000000000 : ℝ)) (X := (58059144011207817923/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(71782598138319/3146500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(135076967591039/6293000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (6293/10000 : ℝ)) (alpha := (71782598138319/3146500000000000 : ℝ)) (beta := (135076967591039/6293000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (6293/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(71782598138319/3146500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(135076967591039/6293000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6293/10000 : ℝ) ^ (87/16 : ℝ) ≤ (8059144011207817923/100000000000000000000 : ℝ) := by
    have hpowers : (6293/10000 : ℝ)^87 ≤ (8059144011207817923/100000000000000000000 : ℝ)^16 := by
      have hnat : (6293 : ℕ)^87*100000000000000000000^16 ≤ 8059144011207817923^16*10000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6293 10000 8059144011207817923 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6293/10000 : ℝ)) (X := (8059144011207817923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (108059144011207817923/100000000000000000000 : ℝ) ≤ (5071782598138319/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (108059144011207817923/100000000000000000000 : ℝ)^16 ≤ (5071782598138319/5000000000000000 : ℝ)^87 := by
      have hnat : (108059144011207817923 : ℕ)^16*5000000000000000^87 ≤ 5071782598138319^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108059144011207817923 100000000000000000000 5071782598138319 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5071782598138319/5000000000000000 : ℝ)) (X := (108059144011207817923/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (58059144011207817923/50000000000000000000 : ℝ) ≤ (10278642163867677/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (58059144011207817923/50000000000000000000 : ℝ)^16 ≤ (10278642163867677/10000000000000000 : ℝ)^87 := by
      have hnat : (58059144011207817923 : ℕ)^16*10000000000000000^87 ≤ 10278642163867677^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58059144011207817923 50000000000000000000 10278642163867677 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10278642163867677/10000000000000000 : ℝ)) (X := (58059144011207817923/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(71782598138319/3146500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(135076967591039/6293000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (6293/10000 : ℝ)) (alpha := (71782598138319/3146500000000000 : ℝ)) (beta := (135076967591039/6293000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6293/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(71782598138319/3146500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(135076967591039/6293000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-7964003/80000000 : ℝ)*X 0 0+(2689346157/5000000000 : ℝ)*X 0 1+(5387489493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1346872599/2500000000 : ℝ)*X 1 0+(-995500019/10000000000 : ℝ)*X 1 1+(672336457/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((43029529/80000000 : ℝ)*X 2 0+(673436327/1250000000 : ℝ)*X 2 1+(-995500471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-897877121/10000000000 : ℝ)*X 0 0+(8919791/20000000 : ℝ)*X 0 1+(6337055397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5649293381/10000000000 : ℝ)*X 1 0+(-169863193/10000000000 : ℝ)*X 1 1+(2806564341/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2133523223/5000000000 : ℝ)*X 2 0+(3473319959/5000000000 : ℝ)*X 2 1+(-48451/4000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3542218331/10000000000 : ℝ)*X 0 0+(5073281261/10000000000 : ℝ)*X 0 1+(352652933/1000000000 : ℝ)*X 0 2+(3542218331/10000000000 : ℝ)*X 1 0+(5073281261/10000000000 : ℝ)*X 1 1+(352652933/1000000000 : ℝ)*X 1 2+(3542218331/10000000000 : ℝ)*X 2 0+(5073281261/10000000000 : ℝ)*X 2 1+(352652933/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-48451/4000000 : ℝ)*X 0 0+(2133523223/5000000000 : ℝ)*X 0 1+(3473319959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6337055397/10000000000 : ℝ)*X 1 0+(-897877121/10000000000 : ℝ)*X 1 1+(8919791/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2806564341/5000000000 : ℝ)*X 2 0+(5649293381/10000000000 : ℝ)*X 2 1+(-169863193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((352652933/1000000000 : ℝ)*X 0 0+(3542218331/10000000000 : ℝ)*X 0 1+(5073281261/10000000000 : ℝ)*X 0 2+(352652933/1000000000 : ℝ)*X 1 0+(3542218331/10000000000 : ℝ)*X 1 1+(5073281261/10000000000 : ℝ)*X 1 2+(352652933/1000000000 : ℝ)*X 2 0+(3542218331/10000000000 : ℝ)*X 2 1+(5073281261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-169863193/10000000000 : ℝ)*X 0 0+(2806564341/5000000000 : ℝ)*X 0 1+(5649293381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3473319959/5000000000 : ℝ)*X 1 0+(-48451/4000000 : ℝ)*X 1 1+(2133523223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((8919791/20000000 : ℝ)*X 2 0+(6337055397/10000000000 : ℝ)*X 2 1+(-897877121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((5073281261/10000000000 : ℝ)*X 0 0+(352652933/1000000000 : ℝ)*X 0 1+(3542218331/10000000000 : ℝ)*X 0 2+(5073281261/10000000000 : ℝ)*X 1 0+(352652933/1000000000 : ℝ)*X 1 1+(3542218331/10000000000 : ℝ)*X 1 2+(5073281261/10000000000 : ℝ)*X 2 0+(352652933/1000000000 : ℝ)*X 2 1+(3542218331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326087_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((34407/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34407/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14086554403793432338413/3146500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2247253/1000000000000 : ℝ)*(base19) + (575669/100000000000 : ℝ)*(base23) + (392973519753/1000000000000 : ℝ)*(base50) + (11306564161/31250000000 : ℝ)*(base60) + (3627239700211/1000000000000 : ℝ)*(major_s1_0) + (3627239700211/1000000000000 : ℝ)*(major_s1_1) + (3627239700211/1000000000000 : ℝ)*(major_s1_2) + (3318111/500000000000 : ℝ)*(sp_s1_1) + (85873915347/15625000000 : ℝ)*(sp_s1_7) + (5495935245181/1000000000000 : ℝ)*(sp_s1_8) + (1373983565533/250000000000 : ℝ)*(sp_s1_9) + (219816722433/125000000000 : ℝ)*(sp_s1_13) + (846653/62500000000 : ℝ)*(sp_s1_14) + (2054917/500000000000 : ℝ)*(sp_s1_23) + (219816722433/125000000000 : ℝ)*(f.failure) + (343496508041/62500000000 : ℝ)*(f.sum) + (5378862819108953/6293000000000000000000000000 : ℝ)*base62 + (3052271693787629/6293000000000000000000000000 : ℝ)*base65 + (1623579237521309/3146500000000000000000000000 : ℝ)*base67 + (732569833559741/3146500000000000000000000000 : ℝ)*base68 + (1248269341656947/6293000000000000000000000000 : ℝ)*base71 + (1310109844725029/6293000000000000000000000000 : ℝ)*base73 + (337183758151571/6293000000000000000000000000 : ℝ)*base74 + (89726643402391/3146500000000000000000000000 : ℝ)*base76 + (1357812692044047/6293000000000000000000000000 : ℝ)*base79 + (1049/2500000000000000 : ℝ)*base87 + (1049/2500000000000000 : ℝ)*base89 + (1049/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((34407/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(34407/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (201235634478090206673/44950000000000000000000000 : ℝ) := by norm_num
    linear_combination (575669/100000000000 : ℝ)*(base13) + (1123627/500000000000 : ℝ)*(base21) + (11306564161/31250000000 : ℝ)*(base40) + (392973519753/1000000000000 : ℝ)*(base60) + (362723970021/100000000000 : ℝ)*(major_s1_0) + (362723970021/100000000000 : ℝ)*(major_s1_1) + (362723970021/100000000000 : ℝ)*(major_s1_2) + (3318109/500000000000 : ℝ)*(sp_s1_2) + (2054917/500000000000 : ℝ)*(sp_s1_7) + (5495934262131/1000000000000 : ℝ)*(sp_s1_14) + (85873915347/15625000000 : ℝ)*(sp_s1_15) + (42936994103/7812500000 : ℝ)*(sp_s1_16) + (219816722433/125000000000 : ℝ)*(sp_s1_20) + (846653/62500000000 : ℝ)*(sp_s1_22) + (219816722433/125000000000 : ℝ)*(f.failure) + (343496508041/62500000000 : ℝ)*(f.sum) + (14327785606091/89900000000000000000000000 : ℝ)*base63 + (58285834246783/89900000000000000000000000 : ℝ)*base64 + (16032128447743/44950000000000000000000000 : ℝ)*base66 + (22781476580243/44950000000000000000000000 : ℝ)*base68 + (80821499756809/89900000000000000000000000 : ℝ)*base70 + (48225789625763/89900000000000000000000000 : ℝ)*base72 + (89302897140303/89900000000000000000000000 : ℝ)*base74 + (42316948927163/44950000000000000000000000 : ℝ)*base76 + (9600985576171/89900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (3549/2500000000000000 : ℝ)*base87 + (3549/2500000000000000 : ℝ)*base89 + (3549/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34407/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34407/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14086533346469208048213/3146500000000000000000000000 : ℝ) := by norm_num
    linear_combination (561813/250000000000 : ℝ)*(base11) + (575669/100000000000 : ℝ)*(base15) + (392973519753/1000000000000 : ℝ)*(base40) + (11306564161/31250000000 : ℝ)*(base50) + (3627239700211/1000000000000 : ℝ)*(major_s1_0) + (3627239700211/1000000000000 : ℝ)*(major_s1_1) + (3627239700211/1000000000000 : ℝ)*(major_s1_2) + (331811/50000000000 : ℝ)*(sp_s1_0) + (846653/62500000000 : ℝ)*(sp_s1_9) + (821967/200000000000 : ℝ)*(sp_s1_15) + (42936994103/7812500000 : ℝ)*(sp_s1_21) + (1373983565533/250000000000 : ℝ)*(sp_s1_22) + (85873915347/15625000000 : ℝ)*(sp_s1_23) + (219816722433/125000000000 : ℝ)*(sp_s1_27) + (219816722433/125000000000 : ℝ)*(f.failure) + (343496508041/62500000000 : ℝ)*(f.sum) + (1802735415384247/6293000000000000000000000000 : ℝ)*base63 + (1027783528350829/6293000000000000000000000000 : ℝ)*base65 + (789330393782891/3146500000000000000000000000 : ℝ)*base66 + (2083681124068441/3146500000000000000000000000 : ℝ)*base68 + (1922846764289347/6293000000000000000000000000 : ℝ)*base71 + (3143795996301571/6293000000000000000000000000 : ℝ)*base72 + (3052271693787629/6293000000000000000000000000 : ℝ)*base75 + (1623579237521309/3146500000000000000000000000 : ℝ)*base77 + (5378862819108953/6293000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1049/2500000000000000 : ℝ)*base87 + (1049/2500000000000000 : ℝ)*base89 + (1049/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_positive87 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 87=![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c326087 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
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

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_positive87 p hpa hpb X hX

#print axioms solution
