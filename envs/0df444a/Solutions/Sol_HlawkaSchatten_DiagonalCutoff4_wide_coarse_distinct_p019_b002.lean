-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b002
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:15.580391+00:00
-- url     : https://prove2.me/submissions/9916c72f-4eed-4e1b-b7e9-3fb5e9299d77

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
theorem collision_support_c319006_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-736495009/2500000000 : ℝ)*x 0 + (-2353298951/5000000000 : ℝ)*x 1 + (-2353298959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (736495009/2500000000 : ℝ)^81 ≤ (5451533457577/25000000000000 : ℝ)^65 := by
    have hnat : (736495009 : ℕ)^81*25000000000000^65 ≤ 5451533457577^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736495009 2500000000 5451533457577 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353298951/5000000000 : ℝ)^81 ≤ (7819386598499/20000000000000 : ℝ)^65 := by
    have hnat : (2353298951 : ℕ)^81*20000000000000^65 ≤ 7819386598499^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353298951 5000000000 7819386598499 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2353298959/5000000000 : ℝ)^81 ≤ (977423328953/2500000000000 : ℝ)^65 := by
    have hnat : (2353298959 : ℕ)^81*2500000000000^65 ≤ 977423328953^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353298959 5000000000 977423328953 2500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-736495009/2500000000 : ℝ), (-2353298951/5000000000 : ℝ), (-2353298959/5000000000 : ℝ)] ![(5451533457577/25000000000000 : ℝ), (7819386598499/20000000000000 : ℝ), (977423328953/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-736495009/2500000000 : ℝ)|^81 ≤ (5451533457577/25000000000000 : ℝ)^65
        have hw : |(-736495009/2500000000 : ℝ)|=(736495009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2353298951/5000000000 : ℝ)|^81 ≤ (7819386598499/20000000000000 : ℝ)^65
        have hw : |(-2353298951/5000000000 : ℝ)|=(2353298951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2353298959/5000000000 : ℝ)|^81 ≤ (977423328953/2500000000000 : ℝ)^65
        have hw : |(-2353298959/5000000000 : ℝ)|=(2353298959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319006_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5806725669/10000000000 : ℝ)*x 0 + (811369561/2500000000 : ℝ)*x 1 + (-649095651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5806725669/10000000000 : ℝ)^81 ≤ (6349391490083/12500000000000 : ℝ)^65 := by
    have hnat : (5806725669 : ℕ)^81*12500000000000^65 ≤ 6349391490083^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5806725669 10000000000 6349391490083 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (811369561/2500000000 : ℝ)^81 ≤ (3075304247339/12500000000000 : ℝ)^65 := by
    have hnat : (811369561 : ℕ)^81*12500000000000^65 ≤ 3075304247339^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811369561 2500000000 3075304247339 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649095651/2000000000 : ℝ)^81 ≤ (24602434082623/100000000000000 : ℝ)^65 := by
    have hnat : (649095651 : ℕ)^81*100000000000000^65 ≤ 24602434082623^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649095651 2000000000 24602434082623 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5806725669/10000000000 : ℝ), (811369561/2500000000 : ℝ), (-649095651/2000000000 : ℝ)] ![(6349391490083/12500000000000 : ℝ), (3075304247339/12500000000000 : ℝ), (24602434082623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5806725669/10000000000 : ℝ)|^81 ≤ (6349391490083/12500000000000 : ℝ)^65
        have hw : |(5806725669/10000000000 : ℝ)|=(5806725669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(811369561/2500000000 : ℝ)|^81 ≤ (3075304247339/12500000000000 : ℝ)^65
        have hw : |(811369561/2500000000 : ℝ)|=(811369561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649095651/2000000000 : ℝ)|^81 ≤ (24602434082623/100000000000000 : ℝ)^65
        have hw : |(-649095651/2000000000 : ℝ)|=(649095651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319006_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (736495009/2500000000 : ℝ)*x 0 + (-2353298951/5000000000 : ℝ)*x 1 + (2353298959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (736495009/2500000000 : ℝ)^81 ≤ (5451533457577/25000000000000 : ℝ)^65 := by
    have hnat : (736495009 : ℕ)^81*25000000000000^65 ≤ 5451533457577^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736495009 2500000000 5451533457577 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353298951/5000000000 : ℝ)^81 ≤ (7819386598499/20000000000000 : ℝ)^65 := by
    have hnat : (2353298951 : ℕ)^81*20000000000000^65 ≤ 7819386598499^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353298951 5000000000 7819386598499 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2353298959/5000000000 : ℝ)^81 ≤ (977423328953/2500000000000 : ℝ)^65 := by
    have hnat : (2353298959 : ℕ)^81*2500000000000^65 ≤ 977423328953^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353298959 5000000000 977423328953 2500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(736495009/2500000000 : ℝ), (-2353298951/5000000000 : ℝ), (2353298959/5000000000 : ℝ)] ![(5451533457577/25000000000000 : ℝ), (7819386598499/20000000000000 : ℝ), (977423328953/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(736495009/2500000000 : ℝ)|^81 ≤ (5451533457577/25000000000000 : ℝ)^65
        have hw : |(736495009/2500000000 : ℝ)|=(736495009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2353298951/5000000000 : ℝ)|^81 ≤ (7819386598499/20000000000000 : ℝ)^65
        have hw : |(-2353298951/5000000000 : ℝ)|=(2353298951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2353298959/5000000000 : ℝ)|^81 ≤ (977423328953/2500000000000 : ℝ)^65
        have hw : |(2353298959/5000000000 : ℝ)|=(2353298959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319006_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5806725669/10000000000 : ℝ)*x 0 + (-811369561/2500000000 : ℝ)*x 1 + (-649095651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5806725669/10000000000 : ℝ)^81 ≤ (6349391490083/12500000000000 : ℝ)^65 := by
    have hnat : (5806725669 : ℕ)^81*12500000000000^65 ≤ 6349391490083^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5806725669 10000000000 6349391490083 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (811369561/2500000000 : ℝ)^81 ≤ (3075304247339/12500000000000 : ℝ)^65 := by
    have hnat : (811369561 : ℕ)^81*12500000000000^65 ≤ 3075304247339^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811369561 2500000000 3075304247339 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649095651/2000000000 : ℝ)^81 ≤ (24602434082623/100000000000000 : ℝ)^65 := by
    have hnat : (649095651 : ℕ)^81*100000000000000^65 ≤ 24602434082623^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649095651 2000000000 24602434082623 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5806725669/10000000000 : ℝ), (-811369561/2500000000 : ℝ), (-649095651/2000000000 : ℝ)] ![(6349391490083/12500000000000 : ℝ), (3075304247339/12500000000000 : ℝ), (24602434082623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5806725669/10000000000 : ℝ)|^81 ≤ (6349391490083/12500000000000 : ℝ)^65
        have hw : |(5806725669/10000000000 : ℝ)|=(5806725669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-811369561/2500000000 : ℝ)|^81 ≤ (3075304247339/12500000000000 : ℝ)^65
        have hw : |(-811369561/2500000000 : ℝ)|=(811369561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649095651/2000000000 : ℝ)|^81 ≤ (24602434082623/100000000000000 : ℝ)^65
        have hw : |(-649095651/2000000000 : ℝ)|=(649095651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319006 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-736495009/2500000000 : ℝ)*X 0 0+(-2353298951/5000000000 : ℝ)*X 0 1+(-2353298959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319006_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5806725669/10000000000 : ℝ)*X 1 0+(811369561/2500000000 : ℝ)*X 1 1+(-649095651/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319006_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((736495009/2500000000 : ℝ)*X 2 0+(-2353298951/5000000000 : ℝ)*X 2 1+(2353298959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319006_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5806725669/10000000000 : ℝ)*X 0 0+(-811369561/2500000000 : ℝ)*X 0 1+(-649095651/2000000000 : ℝ)*X 0 2+(5806725669/10000000000 : ℝ)*X 1 0+(-811369561/2500000000 : ℝ)*X 1 1+(-649095651/2000000000 : ℝ)*X 1 2+(5806725669/10000000000 : ℝ)*X 2 0+(-811369561/2500000000 : ℝ)*X 2 1+(-649095651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319006_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-20009988007126174717496699163/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483450670727/500000000000 : ℝ)*(base3) + (18259/1000000000000 : ℝ)*(base22) + (391861128897/500000000000 : ℝ)*(base39) + (38189041233/125000000000 : ℝ)*(base40) + (383383759659/500000000000 : ℝ)*(base50) + (5857/500000000000 : ℝ)*(base54) + (100547294333/250000000000 : ℝ)*(base59) + (92547/50000 : ℝ)*(major_s0_0) + (92547/50000 : ℝ)*(major_s0_1) + (925469994143/500000000000 : ℝ)*(major_s0_2) + (533599676641/200000000000 : ℝ)*(sp_s0_0) + (1817449853459/500000000000 : ℝ)*(sp_s0_1) + (266799833549/100000000000 : ℝ)*(sp_s0_2) + (33098646831/1000000000000 : ℝ)*(sp_s0_6) + (2667998365463/1000000000000 : ℝ)*(f.sum) + (2309093597374747/5000000000000000000000000000 : ℝ)*base63 + (176069888899721/5000000000000000000000000000 : ℝ)*base65 + (35482201166583/2000000000000000000000 : ℝ)*base67 + (75920533625253/5000000000000000000000000000 : ℝ)*base68 + (1363478567899721/5000000000000000000000000000 : ℝ)*base71 + (114971113/400000000000000000000 : ℝ)*base72 + (3731372161/10000000000000000000000 : ℝ)*base75 + (335333001/2500000000000000000000 : ℝ)*base77 + (952869983/2000000000000000000000 : ℝ)*base78 + (8871/500000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c319007_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-588109309/2500000000 : ℝ)*x 0 + (-1263244513/2000000000 : ℝ)*x 1 + (1754573293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (588109309/2500000000 : ℝ)^81 ≤ (16474596807797/100000000000000 : ℝ)^65 := by
    have hnat : (588109309 : ℕ)^81*100000000000000^65 ≤ 16474596807797^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588109309 2500000000 16474596807797 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263244513/2000000000 : ℝ)^81 ≤ (28203905889127/50000000000000 : ℝ)^65 := by
    have hnat : (1263244513 : ℕ)^81*50000000000000^65 ≤ 28203905889127^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263244513 2000000000 28203905889127 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1754573293/5000000000 : ℝ)^81 ≤ (13558795702033/50000000000000 : ℝ)^65 := by
    have hnat : (1754573293 : ℕ)^81*50000000000000^65 ≤ 13558795702033^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754573293 5000000000 13558795702033 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-588109309/2500000000 : ℝ), (-1263244513/2000000000 : ℝ), (1754573293/5000000000 : ℝ)] ![(16474596807797/100000000000000 : ℝ), (28203905889127/50000000000000 : ℝ), (13558795702033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-588109309/2500000000 : ℝ)|^81 ≤ (16474596807797/100000000000000 : ℝ)^65
        have hw : |(-588109309/2500000000 : ℝ)|=(588109309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1263244513/2000000000 : ℝ)|^81 ≤ (28203905889127/50000000000000 : ℝ)^65
        have hw : |(-1263244513/2000000000 : ℝ)|=(1263244513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1754573293/5000000000 : ℝ)|^81 ≤ (13558795702033/50000000000000 : ℝ)^65
        have hw : |(1754573293/5000000000 : ℝ)|=(1754573293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1134081281/2000000000 : ℝ)*x 0 + (605683989/2000000000 : ℝ)*x 1 + (1806298177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134081281/2000000000 : ℝ)^81 ≤ (49313448145773/100000000000000 : ℝ)^65 := by
    have hnat : (1134081281 : ℕ)^81*100000000000000^65 ≤ 49313448145773^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134081281 2000000000 49313448145773 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605683989/2000000000 : ℝ)^81 ≤ (22569162572323/100000000000000 : ℝ)^65 := by
    have hnat : (605683989 : ℕ)^81*100000000000000^65 ≤ 22569162572323^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605683989 2000000000 22569162572323 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1806298177/5000000000 : ℝ)^81 ≤ (28117389273749/100000000000000 : ℝ)^65 := by
    have hnat : (1806298177 : ℕ)^81*100000000000000^65 ≤ 28117389273749^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806298177 5000000000 28117389273749 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1134081281/2000000000 : ℝ), (605683989/2000000000 : ℝ), (1806298177/5000000000 : ℝ)] ![(49313448145773/100000000000000 : ℝ), (22569162572323/100000000000000 : ℝ), (28117389273749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1134081281/2000000000 : ℝ)|^81 ≤ (49313448145773/100000000000000 : ℝ)^65
        have hw : |(1134081281/2000000000 : ℝ)|=(1134081281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605683989/2000000000 : ℝ)|^81 ≤ (22569162572323/100000000000000 : ℝ)^65
        have hw : |(605683989/2000000000 : ℝ)|=(605683989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1806298177/5000000000 : ℝ)|^81 ≤ (28117389273749/100000000000000 : ℝ)^65
        have hw : |(1806298177/5000000000 : ℝ)|=(1806298177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (449730211/1250000000 : ℝ)*x 0 + (-16952151/50000000 : ℝ)*x 1 + (-670865607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449730211/1250000000 : ℝ)^81 ≤ (1748397230807/6250000000000 : ℝ)^65 := by
    have hnat : (449730211 : ℕ)^81*6250000000000^65 ≤ 1748397230807^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449730211 1250000000 1748397230807 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16952151/50000000 : ℝ)^81 ≤ (6494791755813/25000000000000 : ℝ)^65 := by
    have hnat : (16952151 : ℕ)^81*25000000000000^65 ≤ 6494791755813^65*50000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16952151 50000000 6494791755813 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670865607/1250000000 : ℝ)^81 ≤ (11511619315287/25000000000000 : ℝ)^65 := by
    have hnat : (670865607 : ℕ)^81*25000000000000^65 ≤ 11511619315287^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670865607 1250000000 11511619315287 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449730211/1250000000 : ℝ), (-16952151/50000000 : ℝ), (-670865607/1250000000 : ℝ)] ![(1748397230807/6250000000000 : ℝ), (6494791755813/25000000000000 : ℝ), (11511619315287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449730211/1250000000 : ℝ)|^81 ≤ (1748397230807/6250000000000 : ℝ)^65
        have hw : |(449730211/1250000000 : ℝ)|=(449730211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16952151/50000000 : ℝ)|^81 ≤ (6494791755813/25000000000000 : ℝ)^65
        have hw : |(-16952151/50000000 : ℝ)|=(16952151/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-670865607/1250000000 : ℝ)|^81 ≤ (11511619315287/25000000000000 : ℝ)^65
        have hw : |(-670865607/1250000000 : ℝ)|=(670865607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026597661/5000000000 : ℝ)*x 0 + (-6897132983/10000000000 : ℝ)*x 1 + (1545422381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026597661/5000000000 : ℝ)^81 ≤ (3476340757781/25000000000000 : ℝ)^65 := by
    have hnat : (1026597661 : ℕ)^81*25000000000000^65 ≤ 3476340757781^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026597661 5000000000 3476340757781 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6897132983/10000000000 : ℝ)^81 ≤ (31472138899519/50000000000000 : ℝ)^65 := by
    have hnat : (6897132983 : ℕ)^81*50000000000000^65 ≤ 31472138899519^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6897132983 10000000000 31472138899519 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1545422381/5000000000 : ℝ)^81 ≤ (23150359150457/100000000000000 : ℝ)^65 := by
    have hnat : (1545422381 : ℕ)^81*100000000000000^65 ≤ 23150359150457^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545422381 5000000000 23150359150457 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026597661/5000000000 : ℝ), (-6897132983/10000000000 : ℝ), (1545422381/5000000000 : ℝ)] ![(3476340757781/25000000000000 : ℝ), (31472138899519/50000000000000 : ℝ), (23150359150457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026597661/5000000000 : ℝ)|^81 ≤ (3476340757781/25000000000000 : ℝ)^65
        have hw : |(-1026597661/5000000000 : ℝ)|=(1026597661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6897132983/10000000000 : ℝ)|^81 ≤ (31472138899519/50000000000000 : ℝ)^65
        have hw : |(-6897132983/10000000000 : ℝ)|=(6897132983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1545422381/5000000000 : ℝ)|^81 ≤ (23150359150457/100000000000000 : ℝ)^65
        have hw : |(1545422381/5000000000 : ℝ)|=(1545422381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4976833299/10000000000 : ℝ)*x 0 + (1650664599/5000000000 : ℝ)*x 1 + (2051716969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4976833299/10000000000 : ℝ)^81 ≤ (10478447489183/25000000000000 : ℝ)^65 := by
    have hnat : (4976833299 : ℕ)^81*25000000000000^65 ≤ 10478447489183^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976833299 10000000000 10478447489183 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1650664599/5000000000 : ℝ)^81 ≤ (25131142803881/100000000000000 : ℝ)^65 := by
    have hnat : (1650664599 : ℕ)^81*100000000000000^65 ≤ 25131142803881^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650664599 5000000000 25131142803881 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051716969/5000000000 : ℝ)^81 ≤ (6591013446097/20000000000000 : ℝ)^65 := by
    have hnat : (2051716969 : ℕ)^81*20000000000000^65 ≤ 6591013446097^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051716969 5000000000 6591013446097 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4976833299/10000000000 : ℝ), (1650664599/5000000000 : ℝ), (2051716969/5000000000 : ℝ)] ![(10478447489183/25000000000000 : ℝ), (25131142803881/100000000000000 : ℝ), (6591013446097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4976833299/10000000000 : ℝ)|^81 ≤ (10478447489183/25000000000000 : ℝ)^65
        have hw : |(4976833299/10000000000 : ℝ)|=(4976833299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1650664599/5000000000 : ℝ)|^81 ≤ (25131142803881/100000000000000 : ℝ)^65
        have hw : |(1650664599/5000000000 : ℝ)|=(1650664599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2051716969/5000000000 : ℝ)|^81 ≤ (6591013446097/20000000000000 : ℝ)^65
        have hw : |(2051716969/5000000000 : ℝ)|=(2051716969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (924513419/2500000000 : ℝ)*x 0 + (-3059287609/10000000000 : ℝ)*x 1 + (-2783493053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924513419/2500000000 : ℝ)^81 ≤ (7237159818973/25000000000000 : ℝ)^65 := by
    have hnat : (924513419 : ℕ)^81*25000000000000^65 ≤ 7237159818973^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924513419 2500000000 7237159818973 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059287609/10000000000 : ℝ)^81 ≤ (914247453551/4000000000000 : ℝ)^65 := by
    have hnat : (3059287609 : ℕ)^81*4000000000000^65 ≤ 914247453551^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059287609 10000000000 914247453551 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2783493053/5000000000 : ℝ)^81 ≤ (481951743649/1000000000000 : ℝ)^65 := by
    have hnat : (2783493053 : ℕ)^81*1000000000000^65 ≤ 481951743649^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783493053 5000000000 481951743649 1000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(924513419/2500000000 : ℝ), (-3059287609/10000000000 : ℝ), (-2783493053/5000000000 : ℝ)] ![(7237159818973/25000000000000 : ℝ), (914247453551/4000000000000 : ℝ), (481951743649/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(924513419/2500000000 : ℝ)|^81 ≤ (7237159818973/25000000000000 : ℝ)^65
        have hw : |(924513419/2500000000 : ℝ)|=(924513419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3059287609/10000000000 : ℝ)|^81 ≤ (914247453551/4000000000000 : ℝ)^65
        have hw : |(-3059287609/10000000000 : ℝ)|=(3059287609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2783493053/5000000000 : ℝ)|^81 ≤ (481951743649/1000000000000 : ℝ)^65
        have hw : |(-2783493053/5000000000 : ℝ)|=(2783493053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-63509793/250000000 : ℝ)*x 0 + (-6290581487/10000000000 : ℝ)*x 1 + (3366062841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63509793/250000000 : ℝ)^81 ≤ (18130705523279/100000000000000 : ℝ)^65 := by
    have hnat : (63509793 : ℕ)^81*100000000000000^65 ≤ 18130705523279^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63509793 250000000 18130705523279 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6290581487/10000000000 : ℝ)^81 ≤ (56122596685379/100000000000000 : ℝ)^65 := by
    have hnat : (6290581487 : ℕ)^81*100000000000000^65 ≤ 56122596685379^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6290581487 10000000000 56122596685379 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3366062841/10000000000 : ℝ)^81 ≤ (25746697775961/100000000000000 : ℝ)^65 := by
    have hnat : (3366062841 : ℕ)^81*100000000000000^65 ≤ 25746697775961^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3366062841 10000000000 25746697775961 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63509793/250000000 : ℝ), (-6290581487/10000000000 : ℝ), (3366062841/10000000000 : ℝ)] ![(18130705523279/100000000000000 : ℝ), (56122596685379/100000000000000 : ℝ), (25746697775961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63509793/250000000 : ℝ)|^81 ≤ (18130705523279/100000000000000 : ℝ)^65
        have hw : |(-63509793/250000000 : ℝ)|=(63509793/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6290581487/10000000000 : ℝ)|^81 ≤ (56122596685379/100000000000000 : ℝ)^65
        have hw : |(-6290581487/10000000000 : ℝ)|=(6290581487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3366062841/10000000000 : ℝ)|^81 ≤ (25746697775961/100000000000000 : ℝ)^65
        have hw : |(3366062841/10000000000 : ℝ)|=(3366062841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5670048021/10000000000 : ℝ)*x 0 + (1504837243/5000000000 : ℝ)*x 1 + (181546033/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5670048021/10000000000 : ℝ)^81 ≤ (12327391061351/25000000000000 : ℝ)^65 := by
    have hnat : (5670048021 : ℕ)^81*25000000000000^65 ≤ 12327391061351^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670048021 10000000000 12327391061351 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1504837243/5000000000 : ℝ)^81 ≤ (22395208104169/100000000000000 : ℝ)^65 := by
    have hnat : (1504837243 : ℕ)^81*100000000000000^65 ≤ 22395208104169^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504837243 5000000000 22395208104169 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181546033/500000000 : ℝ)^81 ≤ (28295227634897/100000000000000 : ℝ)^65 := by
    have hnat : (181546033 : ℕ)^81*100000000000000^65 ≤ 28295227634897^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181546033 500000000 28295227634897 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5670048021/10000000000 : ℝ), (1504837243/5000000000 : ℝ), (181546033/500000000 : ℝ)] ![(12327391061351/25000000000000 : ℝ), (22395208104169/100000000000000 : ℝ), (28295227634897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5670048021/10000000000 : ℝ)|^81 ≤ (12327391061351/25000000000000 : ℝ)^65
        have hw : |(5670048021/10000000000 : ℝ)|=(5670048021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1504837243/5000000000 : ℝ)|^81 ≤ (22395208104169/100000000000000 : ℝ)^65
        have hw : |(1504837243/5000000000 : ℝ)|=(1504837243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181546033/500000000 : ℝ)|^81 ≤ (28295227634897/100000000000000 : ℝ)^65
        have hw : |(181546033/500000000 : ℝ)|=(181546033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3436231311/10000000000 : ℝ)*x 0 + (-3378331731/10000000000 : ℝ)*x 1 + (-5522812067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3436231311/10000000000 : ℝ)^81 ≤ (6604307646707/25000000000000 : ℝ)^65 := by
    have hnat : (3436231311 : ℕ)^81*25000000000000^65 ≤ 6604307646707^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3436231311 10000000000 6604307646707 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3378331731/10000000000 : ℝ)^81 ≤ (12931846866379/50000000000000 : ℝ)^65 := by
    have hnat : (3378331731 : ℕ)^81*50000000000000^65 ≤ 12931846866379^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378331731 10000000000 12931846866379 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522812067/10000000000 : ℝ)^81 ≤ (47719075665041/100000000000000 : ℝ)^65 := by
    have hnat : (5522812067 : ℕ)^81*100000000000000^65 ≤ 47719075665041^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522812067 10000000000 47719075665041 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3436231311/10000000000 : ℝ), (-3378331731/10000000000 : ℝ), (-5522812067/10000000000 : ℝ)] ![(6604307646707/25000000000000 : ℝ), (12931846866379/50000000000000 : ℝ), (47719075665041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3436231311/10000000000 : ℝ)|^81 ≤ (6604307646707/25000000000000 : ℝ)^65
        have hw : |(3436231311/10000000000 : ℝ)|=(3436231311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3378331731/10000000000 : ℝ)|^81 ≤ (12931846866379/50000000000000 : ℝ)^65
        have hw : |(-3378331731/10000000000 : ℝ)|=(3378331731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5522812067/10000000000 : ℝ)|^81 ≤ (47719075665041/100000000000000 : ℝ)^65
        have hw : |(-5522812067/10000000000 : ℝ)|=(5522812067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_17 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1557/10000000000 : ℝ)*x 0 + (-9999999973/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557/10000000000 : ℝ)^81 ≤ (328507/100000000000000 : ℝ)^65 := by
    have hnat : (1557 : ℕ)^81*100000000000000^65 ≤ 328507^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557 10000000000 328507 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999973/10000000000 : ℝ)^81 ≤ (99999999663539/100000000000000 : ℝ)^65 := by
    have hnat : (9999999973 : ℕ)^81*100000000000000^65 ≤ 99999999663539^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999973 10000000000 99999999663539 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^81 ≤ (0 : ℝ)^65 := by
    have hnat : (0 : ℕ)^81*1^65 ≤ 0^65*1^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1557/10000000000 : ℝ), (-9999999973/10000000000 : ℝ), (0 : ℝ)] ![(328507/100000000000000 : ℝ), (99999999663539/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1557/10000000000 : ℝ)|^81 ≤ (328507/100000000000000 : ℝ)^65
        have hw : |(-1557/10000000000 : ℝ)|=(1557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9999999973/10000000000 : ℝ)|^81 ≤ (99999999663539/100000000000000 : ℝ)^65
        have hw : |(-9999999973/10000000000 : ℝ)|=(9999999973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^81 ≤ (0 : ℝ)^65
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939705813/10000000000 : ℝ)*x 0 + (-854245869/1250000000 : ℝ)*x 1 + (817098889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939705813/10000000000 : ℝ)^81 ≤ (2590832326589/20000000000000 : ℝ)^65 := by
    have hnat : (1939705813 : ℕ)^81*20000000000000^65 ≤ 2590832326589^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939705813 10000000000 2590832326589 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854245869/1250000000 : ℝ)^81 ≤ (62226728124177/100000000000000 : ℝ)^65 := by
    have hnat : (854245869 : ℕ)^81*100000000000000^65 ≤ 62226728124177^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854245869 1250000000 62226728124177 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (817098889/2500000000 : ℝ)^81 ≤ (24819110233209/100000000000000 : ℝ)^65 := by
    have hnat : (817098889 : ℕ)^81*100000000000000^65 ≤ 24819110233209^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817098889 2500000000 24819110233209 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939705813/10000000000 : ℝ), (-854245869/1250000000 : ℝ), (817098889/2500000000 : ℝ)] ![(2590832326589/20000000000000 : ℝ), (62226728124177/100000000000000 : ℝ), (24819110233209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939705813/10000000000 : ℝ)|^81 ≤ (2590832326589/20000000000000 : ℝ)^65
        have hw : |(-1939705813/10000000000 : ℝ)|=(1939705813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854245869/1250000000 : ℝ)|^81 ≤ (62226728124177/100000000000000 : ℝ)^65
        have hw : |(-854245869/1250000000 : ℝ)|=(854245869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(817098889/2500000000 : ℝ)|^81 ≤ (24819110233209/100000000000000 : ℝ)^65
        have hw : |(817098889/2500000000 : ℝ)|=(817098889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3153916129/5000000000 : ℝ)*x 0 + (2769101619/10000000000 : ℝ)*x 1 + (1564055387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3153916129/5000000000 : ℝ)^81 ≤ (11262890378633/20000000000000 : ℝ)^65 := by
    have hnat : (3153916129 : ℕ)^81*20000000000000^65 ≤ 11262890378633^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3153916129 5000000000 11262890378633 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2769101619/10000000000 : ℝ)^81 ≤ (20186845880017/100000000000000 : ℝ)^65 := by
    have hnat : (2769101619 : ℕ)^81*100000000000000^65 ≤ 20186845880017^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769101619 10000000000 20186845880017 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564055387/5000000000 : ℝ)^81 ≤ (11749351106417/50000000000000 : ℝ)^65 := by
    have hnat : (1564055387 : ℕ)^81*50000000000000^65 ≤ 11749351106417^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564055387 5000000000 11749351106417 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3153916129/5000000000 : ℝ), (2769101619/10000000000 : ℝ), (1564055387/5000000000 : ℝ)] ![(11262890378633/20000000000000 : ℝ), (20186845880017/100000000000000 : ℝ), (11749351106417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3153916129/5000000000 : ℝ)|^81 ≤ (11262890378633/20000000000000 : ℝ)^65
        have hw : |(3153916129/5000000000 : ℝ)|=(3153916129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2769101619/10000000000 : ℝ)|^81 ≤ (20186845880017/100000000000000 : ℝ)^65
        have hw : |(2769101619/10000000000 : ℝ)|=(2769101619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1564055387/5000000000 : ℝ)|^81 ≤ (11749351106417/50000000000000 : ℝ)^65
        have hw : |(1564055387/5000000000 : ℝ)|=(1564055387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (393325303/1250000000 : ℝ)*x 0 + (-3904340153/10000000000 : ℝ)*x 1 + (-5302010909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393325303/1250000000 : ℝ)^81 ≤ (11835966379409/50000000000000 : ℝ)^65 := by
    have hnat : (393325303 : ℕ)^81*50000000000000^65 ≤ 11835966379409^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393325303 1250000000 11835966379409 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3904340153/10000000000 : ℝ)^81 ≤ (30974587363861/100000000000000 : ℝ)^65 := by
    have hnat : (3904340153 : ℕ)^81*100000000000000^65 ≤ 30974587363861^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3904340153 10000000000 30974587363861 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5302010909/10000000000 : ℝ)^81 ≤ (45353479857729/100000000000000 : ℝ)^65 := by
    have hnat : (5302010909 : ℕ)^81*100000000000000^65 ≤ 45353479857729^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302010909 10000000000 45353479857729 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(393325303/1250000000 : ℝ), (-3904340153/10000000000 : ℝ), (-5302010909/10000000000 : ℝ)] ![(11835966379409/50000000000000 : ℝ), (30974587363861/100000000000000 : ℝ), (45353479857729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(393325303/1250000000 : ℝ)|^81 ≤ (11835966379409/50000000000000 : ℝ)^65
        have hw : |(393325303/1250000000 : ℝ)|=(393325303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3904340153/10000000000 : ℝ)|^81 ≤ (30974587363861/100000000000000 : ℝ)^65
        have hw : |(-3904340153/10000000000 : ℝ)|=(3904340153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5302010909/10000000000 : ℝ)|^81 ≤ (45353479857729/100000000000000 : ℝ)^65
        have hw : |(-5302010909/10000000000 : ℝ)|=(5302010909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-170015071/500000000 : ℝ)*x 0 + (-2249671727/5000000000 : ℝ)*x 1 + (1124835549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170015071/500000000 : ℝ)^81 ≤ (13036728810639/50000000000000 : ℝ)^65 := by
    have hnat : (170015071 : ℕ)^81*50000000000000^65 ≤ 13036728810639^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170015071 500000000 13036728810639 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249671727/5000000000 : ℝ)^81 ≤ (18481638812283/50000000000000 : ℝ)^65 := by
    have hnat : (2249671727 : ℕ)^81*50000000000000^65 ≤ 18481638812283^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249671727 5000000000 18481638812283 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124835549/2500000000 : ℝ)^81 ≤ (36963264745819/100000000000000 : ℝ)^65 := by
    have hnat : (1124835549 : ℕ)^81*100000000000000^65 ≤ 36963264745819^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124835549 2500000000 36963264745819 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170015071/500000000 : ℝ), (-2249671727/5000000000 : ℝ), (1124835549/2500000000 : ℝ)] ![(13036728810639/50000000000000 : ℝ), (18481638812283/50000000000000 : ℝ), (36963264745819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170015071/500000000 : ℝ)|^81 ≤ (13036728810639/50000000000000 : ℝ)^65
        have hw : |(-170015071/500000000 : ℝ)|=(170015071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249671727/5000000000 : ℝ)|^81 ≤ (18481638812283/50000000000000 : ℝ)^65
        have hw : |(-2249671727/5000000000 : ℝ)|=(2249671727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124835549/2500000000 : ℝ)|^81 ≤ (36963264745819/100000000000000 : ℝ)^65
        have hw : |(1124835549/2500000000 : ℝ)|=(1124835549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5189190723/10000000000 : ℝ)*x 0 + (359253959/1000000000 : ℝ)*x 1 + (718507717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189190723/10000000000 : ℝ)^81 ≤ (22077013145121/50000000000000 : ℝ)^65 := by
    have hnat : (5189190723 : ℕ)^81*50000000000000^65 ≤ 22077013145121^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189190723 10000000000 22077013145121 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359253959/1000000000 : ℝ)^81 ≤ (6980747928811/25000000000000 : ℝ)^65 := by
    have hnat : (359253959 : ℕ)^81*25000000000000^65 ≤ 6980747928811^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359253959 1000000000 6980747928811 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (718507717/2000000000 : ℝ)^81 ≤ (27922981981093/100000000000000 : ℝ)^65 := by
    have hnat : (718507717 : ℕ)^81*100000000000000^65 ≤ 27922981981093^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718507717 2000000000 27922981981093 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189190723/10000000000 : ℝ), (359253959/1000000000 : ℝ), (718507717/2000000000 : ℝ)] ![(22077013145121/50000000000000 : ℝ), (6980747928811/25000000000000 : ℝ), (27922981981093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189190723/10000000000 : ℝ)|^81 ≤ (22077013145121/50000000000000 : ℝ)^65
        have hw : |(5189190723/10000000000 : ℝ)|=(5189190723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(359253959/1000000000 : ℝ)|^81 ≤ (6980747928811/25000000000000 : ℝ)^65
        have hw : |(359253959/1000000000 : ℝ)|=(359253959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(718507717/2000000000 : ℝ)|^81 ≤ (27922981981093/100000000000000 : ℝ)^65
        have hw : |(718507717/2000000000 : ℝ)|=(718507717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (170015071/500000000 : ℝ)*x 0 + (-2249671727/5000000000 : ℝ)*x 1 + (-1124835549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170015071/500000000 : ℝ)^81 ≤ (13036728810639/50000000000000 : ℝ)^65 := by
    have hnat : (170015071 : ℕ)^81*50000000000000^65 ≤ 13036728810639^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170015071 500000000 13036728810639 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249671727/5000000000 : ℝ)^81 ≤ (18481638812283/50000000000000 : ℝ)^65 := by
    have hnat : (2249671727 : ℕ)^81*50000000000000^65 ≤ 18481638812283^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249671727 5000000000 18481638812283 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124835549/2500000000 : ℝ)^81 ≤ (36963264745819/100000000000000 : ℝ)^65 := by
    have hnat : (1124835549 : ℕ)^81*100000000000000^65 ≤ 36963264745819^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124835549 2500000000 36963264745819 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170015071/500000000 : ℝ), (-2249671727/5000000000 : ℝ), (-1124835549/2500000000 : ℝ)] ![(13036728810639/50000000000000 : ℝ), (18481638812283/50000000000000 : ℝ), (36963264745819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170015071/500000000 : ℝ)|^81 ≤ (13036728810639/50000000000000 : ℝ)^65
        have hw : |(170015071/500000000 : ℝ)|=(170015071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249671727/5000000000 : ℝ)|^81 ≤ (18481638812283/50000000000000 : ℝ)^65
        have hw : |(-2249671727/5000000000 : ℝ)|=(2249671727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1124835549/2500000000 : ℝ)|^81 ≤ (36963264745819/100000000000000 : ℝ)^65
        have hw : |(-1124835549/2500000000 : ℝ)|=(1124835549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319007_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5189190723/10000000000 : ℝ)*x 0 + (-359253959/1000000000 : ℝ)*x 1 + (718507717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189190723/10000000000 : ℝ)^81 ≤ (22077013145121/50000000000000 : ℝ)^65 := by
    have hnat : (5189190723 : ℕ)^81*50000000000000^65 ≤ 22077013145121^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189190723 10000000000 22077013145121 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359253959/1000000000 : ℝ)^81 ≤ (6980747928811/25000000000000 : ℝ)^65 := by
    have hnat : (359253959 : ℕ)^81*25000000000000^65 ≤ 6980747928811^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359253959 1000000000 6980747928811 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (718507717/2000000000 : ℝ)^81 ≤ (27922981981093/100000000000000 : ℝ)^65 := by
    have hnat : (718507717 : ℕ)^81*100000000000000^65 ≤ 27922981981093^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718507717 2000000000 27922981981093 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189190723/10000000000 : ℝ), (-359253959/1000000000 : ℝ), (718507717/2000000000 : ℝ)] ![(22077013145121/50000000000000 : ℝ), (6980747928811/25000000000000 : ℝ), (27922981981093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189190723/10000000000 : ℝ)|^81 ≤ (22077013145121/50000000000000 : ℝ)^65
        have hw : |(5189190723/10000000000 : ℝ)|=(5189190723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359253959/1000000000 : ℝ)|^81 ≤ (6980747928811/25000000000000 : ℝ)^65
        have hw : |(-359253959/1000000000 : ℝ)|=(359253959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(718507717/2000000000 : ℝ)|^81 ≤ (27922981981093/100000000000000 : ℝ)^65
        have hw : |(718507717/2000000000 : ℝ)|=(718507717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319007 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-588109309/2500000000 : ℝ)*X 0 0+(-1263244513/2000000000 : ℝ)*X 0 1+(1754573293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1134081281/2000000000 : ℝ)*X 1 0+(605683989/2000000000 : ℝ)*X 1 1+(1806298177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((449730211/1250000000 : ℝ)*X 2 0+(-16952151/50000000 : ℝ)*X 2 1+(-670865607/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1026597661/5000000000 : ℝ)*X 0 0+(-6897132983/10000000000 : ℝ)*X 0 1+(1545422381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4976833299/10000000000 : ℝ)*X 1 0+(1650664599/5000000000 : ℝ)*X 1 1+(2051716969/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((924513419/2500000000 : ℝ)*X 2 0+(-3059287609/10000000000 : ℝ)*X 2 1+(-2783493053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-63509793/250000000 : ℝ)*X 0 0+(-6290581487/10000000000 : ℝ)*X 0 1+(3366062841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((5670048021/10000000000 : ℝ)*X 1 0+(1504837243/5000000000 : ℝ)*X 1 1+(181546033/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3436231311/10000000000 : ℝ)*X 2 0+(-3378331731/10000000000 : ℝ)*X 2 1+(-5522812067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((-1557/10000000000 : ℝ)*X 0 0+(-9999999973/10000000000 : ℝ)*X 0 1+(-1557/10000000000 : ℝ)*X 2 0+(-9999999973/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_17 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1939705813/10000000000 : ℝ)*X 0 0+(-854245869/1250000000 : ℝ)*X 0 1+(817098889/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3153916129/5000000000 : ℝ)*X 1 0+(2769101619/10000000000 : ℝ)*X 1 1+(1564055387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((393325303/1250000000 : ℝ)*X 2 0+(-3904340153/10000000000 : ℝ)*X 2 1+(-5302010909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((44487/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44487/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18666591413606823503247/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1844894211647/500000000000 : ℝ)*(base3) + (245169522609/200000000000 : ℝ)*(base7) + (131196735609/125000000000 : ℝ)*(base40) + (734597261553/500000000000 : ℝ)*(base49) + (2280303301661/500000000000 : ℝ)*(major_s0_0) + (634070069681/50000000000 : ℝ)*(major_s0_1) + (2280303301661/500000000000 : ℝ)*(major_s0_2) + (5961005893107/1000000000000 : ℝ)*(sp_s0_7) + (4825445536069/500000000000 : ℝ)*(sp_s0_8) + (2980529516771/500000000000 : ℝ)*(sp_s0_9) + (4199611/500000000000 : ℝ)*(sp_s0_14) + (13003631/250000000000 : ℝ)*(sp_s0_15) + (4060397395149/500000000000 : ℝ)*(sp_s0_17) + (105154959/1000000000000 : ℝ)*(sp_s0_20) + (2463940810249/1000000000000 : ℝ)*(f.failure) + (2980555524033/500000000000 : ℝ)*(f.sum) + (460168522722879/5000000000000000000000000000 : ℝ)*base63 + (252800259596933/5000000000000000000000000000 : ℝ)*base64 + (61237118400007/500000000000000000000000000 : ℝ)*base66 + (1492397823512369/5000000000000000000000000000 : ℝ)*base69 + (382599716603859/1250000000000000000000000000 : ℝ)*base71 + (158185793096933/5000000000000000000000000000 : ℝ)*base72 + (84424749871051/500000000000000000000000000 : ℝ)*base75 + (636031323512369/5000000000000000000000000000 : ℝ)*base77 + (2039860846097003/5000000000000000000000000000 : ℝ)*base78 + (14203/50000000000000000 : ℝ)*base87 + (14203/50000000000000000 : ℝ)*base89 + (14203/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-2111/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-2111/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15118905138572271/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (421379397359/250000000000 : ℝ)*(base3) + (11806144439/62500000000 : ℝ)*(base7) + (7024879/1000000000000 : ℝ)*(base13) + (200338651949/200000000000 : ℝ)*(base40) + (586155364509/500000000000 : ℝ)*(base49) + (554030497437/200000000000 : ℝ)*(major_s0_0) + (554030497437/200000000000 : ℝ)*(major_s0_1) + (554030497437/200000000000 : ℝ)*(major_s0_2) + (3583661/62500000000 : ℝ)*(sp_s0_2) + (850063/200000000000 : ℝ)*(sp_s0_8) + (92676077/500000000000 : ℝ)*(sp_s0_9) + (157456032017/40000000000 : ℝ)*(sp_s0_13) + (2810960582213/500000000000 : ℝ)*(sp_s0_14) + (1968082567287/500000000000 : ℝ)*(sp_s0_15) + (1496619278413/1000000000000 : ℝ)*(f.failure) + (492050978163/125000000000 : ℝ)*(f.sum) + (1042481/10000000000000000000 : ℝ)*base63 + (648770771704539/2000000000000000000000000000 : ℝ)*base65 + (201325861704539/2000000000000000000000000000 : ℝ)*base66 + (743632111542927/2000000000000000000000000000 : ℝ)*base68 + (21706547459597/500000000000000000000000000 : ℝ)*base70 + (936301949295461/2000000000000000000000000000 : ℝ)*base72 + (77400095857073/2000000000000000000000000000 : ℝ)*base74 + (424080430657073/2000000000000000000000000000 : ℝ)*base77 + (2628339081/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (37911/50000000000000000 : ℝ)*base87 + (37911/50000000000000000 : ℝ)*base89 + (37911/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58981/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58981/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7790157291313723855233/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4417971811273/1000000000000 : ℝ)*(base3) + (347024900887/250000000000 : ℝ)*(base7) + (234303977499/125000000000 : ℝ)*(base40) + (114217857589/250000000000 : ℝ)*(base49) + (701013958021/125000000000 : ℝ)*(major_s0_0) + (1360276299669/62500000000 : ℝ)*(major_s0_1) + (701013958021/125000000000 : ℝ)*(major_s0_2) + (14759581/250000000000 : ℝ)*(sp_s0_0) + (17792993/500000000000 : ℝ)*(sp_s0_1) + (88301451/250000000000 : ℝ)*(sp_s0_7) + (2019538641317/125000000000 : ℝ)*(sp_s0_17) + (3698816478437/500000000000 : ℝ)*(sp_s0_20) + (11815981426289/1000000000000 : ℝ)*(sp_s0_21) + (3699022600501/500000000000 : ℝ)*(sp_s0_22) + (1514936103863/500000000000 : ℝ)*(f.failure) + (3699022600501/500000000000 : ℝ)*(f.sum) + (94483042084407/1250000000000000000000000000 : ℝ)*base63 + (8383616751987/1250000000000000000000000000 : ℝ)*base65 + (66822930109443/625000000000000000000000000 : ℝ)*base66 + (319913260638809/1250000000000000000000000000 : ℝ)*base69 + (68555477566449/312500000000000000000000000 : ℝ)*base71 + (108439779501987/1250000000000000000000000000 : ℝ)*base73 + (69329287347799/625000000000000000000000000 : ℝ)*base75 + (102910726388809/1250000000000000000000000000 : ℝ)*base77 + (285584080216899/1250000000000000000000000000 : ℝ)*base78 + (9061/25000000000000000 : ℝ)*base87 + (9061/25000000000000000 : ℝ)*base89 + (9061/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (44487/100000 : ℝ) ^ (79/16 : ℝ) ≤ (114559483482006879/6250000000000000000 : ℝ) := by
    have hpowers : (44487/100000 : ℝ)^79 ≤ (114559483482006879/6250000000000000000 : ℝ)^16 := by
      have hnat : (44487 : ℕ)^79*6250000000000000000^16 ≤ 114559483482006879^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44487 100000 114559483482006879 6250000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44487/100000 : ℝ)) (X := (114559483482006879/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (6364559483482006879/6250000000000000000 : ℝ) ≤ (2007370939451151/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (6364559483482006879/6250000000000000000 : ℝ)^16 ≤ (2007370939451151/2000000000000000 : ℝ)^79 := by
      have hnat : (6364559483482006879 : ℕ)^16*2000000000000000^79 ≤ 2007370939451151^79*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6364559483482006879 6250000000000000000 2007370939451151 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2007370939451151/2000000000000000 : ℝ)) (X := (6364559483482006879/6250000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3239559483482006879/3125000000000000000 : ℝ) ≤ (5036592058778219/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3239559483482006879/3125000000000000000 : ℝ)^16 ≤ (5036592058778219/5000000000000000 : ℝ)^79 := by
      have hnat : (3239559483482006879 : ℕ)^16*5000000000000000^79 ≤ 5036592058778219^79*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3239559483482006879 3125000000000000000 5036592058778219 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036592058778219/5000000000000000 : ℝ)) (X := (3239559483482006879/3125000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7370939451151/889740000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(36329420300683/4448700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (44487/100000 : ℝ)) (alpha := (7370939451151/889740000000000 : ℝ)) (beta := (36329420300683/4448700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (44487/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7370939451151/889740000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(36329420300683/4448700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2111/100000 : ℝ) ^ (79/16 : ℝ) ≤ (266766110227/50000000000000000000 : ℝ) := by
    have hpowers : (2111/100000 : ℝ)^79 ≤ (266766110227/50000000000000000000 : ℝ)^16 := by
      have hnat : (2111 : ℕ)^79*50000000000000000000^16 ≤ 266766110227^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2111 100000 266766110227 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2111/100000 : ℝ)) (X := (266766110227/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50000000266766110227/50000000000000000000 : ℝ) ≤ (2500000002701429/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50000000266766110227/50000000000000000000 : ℝ)^16 ≤ (2500000002701429/2500000000000000 : ℝ)^79 := by
      have hnat : (50000000266766110227 : ℕ)^16*2500000000000000^79 ≤ 2500000002701429^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000266766110227 50000000000000000000 2500000002701429 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000002701429/2500000000000000 : ℝ)) (X := (50000000266766110227/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25000000266766110227/25000000000000000000 : ℝ) ≤ (1250000002701429/1250000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (25000000266766110227/25000000000000000000 : ℝ)^16 ≤ (1250000002701429/1250000000000000 : ℝ)^79 := by
      have hnat : (25000000266766110227 : ℕ)^16*1250000000000000^79 ≤ 1250000002701429^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000266766110227 25000000000000000000 1250000002701429 1250000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000002701429/1250000000000000 : ℝ)) (X := (25000000266766110227/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(2701429/52775000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(2701429/52775000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (2111/100000 : ℝ)) (alpha := (2701429/52775000000000 : ℝ)) (beta := (2701429/52775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (2111/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(2701429/52775000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(2701429/52775000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (58981/100000 : ℝ) ^ (79/16 : ℝ) ≤ (922149133804840393/12500000000000000000 : ℝ) := by
    have hpowers : (58981/100000 : ℝ)^79 ≤ (922149133804840393/12500000000000000000 : ℝ)^16 := by
      have hnat : (58981 : ℕ)^79*12500000000000000000^16 ≤ 922149133804840393^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58981 100000 922149133804840393 12500000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58981/100000 : ℝ)) (X := (922149133804840393/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13422149133804840393/12500000000000000000 : ℝ) ≤ (2536300319499541/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (13422149133804840393/12500000000000000000 : ℝ)^16 ≤ (2536300319499541/2500000000000000 : ℝ)^79 := by
      have hnat : (13422149133804840393 : ℕ)^16*2500000000000000^79 ≤ 2536300319499541^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13422149133804840393 12500000000000000000 2536300319499541 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2536300319499541/2500000000000000 : ℝ)) (X := (13422149133804840393/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (7172149133804840393/6250000000000000000 : ℝ) ≤ (5141326419626903/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (7172149133804840393/6250000000000000000 : ℝ)^16 ≤ (5141326419626903/5000000000000000 : ℝ)^79 := by
      have hnat : (7172149133804840393 : ℕ)^16*5000000000000000^79 ≤ 5141326419626903^79*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7172149133804840393 6250000000000000000 5141326419626903 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5141326419626903/5000000000000000 : ℝ)) (X := (7172149133804840393/6250000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(36300319499541/1474525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(68725780627821/2949050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (58981/100000 : ℝ)) (alpha := (36300319499541/1474525000000000 : ℝ)) (beta := (68725780627821/2949050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (58981/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(36300319499541/1474525000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(68725780627821/2949050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-170015071/500000000 : ℝ)*X 0 0+(-2249671727/5000000000 : ℝ)*X 0 1+(1124835549/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5189190723/10000000000 : ℝ)*X 1 0+(359253959/1000000000 : ℝ)*X 1 1+(718507717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((170015071/500000000 : ℝ)*X 2 0+(-2249671727/5000000000 : ℝ)*X 2 1+(-1124835549/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5189190723/10000000000 : ℝ)*X 0 0+(-359253959/1000000000 : ℝ)*X 0 1+(718507717/2000000000 : ℝ)*X 0 2+(5189190723/10000000000 : ℝ)*X 1 0+(-359253959/1000000000 : ℝ)*X 1 1+(718507717/2000000000 : ℝ)*X 1 2+(5189190723/10000000000 : ℝ)*X 2 0+(-359253959/1000000000 : ℝ)*X 2 1+(718507717/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319007_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-122538350650929029395157895535724529/15386186205325000000000000000000000 : ℝ) := by norm_num
    linear_combination (75484310833/100000000000 : ℝ)*(base3) + (688737/500000000000 : ℝ)*(base10) + (315927/250000000000 : ℝ)*(base13) + (553080352229/1000000000000 : ℝ)*(base40) + (1389450357293/1000000000000 : ℝ)*(base49) + (205259192307/250000000000 : ℝ)*(base50) + (574497/1000000000000 : ℝ)*(base54) + (52527878997/100000000000 : ℝ)*(base59) + (92547/50000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (1850939425503/1000000000000 : ℝ)*(major_s1_2) + (663680974947/250000000000 : ℝ)*(sp_s1_0) + (3409569649301/1000000000000 : ℝ)*(sp_s1_1) + (2654725966473/1000000000000 : ℝ)*(sp_s1_2) + (245156317173/1000000000000 : ℝ)*(sp_s1_6) + (265472654097/100000000000 : ℝ)*(f.sum) + (2197739343951787839/6225444550000000000000000000000 : ℝ)*base62 + (504040859639127/2949050000000000000000000000 : ℝ)*base64 + (1511730007517/21110000000000000000000000 : ℝ)*base67 + (101653068716883/368631250000000000000000000 : ℝ)*base68 + (12619278184062186691/14577154150000000000000000000000 : ℝ)*base70 + (1443748130953/4943000000000000000000000 : ℝ)*base73 + (2007313507029/21110000000000000000000000 : ℝ)*base74 + (6777115889571/12357500000000000000000000 : ℝ)*base76 + (25331607886057481/104346730000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p019_b002 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 6 ≤ c.val) (hhi : c.val < 8)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=6 ∨ c=7 := by omega
  rcases hc with rfl|rfl
  · exact collision_c319006 p hpa (by linarith only [hpb]) X hX
  · exact collision_c319007 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 6 ≤ c.val) (hhi : c.val < 8)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b002 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
