-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:48.802066+00:00
-- url     : https://prove2.me/submissions/eaadf85b-77fb-4913-ad32-e4add4c4bf7d

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
theorem collision_support_c320050_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2417567477/10000000000 : ℝ)*x 0 + (2417567609/10000000000 : ℝ)*x 1 + (-7133744101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2417567477/10000000000 : ℝ)^41 ≤ (8567707557433/50000000000000 : ℝ)^33 := by
    have hnat : (2417567477 : ℕ)^41*50000000000000^33 ≤ 8567707557433^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417567477 10000000000 8567707557433 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417567609/10000000000 : ℝ)^41 ≤ (17135416277277/100000000000000 : ℝ)^33 := by
    have hnat : (2417567609 : ℕ)^41*100000000000000^33 ≤ 17135416277277^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417567609 10000000000 17135416277277 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7133744101/10000000000 : ℝ)^41 ≤ (821614607353/1250000000000 : ℝ)^33 := by
    have hnat : (7133744101 : ℕ)^41*1250000000000^33 ≤ 821614607353^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7133744101 10000000000 821614607353 1250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2417567477/10000000000 : ℝ), (2417567609/10000000000 : ℝ), (-7133744101/10000000000 : ℝ)] ![(8567707557433/50000000000000 : ℝ), (17135416277277/100000000000000 : ℝ), (821614607353/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2417567477/10000000000 : ℝ)|^41 ≤ (8567707557433/50000000000000 : ℝ)^33
        have hw : |(-2417567477/10000000000 : ℝ)|=(2417567477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417567609/10000000000 : ℝ)|^41 ≤ (17135416277277/100000000000000 : ℝ)^33
        have hw : |(2417567609/10000000000 : ℝ)|=(2417567609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7133744101/10000000000 : ℝ)|^41 ≤ (821614607353/1250000000000 : ℝ)^33
        have hw : |(-7133744101/10000000000 : ℝ)|=(7133744101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3202609549/10000000000 : ℝ)*x 0 + (-1601304943/5000000000 : ℝ)*x 1 + (-365784593/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3202609549/10000000000 : ℝ)^41 ≤ (24301113544757/100000000000000 : ℝ)^33 := by
    have hnat : (3202609549 : ℕ)^41*100000000000000^33 ≤ 24301113544757^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3202609549 10000000000 24301113544757 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1601304943/5000000000 : ℝ)^41 ≤ (189852474389/781250000000 : ℝ)^33 := by
    have hnat : (1601304943 : ℕ)^41*781250000000^33 ≤ 189852474389^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601304943 5000000000 189852474389 781250000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365784593/625000000 : ℝ)^41 ≤ (51397769725523/100000000000000 : ℝ)^33 := by
    have hnat : (365784593 : ℕ)^41*100000000000000^33 ≤ 51397769725523^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365784593 625000000 51397769725523 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3202609549/10000000000 : ℝ), (-1601304943/5000000000 : ℝ), (-365784593/625000000 : ℝ)] ![(24301113544757/100000000000000 : ℝ), (189852474389/781250000000 : ℝ), (51397769725523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3202609549/10000000000 : ℝ)|^41 ≤ (24301113544757/100000000000000 : ℝ)^33
        have hw : |(3202609549/10000000000 : ℝ)|=(3202609549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1601304943/5000000000 : ℝ)|^41 ≤ (189852474389/781250000000 : ℝ)^33
        have hw : |(-1601304943/5000000000 : ℝ)|=(1601304943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365784593/625000000 : ℝ)|^41 ≤ (51397769725523/100000000000000 : ℝ)^33
        have hw : |(-365784593/625000000 : ℝ)|=(365784593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-676543571/5000000000 : ℝ)*x 0 + (214253177/5000000000 : ℝ)*x 1 + (-9159941317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676543571/5000000000 : ℝ)^41 ≤ (8331785378287/100000000000000 : ℝ)^33 := by
    have hnat : (676543571 : ℕ)^41*100000000000000^33 ≤ 8331785378287^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676543571 5000000000 8331785378287 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214253177/5000000000 : ℝ)^41 ≤ (1996689539813/100000000000000 : ℝ)^33 := by
    have hnat : (214253177 : ℕ)^41*100000000000000^33 ≤ 1996689539813^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214253177 5000000000 1996689539813 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9159941317/10000000000 : ℝ)^41 ≤ (22417881265303/25000000000000 : ℝ)^33 := by
    have hnat : (9159941317 : ℕ)^41*25000000000000^33 ≤ 22417881265303^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9159941317 10000000000 22417881265303 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-676543571/5000000000 : ℝ), (214253177/5000000000 : ℝ), (-9159941317/10000000000 : ℝ)] ![(8331785378287/100000000000000 : ℝ), (1996689539813/100000000000000 : ℝ), (22417881265303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-676543571/5000000000 : ℝ)|^41 ≤ (8331785378287/100000000000000 : ℝ)^33
        have hw : |(-676543571/5000000000 : ℝ)|=(676543571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214253177/5000000000 : ℝ)|^41 ≤ (1996689539813/100000000000000 : ℝ)^33
        have hw : |(214253177/5000000000 : ℝ)|=(214253177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9159941317/10000000000 : ℝ)|^41 ≤ (22417881265303/25000000000000 : ℝ)^33
        have hw : |(-9159941317/10000000000 : ℝ)|=(9159941317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1692946191/5000000000 : ℝ)*x 0 + (-203033503/1000000000 : ℝ)*x 1 + (-6643501997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1692946191/5000000000 : ℝ)^41 ≤ (6510202967571/25000000000000 : ℝ)^33 := by
    have hnat : (1692946191 : ℕ)^41*25000000000000^33 ≤ 6510202967571^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692946191 5000000000 6510202967571 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203033503/1000000000 : ℝ)^41 ≤ (13794479998671/100000000000000 : ℝ)^33 := by
    have hnat : (203033503 : ℕ)^41*100000000000000^33 ≤ 13794479998671^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203033503 1000000000 13794479998671 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6643501997/10000000000 : ℝ)^41 ≤ (15041177029089/25000000000000 : ℝ)^33 := by
    have hnat : (6643501997 : ℕ)^41*25000000000000^33 ≤ 15041177029089^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6643501997 10000000000 15041177029089 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1692946191/5000000000 : ℝ), (-203033503/1000000000 : ℝ), (-6643501997/10000000000 : ℝ)] ![(6510202967571/25000000000000 : ℝ), (13794479998671/100000000000000 : ℝ), (15041177029089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1692946191/5000000000 : ℝ)|^41 ≤ (6510202967571/25000000000000 : ℝ)^33
        have hw : |(1692946191/5000000000 : ℝ)|=(1692946191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203033503/1000000000 : ℝ)|^41 ≤ (13794479998671/100000000000000 : ℝ)^33
        have hw : |(-203033503/1000000000 : ℝ)|=(203033503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6643501997/10000000000 : ℝ)|^41 ≤ (15041177029089/25000000000000 : ℝ)^33
        have hw : |(-6643501997/10000000000 : ℝ)|=(6643501997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4431519489/10000000000 : ℝ)*x 0 + (137490267/200000000 : ℝ)*x 1 + (214411341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4431519489/10000000000 : ℝ)^41 ≤ (36380483017949/100000000000000 : ℝ)^33 := by
    have hnat : (4431519489 : ℕ)^41*100000000000000^33 ≤ 36380483017949^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431519489 10000000000 36380483017949 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137490267/200000000 : ℝ)^41 ≤ (31387409202477/50000000000000 : ℝ)^33 := by
    have hnat : (137490267 : ℕ)^41*50000000000000^33 ≤ 31387409202477^33*200000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137490267 200000000 31387409202477 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214411341/10000000000 : ℝ)^41 ≤ (422349279973/50000000000000 : ℝ)^33 := by
    have hnat : (214411341 : ℕ)^41*50000000000000^33 ≤ 422349279973^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214411341 10000000000 422349279973 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4431519489/10000000000 : ℝ), (137490267/200000000 : ℝ), (214411341/10000000000 : ℝ)] ![(36380483017949/100000000000000 : ℝ), (31387409202477/50000000000000 : ℝ), (422349279973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4431519489/10000000000 : ℝ)|^41 ≤ (36380483017949/100000000000000 : ℝ)^33
        have hw : |(4431519489/10000000000 : ℝ)|=(4431519489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137490267/200000000 : ℝ)|^41 ≤ (31387409202477/50000000000000 : ℝ)^33
        have hw : |(137490267/200000000 : ℝ)|=(137490267/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(214411341/10000000000 : ℝ)|^41 ≤ (422349279973/50000000000000 : ℝ)^33
        have hw : |(214411341/10000000000 : ℝ)|=(214411341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (71103189/500000000 : ℝ)*x 0 + (9209370759/10000000000 : ℝ)*x 1 + (-43676631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71103189/500000000 : ℝ)^41 ≤ (886270152589/10000000000000 : ℝ)^33 := by
    have hnat : (71103189 : ℕ)^41*10000000000000^33 ≤ 886270152589^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71103189 500000000 886270152589 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9209370759/10000000000 : ℝ)^41 ≤ (902731157131/1000000000000 : ℝ)^33 := by
    have hnat : (9209370759 : ℕ)^41*1000000000000^33 ≤ 902731157131^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9209370759 10000000000 902731157131 1000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43676631/2000000000 : ℝ)^41 ≤ (432091375113/50000000000000 : ℝ)^33 := by
    have hnat : (43676631 : ℕ)^41*50000000000000^33 ≤ 432091375113^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43676631 2000000000 432091375113 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71103189/500000000 : ℝ), (9209370759/10000000000 : ℝ), (-43676631/2000000000 : ℝ)] ![(886270152589/10000000000000 : ℝ), (902731157131/1000000000000 : ℝ), (432091375113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71103189/500000000 : ℝ)|^41 ≤ (886270152589/10000000000000 : ℝ)^33
        have hw : |(71103189/500000000 : ℝ)|=(71103189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9209370759/10000000000 : ℝ)|^41 ≤ (902731157131/1000000000000 : ℝ)^33
        have hw : |(9209370759/10000000000 : ℝ)|=(9209370759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43676631/2000000000 : ℝ)|^41 ≤ (432091375113/50000000000000 : ℝ)^33
        have hw : |(-43676631/2000000000 : ℝ)|=(43676631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-412645549/5000000000 : ℝ)*x 0 + (1255793269/10000000000 : ℝ)*x 1 + (-4506925757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412645549/5000000000 : ℝ)^41 ≤ (4507819026459/100000000000000 : ℝ)^33 := by
    have hnat : (412645549 : ℕ)^41*100000000000000^33 ≤ 4507819026459^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412645549 5000000000 4507819026459 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255793269/10000000000 : ℝ)^41 ≤ (7594060737293/100000000000000 : ℝ)^33 := by
    have hnat : (1255793269 : ℕ)^41*100000000000000^33 ≤ 7594060737293^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255793269 10000000000 7594060737293 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506925757/5000000000 : ℝ)^41 ≤ (43949060111153/50000000000000 : ℝ)^33 := by
    have hnat : (4506925757 : ℕ)^41*50000000000000^33 ≤ 43949060111153^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506925757 5000000000 43949060111153 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412645549/5000000000 : ℝ), (1255793269/10000000000 : ℝ), (-4506925757/5000000000 : ℝ)] ![(4507819026459/100000000000000 : ℝ), (7594060737293/100000000000000 : ℝ), (43949060111153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412645549/5000000000 : ℝ)|^41 ≤ (4507819026459/100000000000000 : ℝ)^33
        have hw : |(-412645549/5000000000 : ℝ)|=(412645549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255793269/10000000000 : ℝ)|^41 ≤ (7594060737293/100000000000000 : ℝ)^33
        have hw : |(1255793269/10000000000 : ℝ)|=(1255793269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4506925757/5000000000 : ℝ)|^41 ≤ (43949060111153/50000000000000 : ℝ)^33
        have hw : |(-4506925757/5000000000 : ℝ)|=(4506925757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (113804107/625000000 : ℝ)*x 0 + (-697524533/2500000000 : ℝ)*x 1 + (-7285945609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113804107/625000000 : ℝ)^41 ≤ (12049009661443/100000000000000 : ℝ)^33 := by
    have hnat : (113804107 : ℕ)^41*100000000000000^33 ≤ 12049009661443^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113804107 625000000 12049009661443 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697524533/2500000000 : ℝ)^41 ≤ (10237506834439/50000000000000 : ℝ)^33 := by
    have hnat : (697524533 : ℕ)^41*50000000000000^33 ≤ 10237506834439^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697524533 2500000000 10237506834439 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7285945609/10000000000 : ℝ)^41 ≤ (8434497082387/12500000000000 : ℝ)^33 := by
    have hnat : (7285945609 : ℕ)^41*12500000000000^33 ≤ 8434497082387^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7285945609 10000000000 8434497082387 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(113804107/625000000 : ℝ), (-697524533/2500000000 : ℝ), (-7285945609/10000000000 : ℝ)] ![(12049009661443/100000000000000 : ℝ), (10237506834439/50000000000000 : ℝ), (8434497082387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(113804107/625000000 : ℝ)|^41 ≤ (12049009661443/100000000000000 : ℝ)^33
        have hw : |(113804107/625000000 : ℝ)|=(113804107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-697524533/2500000000 : ℝ)|^41 ≤ (10237506834439/50000000000000 : ℝ)^33
        have hw : |(-697524533/2500000000 : ℝ)|=(697524533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7285945609/10000000000 : ℝ)|^41 ≤ (8434497082387/12500000000000 : ℝ)^33
        have hw : |(-7285945609/10000000000 : ℝ)|=(7285945609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7654084209/10000000000 : ℝ)*x 0 + (44833847/125000000 : ℝ)*x 1 + (90491703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7654084209/10000000000 : ℝ)^41 ≤ (35868742061623/50000000000000 : ℝ)^33 := by
    have hnat : (7654084209 : ℕ)^41*50000000000000^33 ≤ 35868742061623^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7654084209 10000000000 35868742061623 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44833847/125000000 : ℝ)^41 ≤ (27973287295369/100000000000000 : ℝ)^33 := by
    have hnat : (44833847 : ℕ)^41*100000000000000^33 ≤ 27973287295369^33*125000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44833847 125000000 27973287295369 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90491703/10000000000 : ℝ)^41 ≤ (72307142187/25000000000000 : ℝ)^33 := by
    have hnat : (90491703 : ℕ)^41*25000000000000^33 ≤ 72307142187^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90491703 10000000000 72307142187 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7654084209/10000000000 : ℝ), (44833847/125000000 : ℝ), (90491703/10000000000 : ℝ)] ![(35868742061623/50000000000000 : ℝ), (27973287295369/100000000000000 : ℝ), (72307142187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7654084209/10000000000 : ℝ)|^41 ≤ (35868742061623/50000000000000 : ℝ)^33
        have hw : |(7654084209/10000000000 : ℝ)|=(7654084209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44833847/125000000 : ℝ)|^41 ≤ (27973287295369/100000000000000 : ℝ)^33
        have hw : |(44833847/125000000 : ℝ)|=(44833847/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90491703/10000000000 : ℝ)|^41 ≤ (72307142187/25000000000000 : ℝ)^33
        have hw : |(90491703/10000000000 : ℝ)|=(90491703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (470022643/625000000 : ℝ)*x 0 + (915780771/2500000000 : ℝ)*x 1 + (-132663073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470022643/625000000 : ℝ)^41 ≤ (17545916063789/25000000000000 : ℝ)^33 := by
    have hnat : (470022643 : ℕ)^41*25000000000000^33 ≤ 17545916063789^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470022643 625000000 17545916063789 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915780771/2500000000 : ℝ)^41 ≤ (5743128589911/20000000000000 : ℝ)^33 := by
    have hnat : (915780771 : ℕ)^41*20000000000000^33 ≤ 5743128589911^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915780771 2500000000 5743128589911 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132663073/5000000000 : ℝ)^41 ≤ (1100692788627/100000000000000 : ℝ)^33 := by
    have hnat : (132663073 : ℕ)^41*100000000000000^33 ≤ 1100692788627^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132663073 5000000000 1100692788627 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(470022643/625000000 : ℝ), (915780771/2500000000 : ℝ), (-132663073/5000000000 : ℝ)] ![(17545916063789/25000000000000 : ℝ), (5743128589911/20000000000000 : ℝ), (1100692788627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(470022643/625000000 : ℝ)|^41 ≤ (17545916063789/25000000000000 : ℝ)^33
        have hw : |(470022643/625000000 : ℝ)|=(470022643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915780771/2500000000 : ℝ)|^41 ≤ (5743128589911/20000000000000 : ℝ)^33
        have hw : |(915780771/2500000000 : ℝ)|=(915780771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132663073/5000000000 : ℝ)|^41 ≤ (1100692788627/100000000000000 : ℝ)^33
        have hw : |(-132663073/5000000000 : ℝ)|=(132663073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4590732719/10000000000 : ℝ)*x 0 + (2179021897/10000000000 : ℝ)*x 1 + (-1359825953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4590732719/10000000000 : ℝ)^41 ≤ (38011412656349/100000000000000 : ℝ)^33 := by
    have hnat : (4590732719 : ℕ)^41*100000000000000^33 ≤ 38011412656349^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590732719 10000000000 38011412656349 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179021897/10000000000 : ℝ)^41 ≤ (7530263393119/50000000000000 : ℝ)^33 := by
    have hnat : (2179021897 : ℕ)^41*50000000000000^33 ≤ 7530263393119^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179021897 10000000000 7530263393119 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359825953/2500000000 : ℝ)^41 ≤ (46928060545343/100000000000000 : ℝ)^33 := by
    have hnat : (1359825953 : ℕ)^41*100000000000000^33 ≤ 46928060545343^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359825953 2500000000 46928060545343 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4590732719/10000000000 : ℝ), (2179021897/10000000000 : ℝ), (-1359825953/2500000000 : ℝ)] ![(38011412656349/100000000000000 : ℝ), (7530263393119/50000000000000 : ℝ), (46928060545343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4590732719/10000000000 : ℝ)|^41 ≤ (38011412656349/100000000000000 : ℝ)^33
        have hw : |(-4590732719/10000000000 : ℝ)|=(4590732719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2179021897/10000000000 : ℝ)|^41 ≤ (7530263393119/50000000000000 : ℝ)^33
        have hw : |(2179021897/10000000000 : ℝ)|=(2179021897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1359825953/2500000000 : ℝ)|^41 ≤ (46928060545343/100000000000000 : ℝ)^33
        have hw : |(-1359825953/2500000000 : ℝ)|=(1359825953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2194885733/10000000000 : ℝ)*x 0 + (-2459121191/10000000000 : ℝ)*x 1 + (-7270736891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194885733/10000000000 : ℝ)^41 ≤ (7598435870381/50000000000000 : ℝ)^33 := by
    have hnat : (2194885733 : ℕ)^41*50000000000000^33 ≤ 7598435870381^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194885733 10000000000 7598435870381 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2459121191/10000000000 : ℝ)^41 ≤ (17502102336783/100000000000000 : ℝ)^33 := by
    have hnat : (2459121191 : ℕ)^41*100000000000000^33 ≤ 17502102336783^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459121191 10000000000 17502102336783 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7270736891/10000000000 : ℝ)^41 ≤ (6730102590367/10000000000000 : ℝ)^33 := by
    have hnat : (7270736891 : ℕ)^41*10000000000000^33 ≤ 6730102590367^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7270736891 10000000000 6730102590367 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2194885733/10000000000 : ℝ), (-2459121191/10000000000 : ℝ), (-7270736891/10000000000 : ℝ)] ![(7598435870381/50000000000000 : ℝ), (17502102336783/100000000000000 : ℝ), (6730102590367/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2194885733/10000000000 : ℝ)|^41 ≤ (7598435870381/50000000000000 : ℝ)^33
        have hw : |(2194885733/10000000000 : ℝ)|=(2194885733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2459121191/10000000000 : ℝ)|^41 ≤ (17502102336783/100000000000000 : ℝ)^33
        have hw : |(-2459121191/10000000000 : ℝ)|=(2459121191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7270736891/10000000000 : ℝ)|^41 ≤ (6730102590367/10000000000000 : ℝ)^33
        have hw : |(-7270736891/10000000000 : ℝ)|=(7270736891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4119082149/5000000000 : ℝ)*x 0 + (1342932597/5000000000 : ℝ)*x 1 + (406555611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119082149/5000000000 : ℝ)^41 ≤ (307033486429/390625000000 : ℝ)^33 := by
    have hnat : (4119082149 : ℕ)^41*390625000000^33 ≤ 307033486429^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119082149 5000000000 307033486429 390625000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342932597/5000000000 : ℝ)^41 ≤ (19529017008987/100000000000000 : ℝ)^33 := by
    have hnat : (1342932597 : ℕ)^41*100000000000000^33 ≤ 19529017008987^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342932597 5000000000 19529017008987 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406555611/10000000000 : ℝ)^41 ≤ (1870410445121/100000000000000 : ℝ)^33 := by
    have hnat : (406555611 : ℕ)^41*100000000000000^33 ≤ 1870410445121^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406555611 10000000000 1870410445121 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119082149/5000000000 : ℝ), (1342932597/5000000000 : ℝ), (406555611/10000000000 : ℝ)] ![(307033486429/390625000000 : ℝ), (19529017008987/100000000000000 : ℝ), (1870410445121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119082149/5000000000 : ℝ)|^41 ≤ (307033486429/390625000000 : ℝ)^33
        have hw : |(4119082149/5000000000 : ℝ)|=(4119082149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1342932597/5000000000 : ℝ)|^41 ≤ (19529017008987/100000000000000 : ℝ)^33
        have hw : |(1342932597/5000000000 : ℝ)|=(1342932597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(406555611/10000000000 : ℝ)|^41 ≤ (1870410445121/100000000000000 : ℝ)^33
        have hw : |(406555611/10000000000 : ℝ)|=(406555611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s0_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (136467631/10000000000 : ℝ)*x 0 + (12364197/12500000 : ℝ)*x 1 + (-109392911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136467631/10000000000 : ℝ)^41 ≤ (481854177907/100000000000000 : ℝ)^33 := by
    have hnat : (136467631 : ℕ)^41*100000000000000^33 ≤ 481854177907^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136467631 10000000000 481854177907 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12364197/12500000 : ℝ)^41 ≤ (98651982905601/100000000000000 : ℝ)^33 := by
    have hnat : (12364197 : ℕ)^41*100000000000000^33 ≤ 98651982905601^33*12500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12364197 12500000 98651982905601 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109392911/5000000000 : ℝ)^41 ≤ (433081453147/50000000000000 : ℝ)^33 := by
    have hnat : (109392911 : ℕ)^41*50000000000000^33 ≤ 433081453147^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109392911 5000000000 433081453147 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136467631/10000000000 : ℝ), (12364197/12500000 : ℝ), (-109392911/5000000000 : ℝ)] ![(481854177907/100000000000000 : ℝ), (98651982905601/100000000000000 : ℝ), (433081453147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136467631/10000000000 : ℝ)|^41 ≤ (481854177907/100000000000000 : ℝ)^33
        have hw : |(136467631/10000000000 : ℝ)|=(136467631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12364197/12500000 : ℝ)|^41 ≤ (98651982905601/100000000000000 : ℝ)^33
        have hw : |(12364197/12500000 : ℝ)|=(12364197/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109392911/5000000000 : ℝ)|^41 ≤ (433081453147/50000000000000 : ℝ)^33
        have hw : |(-109392911/5000000000 : ℝ)|=(109392911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-188931067/625000000 : ℝ)*x 0 + (2983464369/10000000000 : ℝ)*x 1 + (-6192150059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188931067/625000000 : ℝ)^41 ≤ (2827322827197/12500000000000 : ℝ)^33 := by
    have hnat : (188931067 : ℕ)^41*12500000000000^33 ≤ 2827322827197^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188931067 625000000 2827322827197 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2983464369/10000000000 : ℝ)^41 ≤ (11126292198221/50000000000000 : ℝ)^33 := by
    have hnat : (2983464369 : ℕ)^41*50000000000000^33 ≤ 11126292198221^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983464369 10000000000 11126292198221 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6192150059/10000000000 : ℝ)^41 ≤ (6891104122649/12500000000000 : ℝ)^33 := by
    have hnat : (6192150059 : ℕ)^41*12500000000000^33 ≤ 6891104122649^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6192150059 10000000000 6891104122649 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-188931067/625000000 : ℝ), (2983464369/10000000000 : ℝ), (-6192150059/10000000000 : ℝ)] ![(2827322827197/12500000000000 : ℝ), (11126292198221/50000000000000 : ℝ), (6891104122649/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-188931067/625000000 : ℝ)|^41 ≤ (2827322827197/12500000000000 : ℝ)^33
        have hw : |(-188931067/625000000 : ℝ)|=(188931067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2983464369/10000000000 : ℝ)|^41 ≤ (11126292198221/50000000000000 : ℝ)^33
        have hw : |(2983464369/10000000000 : ℝ)|=(2983464369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6192150059/10000000000 : ℝ)|^41 ≤ (6891104122649/12500000000000 : ℝ)^33
        have hw : |(-6192150059/10000000000 : ℝ)|=(6192150059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1762983099/5000000000 : ℝ)*x 0 + (-868596179/2500000000 : ℝ)*x 1 + (-2663393487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1762983099/5000000000 : ℝ)^41 ≤ (219087388549/800000000000 : ℝ)^33 := by
    have hnat : (1762983099 : ℕ)^41*800000000000^33 ≤ 219087388549^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762983099 5000000000 219087388549 800000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868596179/2500000000 : ℝ)^41 ≤ (3361132188889/12500000000000 : ℝ)^33 := by
    have hnat : (868596179 : ℕ)^41*12500000000000^33 ≤ 3361132188889^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868596179 2500000000 3361132188889 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663393487/5000000000 : ℝ)^41 ≤ (45725018902271/100000000000000 : ℝ)^33 := by
    have hnat : (2663393487 : ℕ)^41*100000000000000^33 ≤ 45725018902271^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663393487 5000000000 45725018902271 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1762983099/5000000000 : ℝ), (-868596179/2500000000 : ℝ), (-2663393487/5000000000 : ℝ)] ![(219087388549/800000000000 : ℝ), (3361132188889/12500000000000 : ℝ), (45725018902271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1762983099/5000000000 : ℝ)|^41 ≤ (219087388549/800000000000 : ℝ)^33
        have hw : |(1762983099/5000000000 : ℝ)|=(1762983099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-868596179/2500000000 : ℝ)|^41 ≤ (3361132188889/12500000000000 : ℝ)^33
        have hw : |(-868596179/2500000000 : ℝ)|=(868596179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2663393487/5000000000 : ℝ)|^41 ≤ (45725018902271/100000000000000 : ℝ)^33
        have hw : |(-2663393487/5000000000 : ℝ)|=(2663393487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (230289899/400000000 : ℝ)*x 0 + (4984081843/10000000000 : ℝ)*x 1 + (49949021/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230289899/400000000 : ℝ)^41 ≤ (6294992098129/12500000000000 : ℝ)^33 := by
    have hnat : (230289899 : ℕ)^41*12500000000000^33 ≤ 6294992098129^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230289899 400000000 6294992098129 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4984081843/10000000000 : ℝ)^41 ≤ (42099067666983/100000000000000 : ℝ)^33 := by
    have hnat : (4984081843 : ℕ)^41*100000000000000^33 ≤ 42099067666983^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984081843 10000000000 42099067666983 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49949021/400000000 : ℝ)^41 ≤ (942624441547/12500000000000 : ℝ)^33 := by
    have hnat : (49949021 : ℕ)^41*12500000000000^33 ≤ 942624441547^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49949021 400000000 942624441547 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(230289899/400000000 : ℝ), (4984081843/10000000000 : ℝ), (49949021/400000000 : ℝ)] ![(6294992098129/12500000000000 : ℝ), (42099067666983/100000000000000 : ℝ), (942624441547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(230289899/400000000 : ℝ)|^41 ≤ (6294992098129/12500000000000 : ℝ)^33
        have hw : |(230289899/400000000 : ℝ)|=(230289899/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4984081843/10000000000 : ℝ)|^41 ≤ (42099067666983/100000000000000 : ℝ)^33
        have hw : |(4984081843/10000000000 : ℝ)|=(4984081843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49949021/400000000 : ℝ)|^41 ≤ (942624441547/12500000000000 : ℝ)^33
        have hw : |(49949021/400000000 : ℝ)|=(49949021/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320050_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3693821223/10000000000 : ℝ)*x 0 + (121418073/200000000 : ℝ)*x 1 + (-606059703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3693821223/10000000000 : ℝ)^41 ≤ (5802986147963/20000000000000 : ℝ)^33 := by
    have hnat : (3693821223 : ℕ)^41*20000000000000^33 ≤ 5802986147963^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693821223 10000000000 5802986147963 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121418073/200000000 : ℝ)^41 ≤ (2689544286857/5000000000000 : ℝ)^33 := by
    have hnat : (121418073 : ℕ)^41*5000000000000^33 ≤ 2689544286857^33*200000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121418073 200000000 2689544286857 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606059703/2500000000 : ℝ)^41 ≤ (17194183510163/100000000000000 : ℝ)^33 := by
    have hnat : (606059703 : ℕ)^41*100000000000000^33 ≤ 17194183510163^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606059703 2500000000 17194183510163 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3693821223/10000000000 : ℝ), (121418073/200000000 : ℝ), (-606059703/2500000000 : ℝ)] ![(5802986147963/20000000000000 : ℝ), (2689544286857/5000000000000 : ℝ), (17194183510163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3693821223/10000000000 : ℝ)|^41 ≤ (5802986147963/20000000000000 : ℝ)^33
        have hw : |(3693821223/10000000000 : ℝ)|=(3693821223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121418073/200000000 : ℝ)|^41 ≤ (2689544286857/5000000000000 : ℝ)^33
        have hw : |(121418073/200000000 : ℝ)|=(121418073/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-606059703/2500000000 : ℝ)|^41 ≤ (17194183510163/100000000000000 : ℝ)^33
        have hw : |(-606059703/2500000000 : ℝ)|=(606059703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320050 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (1059/625 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2417567477/10000000000 : ℝ)*X 0 0+(2417567609/10000000000 : ℝ)*X 0 1+(-7133744101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3202609549/10000000000 : ℝ)*X 1 0+(-1601304943/5000000000 : ℝ)*X 1 1+(-365784593/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-676543571/5000000000 : ℝ)*X 0 0+(214253177/5000000000 : ℝ)*X 0 1+(-9159941317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1692946191/5000000000 : ℝ)*X 1 0+(-203033503/1000000000 : ℝ)*X 1 1+(-6643501997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4431519489/10000000000 : ℝ)*X 2 0+(137490267/200000000 : ℝ)*X 2 1+(214411341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((71103189/500000000 : ℝ)*X 0 0+(9209370759/10000000000 : ℝ)*X 0 1+(-43676631/2000000000 : ℝ)*X 0 2+(71103189/500000000 : ℝ)*X 1 0+(9209370759/10000000000 : ℝ)*X 1 1+(-43676631/2000000000 : ℝ)*X 1 2+(71103189/500000000 : ℝ)*X 2 0+(9209370759/10000000000 : ℝ)*X 2 1+(-43676631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-412645549/5000000000 : ℝ)*X 0 0+(1255793269/10000000000 : ℝ)*X 0 1+(-4506925757/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((113804107/625000000 : ℝ)*X 1 0+(-697524533/2500000000 : ℝ)*X 1 1+(-7285945609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7654084209/10000000000 : ℝ)*X 2 0+(44833847/125000000 : ℝ)*X 2 1+(90491703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((470022643/625000000 : ℝ)*X 0 0+(915780771/2500000000 : ℝ)*X 0 1+(-132663073/5000000000 : ℝ)*X 0 2+(470022643/625000000 : ℝ)*X 1 0+(915780771/2500000000 : ℝ)*X 1 1+(-132663073/5000000000 : ℝ)*X 1 2+(470022643/625000000 : ℝ)*X 2 0+(915780771/2500000000 : ℝ)*X 2 1+(-132663073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4590732719/10000000000 : ℝ)*X 0 0+(2179021897/10000000000 : ℝ)*X 0 1+(-1359825953/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2194885733/10000000000 : ℝ)*X 1 0+(-2459121191/10000000000 : ℝ)*X 1 1+(-7270736891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4119082149/5000000000 : ℝ)*X 2 0+(1342932597/5000000000 : ℝ)*X 2 1+(406555611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((136467631/10000000000 : ℝ)*X 0 0+(12364197/12500000 : ℝ)*X 0 1+(-109392911/5000000000 : ℝ)*X 0 2+(136467631/10000000000 : ℝ)*X 1 0+(12364197/12500000 : ℝ)*X 1 1+(-109392911/5000000000 : ℝ)*X 1 2+(136467631/10000000000 : ℝ)*X 2 0+(12364197/12500000 : ℝ)*X 2 1+(-109392911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((36713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84948090487139393805681/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (441325302761/500000000000 : ℝ)*(base7) + (811031/500000000000 : ℝ)*(base44) + (165481/1000000000000 : ℝ)*(base50) + (138376852619/250000000000 : ℝ)*(base53) + (1713553/1000000000000 : ℝ)*(base60) + (302264085379/200000000000 : ℝ)*(major_s0_0) + (1511318804833/1000000000000 : ℝ)*(major_s0_1) + (957813016419/1000000000000 : ℝ)*(major_s0_2) + (1165430195541/1000000000000 : ℝ)*(sp_s0_7) + (1165512177389/1000000000000 : ℝ)*(sp_s0_8) + (1719021209927/1000000000000 : ℝ)*(sp_s0_9) + (843855200591/500000000000 : ℝ)*(sp_s0_13) + (8360391/100000000000 : ℝ)*(sp_s0_14) + (7875233/250000000000 : ℝ)*(sp_s0_27) + (805092918653/1000000000000 : ℝ)*(f.failure) + (1719021209927/1000000000000 : ℝ)*(f.sum) + (2492901764656657/5000000000000000000000000000 : ℝ)*base63 + (5432229034391163/10000000000000000000000000000 : ℝ)*base64 + (5251073367350441/10000000000000000000000000000 : ℝ)*base67 + (61820023806931/10000000000000000000000000000 : ℝ)*base69 + (1858552573700509/5000000000000000000000000000 : ℝ)*base70 + (263835084597083/2000000000000000000000000000 : ℝ)*base72 + (3905918550506383/10000000000000000000000000000 : ℝ)*base75 + (1619141575001971/2000000000000000000000000000 : ℝ)*base76 + (2267203726682513/5000000000000000000000000000 : ℝ)*base79 + (1029/2500000000000000 : ℝ)*base87 + (1029/2500000000000000 : ℝ)*base89 + (1029/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33981/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33981/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (73521285442261827/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (1627186926917/1000000000000 : ℝ)*(base5) + (423699031409/500000000000 : ℝ)*(base7) + (29468198651/1000000000000 : ℝ)*(base39) + (25492654927/25000000000 : ℝ)*(base60) + (471541677127/250000000000 : ℝ)*(major_s0_0) + (471541677127/250000000000 : ℝ)*(major_s0_1) + (471541677127/250000000000 : ℝ)*(major_s0_2) + (2685841/500000000000 : ℝ)*(sp_s0_0) + (4898563/1000000000000 : ℝ)*(sp_s0_1) + (572234019521/250000000000 : ℝ)*(sp_s0_14) + (18310318349/8000000000 : ℝ)*(sp_s0_15) + (979032094171/250000000000 : ℝ)*(sp_s0_16) + (224987775847/1000000000000 : ℝ)*(sp_s0_20) + (73378789/500000000000 : ℝ)*(sp_s0_22) + (1004776639947/1000000000000 : ℝ)*(f.failure) + (1144470724883/500000000000 : ℝ)*(f.sum) + (331797539/1000000000000000000000 : ℝ)*base62 + (537367563143521/2500000000000000000000000000 : ℝ)*base65 + (1151381153643521/2500000000000000000000000000 : ℝ)*base66 + (3710839111577/2500000000000000000000000000 : ℝ)*base68 + (138642554747451/1250000000000000000000000000 : ℝ)*base70 + (1070231659106479/2500000000000000000000000000 : ℝ)*base72 + (366538558138423/2500000000000000000000000000 : ℝ)*base74 + (362216667861577/2500000000000000000000000000 : ℝ)*base77 + (16425719/1000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1271/2500000000000000 : ℝ)*base87 + (1271/2500000000000000 : ℝ)*base89 + (1271/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7427/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7427/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9401757838115629207791/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (517600082089/1000000000000 : ℝ)*(base7) + (44250638003/200000000000 : ℝ)*(base33) + (365991/200000000000 : ℝ)*(base39) + (707943540877/1000000000000 : ℝ)*(base44) + (23465491209/1000000000000 : ℝ)*(base50) + (443029/1000000000000 : ℝ)*(base60) + (63992098439/40000000000 : ℝ)*(major_s0_0) + (556556055057/500000000000 : ℝ)*(major_s0_1) + (182105565099/100000000000 : ℝ)*(major_s0_2) + (15440839/200000000000 : ℝ)*(sp_s0_8) + (297459603571/125000000000 : ℝ)*(sp_s0_21) + (725201446741/500000000000 : ℝ)*(sp_s0_22) + (2158423638553/1000000000000 : ℝ)*(sp_s0_23) + (779747981117/1000000000000 : ℝ)*(sp_s0_27) + (194018287981/200000000000 : ℝ)*(f.failure) + (297459603571/125000000000 : ℝ)*(f.sum) + (706755202108131/2500000000000000000000000000 : ℝ)*base63 + (704386342692477/1000000000000000000000000000 : ℝ)*base65 + (2287649209200089/5000000000000000000000000000 : ℝ)*base67 + (401789412679749/1000000000000000000000000000 : ℝ)*base68 + (602772583895399/2000000000000000000000000000 : ℝ)*base71 + (81303805831297/400000000000000000000000000 : ℝ)*base73 + (2826629563115007/5000000000000000000000000000 : ℝ)*base75 + (371030184102089/400000000000000000000000000 : ℝ)*base77 + (1953476414182603/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (167/500000000000000 : ℝ)*base86 + (667/500000000000000 : ℝ)*base88 + (167/500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (36713/50000 : ℝ) ^ (5 : ℝ) ≤ (21342699506403643077/100000000000000000000 : ℝ) := by
    have hpowers : (36713/50000 : ℝ)^5 ≤ (21342699506403643077/100000000000000000000 : ℝ)^1 := by
      have hnat : (36713 : ℕ)^5*100000000000000000000^1 ≤ 21342699506403643077^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36713 50000 21342699506403643077 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36713/50000 : ℝ)) (X := (21342699506403643077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (121342699506403643077/100000000000000000000 : ℝ) ≤ (2078895820658657/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (121342699506403643077/100000000000000000000 : ℝ)^1 ≤ (2078895820658657/2000000000000000 : ℝ)^5 := by
      have hnat : (121342699506403643077 : ℕ)^1*2000000000000000^5 ≤ 2078895820658657^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121342699506403643077 100000000000000000000 2078895820658657 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2078895820658657/2000000000000000 : ℝ)) (X := (121342699506403643077/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (71342699506403643077/50000000000000000000 : ℝ) ≤ (10736825796826879/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (71342699506403643077/50000000000000000000 : ℝ)^1 ≤ (10736825796826879/10000000000000000 : ℝ)^5 := by
      have hnat : (71342699506403643077 : ℕ)^1*10000000000000000^5 ≤ 10736825796826879^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71342699506403643077 50000000000000000000 10736825796826879 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10736825796826879/10000000000000000 : ℝ)) (X := (71342699506403643077/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(78895820658657/1468520000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(171173346766797/3671300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (36713/50000 : ℝ)) (alpha := (78895820658657/1468520000000000 : ℝ)) (beta := (171173346766797/3671300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36713/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(78895820658657/1468520000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(171173346766797/3671300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (33981/50000 : ℝ) ^ (5 : ℝ) ≤ (14498756444215075871/100000000000000000000 : ℝ) := by
    have hpowers : (33981/50000 : ℝ)^5 ≤ (14498756444215075871/100000000000000000000 : ℝ)^1 := by
      have hnat : (33981 : ℕ)^5*100000000000000000000^1 ≤ 14498756444215075871^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33981 50000 14498756444215075871 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33981/50000 : ℝ)) (X := (14498756444215075871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (114498756444215075871/100000000000000000000 : ℝ) ≤ (10274487165471061/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (114498756444215075871/100000000000000000000 : ℝ)^1 ≤ (10274487165471061/10000000000000000 : ℝ)^5 := by
      have hnat : (114498756444215075871 : ℕ)^1*10000000000000000^5 ≤ 10274487165471061^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114498756444215075871 100000000000000000000 10274487165471061 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10274487165471061/10000000000000000 : ℝ)) (X := (114498756444215075871/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (64498756444215075871/50000000000000000000 : ℝ) ≤ (1315304422667157/1250000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (64498756444215075871/50000000000000000000 : ℝ)^1 ≤ (1315304422667157/1250000000000000 : ℝ)^5 := by
      have hnat : (64498756444215075871 : ℕ)^1*1250000000000000^5 ≤ 1315304422667157^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64498756444215075871 50000000000000000000 1315304422667157 1250000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1315304422667157/1250000000000000 : ℝ)) (X := (64498756444215075871/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(91495721823687/2265400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(49589643173239/1359240000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (33981/50000 : ℝ)) (alpha := (91495721823687/2265400000000000 : ℝ)) (beta := (49589643173239/1359240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (33981/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(91495721823687/2265400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(49589643173239/1359240000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7427/12500 : ℝ) ^ (5 : ℝ) ≤ (7404863454264841309/100000000000000000000 : ℝ) := by
    have hpowers : (7427/12500 : ℝ)^5 ≤ (7404863454264841309/100000000000000000000 : ℝ)^1 := by
      have hnat : (7427 : ℕ)^5*100000000000000000000^1 ≤ 7404863454264841309^1*12500^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7427 12500 7404863454264841309 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7427/12500 : ℝ)) (X := (7404863454264841309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (107404863454264841309/100000000000000000000 : ℝ) ≤ (5071948017456607/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (107404863454264841309/100000000000000000000 : ℝ)^1 ≤ (5071948017456607/5000000000000000 : ℝ)^5 := by
      have hnat : (107404863454264841309 : ℕ)^1*5000000000000000^5 ≤ 5071948017456607^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107404863454264841309 100000000000000000000 5071948017456607 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5071948017456607/5000000000000000 : ℝ)) (X := (107404863454264841309/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (57404863454264841309/50000000000000000000 : ℝ) ≤ (5140031033677981/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (57404863454264841309/50000000000000000000 : ℝ)^1 ≤ (5140031033677981/5000000000000000 : ℝ)^5 := by
      have hnat : (57404863454264841309 : ℕ)^1*5000000000000000^5 ≤ 5140031033677981^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57404863454264841309 50000000000000000000 5140031033677981 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5140031033677981/5000000000000000 : ℝ)) (X := (57404863454264841309/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(71948017456607/2970800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(4863072587241/212200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (7427/12500 : ℝ)) (alpha := (71948017456607/2970800000000000 : ℝ)) (beta := (4863072587241/212200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7427/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(71948017456607/2970800000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(4863072587241/212200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-188931067/625000000 : ℝ)*X 0 0+(2983464369/10000000000 : ℝ)*X 0 1+(-6192150059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1762983099/5000000000 : ℝ)*X 1 0+(-868596179/2500000000 : ℝ)*X 1 1+(-2663393487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((230289899/400000000 : ℝ)*X 2 0+(4984081843/10000000000 : ℝ)*X 2 1+(49949021/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3693821223/10000000000 : ℝ)*X 0 0+(121418073/200000000 : ℝ)*X 0 1+(-606059703/2500000000 : ℝ)*X 0 2+(3693821223/10000000000 : ℝ)*X 1 0+(121418073/200000000 : ℝ)*X 1 1+(-606059703/2500000000 : ℝ)*X 1 2+(3693821223/10000000000 : ℝ)*X 2 0+(121418073/200000000 : ℝ)*X 2 1+(-606059703/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320050_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-69420818883900362598448374370203/8412562900000000000000000000000 : ℝ) := by norm_num
    linear_combination (14577/1000000000000 : ℝ)*(base12) + (5743/500000000000 : ℝ)*(base16) + (223/50000000000 : ℝ)*(base23) + (82023268037/1000000000000 : ℝ)*(base39) + (4273/250000000000 : ℝ)*(base40) + (24193/500000000000 : ℝ)*(base53) + (3/1250000000 : ℝ)*(base59) + (123118616609/250000000000 : ℝ)*(base60) + (4693/2500 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (938599975807/500000000000 : ℝ)*(major_s1_2) + (550136093047/200000000000 : ℝ)*(sp_s1_0) + (1375340234163/500000000000 : ℝ)*(sp_s1_1) + (2750680523737/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2750680528197/1000000000000 : ℝ)*(f.sum) + (3960325666072674977/16825125800000000000000000000000 : ℝ)*base63 + (22278704417663/106100000000000000000000000 : ℝ)*base64 + (32590612026313/67962000000000000000000000 : ℝ)*base67 + (81586486533231/1485400000000000000000000000 : ℝ)*base69 + (1207639104288085889/3895249300000000000000000000000 : ℝ)*base70 + (30874805435653/91782500000000000000000000 : ℝ)*base73 + (1141222358899/4530800000000000000000000 : ℝ)*base75 + (115465033725517/367130000000000000000000000 : ℝ)*base77 + (140226223401287081/499017781200000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b029 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 50 ≤ c.val) (hhi : c.val < 51)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=50 := by omega
  rcases hc with rfl
  · exact collision_c320050 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 50 ≤ c.val) (hhi : c.val < 51)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
