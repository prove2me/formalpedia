-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:58:29.989963+00:00
-- url     : https://prove2.me/submissions/1b947eee-81f4-4540-8f0d-f41376a38300

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
theorem collision_support_c311069_s0_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042003407/10000000000 : ℝ)*x 0 + (-3650681341/5000000000 : ℝ)*x 1 + (1446170037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042003407/10000000000 : ℝ)^9 ≤ (12969694227521/100000000000000 : ℝ)^7 := by
    have hnat : (2042003407 : ℕ)^9*100000000000000^7 ≤ 12969694227521^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042003407 10000000000 12969694227521 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3650681341/5000000000 : ℝ)^9 ≤ (33369252268753/50000000000000 : ℝ)^7 := by
    have hnat : (3650681341 : ℕ)^9*50000000000000^7 ≤ 33369252268753^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3650681341 5000000000 33369252268753 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1446170037/5000000000 : ℝ)^9 ≤ (20291801212033/100000000000000 : ℝ)^7 := by
    have hnat : (1446170037 : ℕ)^9*100000000000000^7 ≤ 20291801212033^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446170037 5000000000 20291801212033 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042003407/10000000000 : ℝ), (-3650681341/5000000000 : ℝ), (1446170037/5000000000 : ℝ)] ![(12969694227521/100000000000000 : ℝ), (33369252268753/50000000000000 : ℝ), (20291801212033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042003407/10000000000 : ℝ)|^9 ≤ (12969694227521/100000000000000 : ℝ)^7
        have hw : |(-2042003407/10000000000 : ℝ)|=(2042003407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3650681341/5000000000 : ℝ)|^9 ≤ (33369252268753/50000000000000 : ℝ)^7
        have hw : |(-3650681341/5000000000 : ℝ)|=(3650681341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1446170037/5000000000 : ℝ)|^9 ≤ (20291801212033/100000000000000 : ℝ)^7
        have hw : |(1446170037/5000000000 : ℝ)|=(1446170037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1458250427/2500000000 : ℝ)*x 0 + (-2652110343/10000000000 : ℝ)*x 1 + (4106539333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1458250427/2500000000 : ℝ)^9 ≤ (50003929384871/100000000000000 : ℝ)^7 := by
    have hnat : (1458250427 : ℕ)^9*100000000000000^7 ≤ 50003929384871^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458250427 2500000000 50003929384871 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2652110343/10000000000 : ℝ)^9 ≤ (18151121835119/100000000000000 : ℝ)^7 := by
    have hnat : (2652110343 : ℕ)^9*100000000000000^7 ≤ 18151121835119^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652110343 10000000000 18151121835119 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4106539333/10000000000 : ℝ)^9 ≤ (3980618596683/12500000000000 : ℝ)^7 := by
    have hnat : (4106539333 : ℕ)^9*12500000000000^7 ≤ 3980618596683^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4106539333 10000000000 3980618596683 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1458250427/2500000000 : ℝ), (-2652110343/10000000000 : ℝ), (4106539333/10000000000 : ℝ)] ![(50003929384871/100000000000000 : ℝ), (18151121835119/100000000000000 : ℝ), (3980618596683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1458250427/2500000000 : ℝ)|^9 ≤ (50003929384871/100000000000000 : ℝ)^7
        have hw : |(1458250427/2500000000 : ℝ)|=(1458250427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2652110343/10000000000 : ℝ)|^9 ≤ (18151121835119/100000000000000 : ℝ)^7
        have hw : |(-2652110343/10000000000 : ℝ)|=(2652110343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4106539333/10000000000 : ℝ)|^9 ≤ (3980618596683/12500000000000 : ℝ)^7
        have hw : |(4106539333/10000000000 : ℝ)|=(4106539333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1641272541/10000000000 : ℝ)*x 0 + (-1598022901/2000000000 : ℝ)*x 1 + (9055171/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1641272541/10000000000 : ℝ)^9 ≤ (4896847997571/50000000000000 : ℝ)^7 := by
    have hnat : (1641272541 : ℕ)^9*50000000000000^7 ≤ 4896847997571^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641272541 10000000000 4896847997571 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1598022901/2000000000 : ℝ)^9 ≤ (18734884185513/25000000000000 : ℝ)^7 := by
    have hnat : (1598022901 : ℕ)^9*25000000000000^7 ≤ 18734884185513^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598022901 2000000000 18734884185513 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9055171/39062500 : ℝ)^9 ≤ (15266767250437/100000000000000 : ℝ)^7 := by
    have hnat : (9055171 : ℕ)^9*100000000000000^7 ≤ 15266767250437^7*39062500^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9055171 39062500 15266767250437 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1641272541/10000000000 : ℝ), (-1598022901/2000000000 : ℝ), (9055171/39062500 : ℝ)] ![(4896847997571/50000000000000 : ℝ), (18734884185513/25000000000000 : ℝ), (15266767250437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1641272541/10000000000 : ℝ)|^9 ≤ (4896847997571/50000000000000 : ℝ)^7
        have hw : |(-1641272541/10000000000 : ℝ)|=(1641272541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1598022901/2000000000 : ℝ)|^9 ≤ (18734884185513/25000000000000 : ℝ)^7
        have hw : |(-1598022901/2000000000 : ℝ)|=(1598022901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9055171/39062500 : ℝ)|^9 ≤ (15266767250437/100000000000000 : ℝ)^7
        have hw : |(9055171/39062500 : ℝ)|=(9055171/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (22732467/40000000 : ℝ)*x 0 + (1273848779/5000000000 : ℝ)*x 1 + (2180514101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22732467/40000000 : ℝ)^9 ≤ (24179007041821/50000000000000 : ℝ)^7 := by
    have hnat : (22732467 : ℕ)^9*50000000000000^7 ≤ 24179007041821^7*40000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22732467 40000000 24179007041821 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273848779/5000000000 : ℝ)^9 ≤ (8618780853823/50000000000000 : ℝ)^7 := by
    have hnat : (1273848779 : ℕ)^9*50000000000000^7 ≤ 8618780853823^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273848779 5000000000 8618780853823 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180514101/5000000000 : ℝ)^9 ≤ (34404424201437/100000000000000 : ℝ)^7 := by
    have hnat : (2180514101 : ℕ)^9*100000000000000^7 ≤ 34404424201437^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180514101 5000000000 34404424201437 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22732467/40000000 : ℝ), (1273848779/5000000000 : ℝ), (2180514101/5000000000 : ℝ)] ![(24179007041821/50000000000000 : ℝ), (8618780853823/50000000000000 : ℝ), (34404424201437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22732467/40000000 : ℝ)|^9 ≤ (24179007041821/50000000000000 : ℝ)^7
        have hw : |(22732467/40000000 : ℝ)|=(22732467/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1273848779/5000000000 : ℝ)|^9 ≤ (8618780853823/50000000000000 : ℝ)^7
        have hw : |(1273848779/5000000000 : ℝ)|=(1273848779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180514101/5000000000 : ℝ)|^9 ≤ (34404424201437/100000000000000 : ℝ)^7
        have hw : |(2180514101/5000000000 : ℝ)|=(2180514101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4096981531/10000000000 : ℝ)*x 0 + (-3400997/12500000 : ℝ)*x 1 + (-5786552849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096981531/10000000000 : ℝ)^9 ≤ (31749686144623/100000000000000 : ℝ)^7 := by
    have hnat : (4096981531 : ℕ)^9*100000000000000^7 ≤ 31749686144623^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096981531 10000000000 31749686144623 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3400997/12500000 : ℝ)^9 ≤ (2344719458797/12500000000000 : ℝ)^7 := by
    have hnat : (3400997 : ℕ)^9*12500000000000^7 ≤ 2344719458797^7*12500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3400997 12500000 2344719458797 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5786552849/10000000000 : ℝ)^9 ≤ (4949255816883/10000000000000 : ℝ)^7 := by
    have hnat : (5786552849 : ℕ)^9*10000000000000^7 ≤ 4949255816883^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5786552849 10000000000 4949255816883 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096981531/10000000000 : ℝ), (-3400997/12500000 : ℝ), (-5786552849/10000000000 : ℝ)] ![(31749686144623/100000000000000 : ℝ), (2344719458797/12500000000000 : ℝ), (4949255816883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096981531/10000000000 : ℝ)|^9 ≤ (31749686144623/100000000000000 : ℝ)^7
        have hw : |(4096981531/10000000000 : ℝ)|=(4096981531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3400997/12500000 : ℝ)|^9 ≤ (2344719458797/12500000000000 : ℝ)^7
        have hw : |(-3400997/12500000 : ℝ)|=(3400997/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5786552849/10000000000 : ℝ)|^9 ≤ (4949255816883/10000000000000 : ℝ)^7
        have hw : |(-5786552849/10000000000 : ℝ)|=(5786552849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207716797/10000000000 : ℝ)*x 0 + (-1820897019/2500000000 : ℝ)*x 1 + (345365427/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207716797/10000000000 : ℝ)^9 ≤ (7169165604377/50000000000000 : ℝ)^7 := by
    have hnat : (2207716797 : ℕ)^9*50000000000000^7 ≤ 7169165604377^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207716797 10000000000 7169165604377 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820897019/2500000000 : ℝ)^9 ≤ (33264843769103/50000000000000 : ℝ)^7 := by
    have hnat : (1820897019 : ℕ)^9*50000000000000^7 ≤ 33264843769103^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820897019 2500000000 33264843769103 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345365427/1250000000 : ℝ)^9 ≤ (3826396247383/20000000000000 : ℝ)^7 := by
    have hnat : (345365427 : ℕ)^9*20000000000000^7 ≤ 3826396247383^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345365427 1250000000 3826396247383 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207716797/10000000000 : ℝ), (-1820897019/2500000000 : ℝ), (345365427/1250000000 : ℝ)] ![(7169165604377/50000000000000 : ℝ), (33264843769103/50000000000000 : ℝ), (3826396247383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207716797/10000000000 : ℝ)|^9 ≤ (7169165604377/50000000000000 : ℝ)^7
        have hw : |(-2207716797/10000000000 : ℝ)|=(2207716797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820897019/2500000000 : ℝ)|^9 ≤ (33264843769103/50000000000000 : ℝ)^7
        have hw : |(-1820897019/2500000000 : ℝ)|=(1820897019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345365427/1250000000 : ℝ)|^9 ≤ (3826396247383/20000000000000 : ℝ)^7
        have hw : |(345365427/1250000000 : ℝ)|=(345365427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5845312799/10000000000 : ℝ)*x 0 + (1270981901/5000000000 : ℝ)*x 1 + (4189317481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5845312799/10000000000 : ℝ)^9 ≤ (3133728868827/6250000000000 : ℝ)^7 := by
    have hnat : (5845312799 : ℕ)^9*6250000000000^7 ≤ 3133728868827^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845312799 10000000000 3133728868827 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270981901/5000000000 : ℝ)^9 ≤ (17187699452909/100000000000000 : ℝ)^7 := by
    have hnat : (1270981901 : ℕ)^9*100000000000000^7 ≤ 17187699452909^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270981901 5000000000 17187699452909 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4189317481/10000000000 : ℝ)^9 ≤ (6534527726197/20000000000000 : ℝ)^7 := by
    have hnat : (4189317481 : ℕ)^9*20000000000000^7 ≤ 6534527726197^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189317481 10000000000 6534527726197 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5845312799/10000000000 : ℝ), (1270981901/5000000000 : ℝ), (4189317481/10000000000 : ℝ)] ![(3133728868827/6250000000000 : ℝ), (17187699452909/100000000000000 : ℝ), (6534527726197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5845312799/10000000000 : ℝ)|^9 ≤ (3133728868827/6250000000000 : ℝ)^7
        have hw : |(5845312799/10000000000 : ℝ)|=(5845312799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270981901/5000000000 : ℝ)|^9 ≤ (17187699452909/100000000000000 : ℝ)^7
        have hw : |(1270981901/5000000000 : ℝ)|=(1270981901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4189317481/10000000000 : ℝ)|^9 ≤ (6534527726197/20000000000000 : ℝ)^7
        have hw : |(4189317481/10000000000 : ℝ)|=(4189317481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3763656199/10000000000 : ℝ)*x 0 + (-633843183/2000000000 : ℝ)*x 1 + (-2857605089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3763656199/10000000000 : ℝ)^9 ≤ (28467913878223/100000000000000 : ℝ)^7 := by
    have hnat : (3763656199 : ℕ)^9*100000000000000^7 ≤ 28467913878223^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763656199 10000000000 28467913878223 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633843183/2000000000 : ℝ)^9 ≤ (22822679749369/100000000000000 : ℝ)^7 := by
    have hnat : (633843183 : ℕ)^9*100000000000000^7 ≤ 22822679749369^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633843183 2000000000 22822679749369 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2857605089/5000000000 : ℝ)^9 ≤ (48709406356423/100000000000000 : ℝ)^7 := by
    have hnat : (2857605089 : ℕ)^9*100000000000000^7 ≤ 48709406356423^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857605089 5000000000 48709406356423 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3763656199/10000000000 : ℝ), (-633843183/2000000000 : ℝ), (-2857605089/5000000000 : ℝ)] ![(28467913878223/100000000000000 : ℝ), (22822679749369/100000000000000 : ℝ), (48709406356423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3763656199/10000000000 : ℝ)|^9 ≤ (28467913878223/100000000000000 : ℝ)^7
        have hw : |(3763656199/10000000000 : ℝ)|=(3763656199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-633843183/2000000000 : ℝ)|^9 ≤ (22822679749369/100000000000000 : ℝ)^7
        have hw : |(-633843183/2000000000 : ℝ)|=(633843183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2857605089/5000000000 : ℝ)|^9 ≤ (48709406356423/100000000000000 : ℝ)^7
        have hw : |(-2857605089/5000000000 : ℝ)|=(2857605089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_19 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5845312799/10000000000 : ℝ)*x 0 + (-1617986309/5000000000 : ℝ)*x 1 + (3551100489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5845312799/10000000000 : ℝ)^9 ≤ (3133728868827/6250000000000 : ℝ)^7 := by
    have hnat : (5845312799 : ℕ)^9*6250000000000^7 ≤ 3133728868827^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845312799 10000000000 3133728868827 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1617986309/5000000000 : ℝ)^9 ≤ (732581997429/3125000000000 : ℝ)^7 := by
    have hnat : (1617986309 : ℕ)^9*3125000000000^7 ≤ 732581997429^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617986309 5000000000 732581997429 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3551100489/10000000000 : ℝ)^9 ≤ (26417714174279/100000000000000 : ℝ)^7 := by
    have hnat : (3551100489 : ℕ)^9*100000000000000^7 ≤ 26417714174279^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3551100489 10000000000 26417714174279 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5845312799/10000000000 : ℝ), (-1617986309/5000000000 : ℝ), (3551100489/10000000000 : ℝ)] ![(3133728868827/6250000000000 : ℝ), (732581997429/3125000000000 : ℝ), (26417714174279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5845312799/10000000000 : ℝ)|^9 ≤ (3133728868827/6250000000000 : ℝ)^7
        have hw : |(5845312799/10000000000 : ℝ)|=(5845312799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1617986309/5000000000 : ℝ)|^9 ≤ (732581997429/3125000000000 : ℝ)^7
        have hw : |(-1617986309/5000000000 : ℝ)|=(1617986309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3551100489/10000000000 : ℝ)|^9 ≤ (26417714174279/100000000000000 : ℝ)^7
        have hw : |(3551100489/10000000000 : ℝ)|=(3551100489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1459214447/10000000000 : ℝ)*x 0 + (-7886964073/10000000000 : ℝ)*x 1 + (2621514501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1459214447/10000000000 : ℝ)^9 ≤ (8419688267859/100000000000000 : ℝ)^7 := by
    have hnat : (1459214447 : ℕ)^9*100000000000000^7 ≤ 8419688267859^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459214447 10000000000 8419688267859 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7886964073/10000000000 : ℝ)^9 ≤ (7369797204917/10000000000000 : ℝ)^7 := by
    have hnat : (7886964073 : ℕ)^9*10000000000000^7 ≤ 7369797204917^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7886964073 10000000000 7369797204917 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621514501/10000000000 : ℝ)^9 ≤ (8941169834641/50000000000000 : ℝ)^7 := by
    have hnat : (2621514501 : ℕ)^9*50000000000000^7 ≤ 8941169834641^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621514501 10000000000 8941169834641 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1459214447/10000000000 : ℝ), (-7886964073/10000000000 : ℝ), (2621514501/10000000000 : ℝ)] ![(8419688267859/100000000000000 : ℝ), (7369797204917/10000000000000 : ℝ), (8941169834641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1459214447/10000000000 : ℝ)|^9 ≤ (8419688267859/100000000000000 : ℝ)^7
        have hw : |(-1459214447/10000000000 : ℝ)|=(1459214447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7886964073/10000000000 : ℝ)|^9 ≤ (7369797204917/10000000000000 : ℝ)^7
        have hw : |(-7886964073/10000000000 : ℝ)|=(7886964073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621514501/10000000000 : ℝ)|^9 ≤ (8941169834641/50000000000000 : ℝ)^7
        have hw : |(2621514501/10000000000 : ℝ)|=(2621514501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6667472499/10000000000 : ℝ)*x 0 + (88760627/400000000 : ℝ)*x 1 + (3526634879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6667472499/10000000000 : ℝ)^9 ≤ (59383315630011/100000000000000 : ℝ)^7 := by
    have hnat : (6667472499 : ℕ)^9*100000000000000^7 ≤ 59383315630011^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6667472499 10000000000 59383315630011 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88760627/400000000 : ℝ)^9 ≤ (14432748613427/100000000000000 : ℝ)^7 := by
    have hnat : (88760627 : ℕ)^9*100000000000000^7 ≤ 14432748613427^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88760627 400000000 14432748613427 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3526634879/10000000000 : ℝ)^9 ≤ (13091967873069/50000000000000 : ℝ)^7 := by
    have hnat : (3526634879 : ℕ)^9*50000000000000^7 ≤ 13091967873069^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3526634879 10000000000 13091967873069 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6667472499/10000000000 : ℝ), (88760627/400000000 : ℝ), (3526634879/10000000000 : ℝ)] ![(59383315630011/100000000000000 : ℝ), (14432748613427/100000000000000 : ℝ), (13091967873069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6667472499/10000000000 : ℝ)|^9 ≤ (59383315630011/100000000000000 : ℝ)^7
        have hw : |(6667472499/10000000000 : ℝ)|=(6667472499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88760627/400000000 : ℝ)|^9 ≤ (14432748613427/100000000000000 : ℝ)^7
        have hw : |(88760627/400000000 : ℝ)|=(88760627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3526634879/10000000000 : ℝ)|^9 ≤ (13091967873069/50000000000000 : ℝ)^7
        have hw : |(3526634879/10000000000 : ℝ)|=(3526634879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3330499579/10000000000 : ℝ)*x 0 + (-3296346741/10000000000 : ℝ)*x 1 + (-74791551/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3330499579/10000000000 : ℝ)^9 ≤ (12163358210437/50000000000000 : ℝ)^7 := by
    have hnat : (3330499579 : ℕ)^9*50000000000000^7 ≤ 12163358210437^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3330499579 10000000000 12163358210437 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3296346741/10000000000 : ℝ)^9 ≤ (240064531511/1000000000000 : ℝ)^7 := by
    have hnat : (3296346741 : ℕ)^9*1000000000000^7 ≤ 240064531511^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3296346741 10000000000 240064531511 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74791551/125000000 : ℝ)^9 ≤ (51666830412869/100000000000000 : ℝ)^7 := by
    have hnat : (74791551 : ℕ)^9*100000000000000^7 ≤ 51666830412869^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74791551 125000000 51666830412869 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3330499579/10000000000 : ℝ), (-3296346741/10000000000 : ℝ), (-74791551/125000000 : ℝ)] ![(12163358210437/50000000000000 : ℝ), (240064531511/1000000000000 : ℝ), (51666830412869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3330499579/10000000000 : ℝ)|^9 ≤ (12163358210437/50000000000000 : ℝ)^7
        have hw : |(3330499579/10000000000 : ℝ)|=(3330499579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3296346741/10000000000 : ℝ)|^9 ≤ (240064531511/1000000000000 : ℝ)^7
        have hw : |(-3296346741/10000000000 : ℝ)|=(3296346741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74791551/125000000 : ℝ)|^9 ≤ (51666830412869/100000000000000 : ℝ)^7
        have hw : |(-74791551/125000000 : ℝ)|=(74791551/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s0_25 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6667472499/10000000000 : ℝ)*x 0 + (-88760627/400000000 : ℝ)*x 1 + (3526634879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6667472499/10000000000 : ℝ)^9 ≤ (59383315630011/100000000000000 : ℝ)^7 := by
    have hnat : (6667472499 : ℕ)^9*100000000000000^7 ≤ 59383315630011^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6667472499 10000000000 59383315630011 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88760627/400000000 : ℝ)^9 ≤ (14432748613427/100000000000000 : ℝ)^7 := by
    have hnat : (88760627 : ℕ)^9*100000000000000^7 ≤ 14432748613427^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88760627 400000000 14432748613427 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3526634879/10000000000 : ℝ)^9 ≤ (13091967873069/50000000000000 : ℝ)^7 := by
    have hnat : (3526634879 : ℕ)^9*50000000000000^7 ≤ 13091967873069^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3526634879 10000000000 13091967873069 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6667472499/10000000000 : ℝ), (-88760627/400000000 : ℝ), (3526634879/10000000000 : ℝ)] ![(59383315630011/100000000000000 : ℝ), (14432748613427/100000000000000 : ℝ), (13091967873069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6667472499/10000000000 : ℝ)|^9 ≤ (59383315630011/100000000000000 : ℝ)^7
        have hw : |(6667472499/10000000000 : ℝ)|=(6667472499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88760627/400000000 : ℝ)|^9 ≤ (14432748613427/100000000000000 : ℝ)^7
        have hw : |(-88760627/400000000 : ℝ)|=(88760627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3526634879/10000000000 : ℝ)|^9 ≤ (13091967873069/50000000000000 : ℝ)^7
        have hw : |(3526634879/10000000000 : ℝ)|=(3526634879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-655382169/2000000000 : ℝ)*x 0 + (-1088602523/2000000000 : ℝ)*x 1 + (1981860833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655382169/2000000000 : ℝ)^9 ≤ (23824618073783/100000000000000 : ℝ)^7 := by
    have hnat : (655382169 : ℕ)^9*100000000000000^7 ≤ 23824618073783^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655382169 2000000000 23824618073783 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088602523/2000000000 : ℝ)^9 ≤ (11436809190741/25000000000000 : ℝ)^7 := by
    have hnat : (1088602523 : ℕ)^9*25000000000000^7 ≤ 11436809190741^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088602523 2000000000 11436809190741 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981860833/5000000000 : ℝ)^9 ≤ (15214072575511/50000000000000 : ℝ)^7 := by
    have hnat : (1981860833 : ℕ)^9*50000000000000^7 ≤ 15214072575511^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981860833 5000000000 15214072575511 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-655382169/2000000000 : ℝ), (-1088602523/2000000000 : ℝ), (1981860833/5000000000 : ℝ)] ![(23824618073783/100000000000000 : ℝ), (11436809190741/25000000000000 : ℝ), (15214072575511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-655382169/2000000000 : ℝ)|^9 ≤ (23824618073783/100000000000000 : ℝ)^7
        have hw : |(-655382169/2000000000 : ℝ)|=(655382169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088602523/2000000000 : ℝ)|^9 ≤ (11436809190741/25000000000000 : ℝ)^7
        have hw : |(-1088602523/2000000000 : ℝ)|=(1088602523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1981860833/5000000000 : ℝ)|^9 ≤ (15214072575511/50000000000000 : ℝ)^7
        have hw : |(1981860833/5000000000 : ℝ)|=(1981860833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2607585261/5000000000 : ℝ)*x 0 + (168112507/500000000 : ℝ)*x 1 + (4129562941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2607585261/5000000000 : ℝ)^9 ≤ (21650009577051/50000000000000 : ℝ)^7 := by
    have hnat : (2607585261 : ℕ)^9*50000000000000^7 ≤ 21650009577051^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607585261 5000000000 21650009577051 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168112507/500000000 : ℝ)^9 ≤ (12312647864877/50000000000000 : ℝ)^7 := by
    have hnat : (168112507 : ℕ)^9*50000000000000^7 ≤ 12312647864877^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168112507 500000000 12312647864877 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129562941/10000000000 : ℝ)^9 ≤ (8018671273447/25000000000000 : ℝ)^7 := by
    have hnat : (4129562941 : ℕ)^9*25000000000000^7 ≤ 8018671273447^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129562941 10000000000 8018671273447 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2607585261/5000000000 : ℝ), (168112507/500000000 : ℝ), (4129562941/10000000000 : ℝ)] ![(21650009577051/50000000000000 : ℝ), (12312647864877/50000000000000 : ℝ), (8018671273447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2607585261/5000000000 : ℝ)|^9 ≤ (21650009577051/50000000000000 : ℝ)^7
        have hw : |(2607585261/5000000000 : ℝ)|=(2607585261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168112507/500000000 : ℝ)|^9 ≤ (12312647864877/50000000000000 : ℝ)^7
        have hw : |(168112507/500000000 : ℝ)|=(168112507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129562941/10000000000 : ℝ)|^9 ≤ (8018671273447/25000000000000 : ℝ)^7
        have hw : |(4129562941/10000000000 : ℝ)|=(4129562941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1999193749/5000000000 : ℝ)*x 0 + (-978283481/2500000000 : ℝ)*x 1 + (-604551661/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999193749/5000000000 : ℝ)^9 ≤ (30770723229741/100000000000000 : ℝ)^7 := by
    have hnat : (1999193749 : ℕ)^9*100000000000000^7 ≤ 30770723229741^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999193749 5000000000 30770723229741 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978283481/2500000000 : ℝ)^9 ≤ (1870609854499/6250000000000 : ℝ)^7 := by
    have hnat : (978283481 : ℕ)^9*6250000000000^7 ≤ 1870609854499^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978283481 2500000000 1870609854499 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604551661/1250000000 : ℝ)^9 ≤ (39299519089711/100000000000000 : ℝ)^7 := by
    have hnat : (604551661 : ℕ)^9*100000000000000^7 ≤ 39299519089711^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604551661 1250000000 39299519089711 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999193749/5000000000 : ℝ), (-978283481/2500000000 : ℝ), (-604551661/1250000000 : ℝ)] ![(30770723229741/100000000000000 : ℝ), (1870609854499/6250000000000 : ℝ), (39299519089711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999193749/5000000000 : ℝ)|^9 ≤ (30770723229741/100000000000000 : ℝ)^7
        have hw : |(1999193749/5000000000 : ℝ)|=(1999193749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978283481/2500000000 : ℝ)|^9 ≤ (1870609854499/6250000000000 : ℝ)^7
        have hw : |(-978283481/2500000000 : ℝ)|=(978283481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-604551661/1250000000 : ℝ)|^9 ≤ (39299519089711/100000000000000 : ℝ)^7
        have hw : |(-604551661/1250000000 : ℝ)|=(604551661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311069_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4750229029/10000000000 : ℝ)*x 0 + (-264818793/625000000 : ℝ)*x 1 + (1880702623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4750229029/10000000000 : ℝ)^9 ≤ (38401419451823/100000000000000 : ℝ)^7 := by
    have hnat : (4750229029 : ℕ)^9*100000000000000^7 ≤ 38401419451823^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750229029 10000000000 38401419451823 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264818793/625000000 : ℝ)^9 ≤ (33152555332029/100000000000000 : ℝ)^7 := by
    have hnat : (264818793 : ℕ)^9*100000000000000^7 ≤ 33152555332029^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264818793 625000000 33152555332029 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1880702623/5000000000 : ℝ)^9 ≤ (28446025202757/100000000000000 : ℝ)^7 := by
    have hnat : (1880702623 : ℕ)^9*100000000000000^7 ≤ 28446025202757^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880702623 5000000000 28446025202757 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4750229029/10000000000 : ℝ), (-264818793/625000000 : ℝ), (1880702623/5000000000 : ℝ)] ![(38401419451823/100000000000000 : ℝ), (33152555332029/100000000000000 : ℝ), (28446025202757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4750229029/10000000000 : ℝ)|^9 ≤ (38401419451823/100000000000000 : ℝ)^7
        have hw : |(4750229029/10000000000 : ℝ)|=(4750229029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264818793/625000000 : ℝ)|^9 ≤ (33152555332029/100000000000000 : ℝ)^7
        have hw : |(-264818793/625000000 : ℝ)|=(264818793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1880702623/5000000000 : ℝ)|^9 ≤ (28446025202757/100000000000000 : ℝ)^7
        have hw : |(1880702623/5000000000 : ℝ)|=(1880702623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311069 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2042003407/10000000000 : ℝ)*X 0 0+(-3650681341/5000000000 : ℝ)*X 0 1+(1446170037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1458250427/2500000000 : ℝ)*X 0 0+(-2652110343/10000000000 : ℝ)*X 0 1+(4106539333/10000000000 : ℝ)*X 0 2+(1458250427/2500000000 : ℝ)*X 1 0+(-2652110343/10000000000 : ℝ)*X 1 1+(4106539333/10000000000 : ℝ)*X 1 2+(1458250427/2500000000 : ℝ)*X 2 0+(-2652110343/10000000000 : ℝ)*X 2 1+(4106539333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1641272541/10000000000 : ℝ)*X 0 0+(-1598022901/2000000000 : ℝ)*X 0 1+(9055171/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((22732467/40000000 : ℝ)*X 1 0+(1273848779/5000000000 : ℝ)*X 1 1+(2180514101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4096981531/10000000000 : ℝ)*X 2 0+(-3400997/12500000 : ℝ)*X 2 1+(-5786552849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2207716797/10000000000 : ℝ)*X 0 0+(-1820897019/2500000000 : ℝ)*X 0 1+(345365427/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((5845312799/10000000000 : ℝ)*X 1 0+(1270981901/5000000000 : ℝ)*X 1 1+(4189317481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3763656199/10000000000 : ℝ)*X 2 0+(-633843183/2000000000 : ℝ)*X 2 1+(-2857605089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((5845312799/10000000000 : ℝ)*X 0 0+(-1617986309/5000000000 : ℝ)*X 0 1+(3551100489/10000000000 : ℝ)*X 0 2+(5845312799/10000000000 : ℝ)*X 1 0+(-1617986309/5000000000 : ℝ)*X 1 1+(3551100489/10000000000 : ℝ)*X 1 2+(5845312799/10000000000 : ℝ)*X 2 0+(-1617986309/5000000000 : ℝ)*X 2 1+(3551100489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1459214447/10000000000 : ℝ)*X 0 0+(-7886964073/10000000000 : ℝ)*X 0 1+(2621514501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((6667472499/10000000000 : ℝ)*X 1 0+(88760627/400000000 : ℝ)*X 1 1+(3526634879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3330499579/10000000000 : ℝ)*X 2 0+(-3296346741/10000000000 : ℝ)*X 2 1+(-74791551/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((6667472499/10000000000 : ℝ)*X 0 0+(-88760627/400000000 : ℝ)*X 0 1+(3526634879/10000000000 : ℝ)*X 0 2+(6667472499/10000000000 : ℝ)*X 1 0+(-88760627/400000000 : ℝ)*X 1 1+(3526634879/10000000000 : ℝ)*X 1 2+(6667472499/10000000000 : ℝ)*X 2 0+(-88760627/400000000 : ℝ)*X 2 1+(3526634879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((15253/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15253/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11429481110036046386049/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1430461536853/500000000000 : ℝ)*(base3) + (1126790242863/1000000000000 : ℝ)*(base40) + (3733098835861/1000000000000 : ℝ)*(base49) + (2390250330767/1000000000000 : ℝ)*(base50) + (1651113/500000000000 : ℝ)*(base60) + (2350937208931/500000000000 : ℝ)*(major_s0_0) + (2350937208931/500000000000 : ℝ)*(major_s0_1) + (2350937208931/500000000000 : ℝ)*(major_s0_2) + (694363/250000000000 : ℝ)*(sp_s0_6) + (3271319997309/500000000000 : ℝ)*(sp_s0_7) + (1880748602081/200000000000 : ℝ)*(sp_s0_8) + (6542737005769/1000000000000 : ℝ)*(sp_s0_9) + (8293093/100000000000 : ℝ)*(sp_s0_15) + (179942081/1000000000000 : ℝ)*(sp_s0_20) + (2860925851159/1000000000000 : ℝ)*(f.failure) + (6542819936699/1000000000000 : ℝ)*(f.sum) + (86715989246317/5000000000000000000000000000 : ℝ)*base62 + (70948651952293/312500000000000000000000000 : ℝ)*base65 + (139742033403399/1000000000000000000000000000 : ℝ)*base66 + (200522509696601/1000000000000000000000000000 : ℝ)*base68 + (3126938730746317/5000000000000000000000000000 : ℝ)*base70 + (90926807828957/312500000000000000000000000 : ℝ)*base73 + (70446706297707/312500000000000000000000000 : ℝ)*base74 + (180606194496601/1000000000000000000000000000 : ℝ)*base76 + (3351522206246317/5000000000000000000000000000 : ℝ)*base79 + (19833/25000000000000000 : ℝ)*base87 + (19833/25000000000000000 : ℝ)*base89 + (19833/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-2569/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-2569/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8266143905490577831773/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (953786011733/1000000000000 : ℝ)*(base3) + (613767/200000000000 : ℝ)*(base39) + (83702342937/100000000000 : ℝ)*(base40) + (582644803893/1000000000000 : ℝ)*(base49) + (574061123313/200000000000 : ℝ)*(major_s0_0) + (574061123313/200000000000 : ℝ)*(major_s0_1) + (574061123313/200000000000 : ℝ)*(major_s0_2) + (67672441/1000000000000 : ℝ)*(sp_s0_6) + (48035241/1000000000000 : ℝ)*(sp_s0_9) + (3994128072407/1000000000000 : ℝ)*(sp_s0_13) + (247395704207/50000000000 : ℝ)*(sp_s0_14) + (1997040018583/500000000000 : ℝ)*(sp_s0_15) + (792606737329/1000000000000 : ℝ)*(sp_s0_19) + (3996767/200000000000 : ℝ)*(sp_s0_25) + (873240202669/500000000000 : ℝ)*(f.failure) + (3994128072407/1000000000000 : ℝ)*(f.sum) + (836309250189409/2000000000000000000000000000 : ℝ)*base63 + (59240041824811/125000000000000000000000000 : ℝ)*base64 + (108237114602723/400000000000000000000000000 : ℝ)*base67 + (165030739997277/400000000000000000000000000 : ℝ)*base69 + (399742113189409/2000000000000000000000000000 : ℝ)*base71 + (3101780612311/125000000000000000000000000 : ℝ)*base73 + (96812084287689/125000000000000000000000000 : ℝ)*base75 + (56672807042723/400000000000000000000000000 : ℝ)*base76 + (926522435589409/2000000000000000000000000000 : ℝ)*base78 + (1297/12500000000000000 : ℝ)*base86 + (1297/12500000000000000 : ℝ)*base88 + (1297/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29581/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29581/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7324961069737851756123/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3307044658629/1000000000000 : ℝ)*(base3) + (1088252739617/500000000000 : ℝ)*(base40) + (4720901821191/1000000000000 : ℝ)*(base49) + (1200178253401/500000000000 : ℝ)*(base50) + (6081575080429/1000000000000 : ℝ)*(major_s0_0) + (6081575080429/1000000000000 : ℝ)*(major_s0_1) + (6081575080429/1000000000000 : ℝ)*(major_s0_2) + (13838439/250000000000 : ℝ)*(sp_s0_0) + (91078627/500000000000 : ℝ)*(sp_s0_7) + (22311177/500000000000 : ℝ)*(sp_s0_19) + (8462484842239/1000000000000 : ℝ)*(sp_s0_20) + (5884883505939/500000000000 : ℝ)*(sp_s0_21) + (8462722353249/1000000000000 : ℝ)*(sp_s0_22) + (196668042483/500000000000 : ℝ)*(sp_s0_25) + (925106341487/250000000000 : ℝ)*(f.failure) + (8462722353249/1000000000000 : ℝ)*(f.sum) + (3263557185392797/10000000000000000000000000000 : ℝ)*base63 + (241461155602037/625000000000000000000000000 : ℝ)*base65 + (896217154952041/2000000000000000000000000000 : ℝ)*base66 + (1104494646847959/2000000000000000000000000000 : ℝ)*base68 + (2600062701607203/10000000000000000000000000000 : ℝ)*base70 + (15712228710463/625000000000000000000000000 : ℝ)*base73 + (118738144227037/625000000000000000000000000 : ℝ)*base75 + (177722980247959/2000000000000000000000000000 : ℝ)*base76 + (1282495573607203/10000000000000000000000000000 : ℝ)*base79 + (4881/6250000000000000 : ℝ)*base86 + (4881/6250000000000000 : ℝ)*base88 + (4881/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (15253/100000 : ℝ) ^ (71/16 : ℝ) ≤ (11888006013893387/50000000000000000000 : ℝ) := by
    have hpowers : (15253/100000 : ℝ)^71 ≤ (11888006013893387/50000000000000000000 : ℝ)^16 := by
      have hnat : (15253 : ℕ)^71*50000000000000000000^16 ≤ 11888006013893387^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15253 100000 11888006013893387 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15253/100000 : ℝ)) (X := (11888006013893387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50011888006013893387/50000000000000000000 : ℝ) ≤ (5000267874059699/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (50011888006013893387/50000000000000000000 : ℝ)^16 ≤ (5000267874059699/5000000000000000 : ℝ)^71 := by
      have hnat : (50011888006013893387 : ℕ)^16*5000000000000000^71 ≤ 5000267874059699^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011888006013893387 50000000000000000000 5000267874059699 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000267874059699/5000000000000000 : ℝ)) (X := (50011888006013893387/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25011888006013893387/25000000000000000000 : ℝ) ≤ (10001071397597043/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (25011888006013893387/25000000000000000000 : ℝ)^16 ≤ (10001071397597043/10000000000000000 : ℝ)^71 := by
      have hnat : (25011888006013893387 : ℕ)^16*10000000000000000^71 ≤ 10001071397597043^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011888006013893387 25000000000000000000 10001071397597043 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001071397597043/10000000000000000 : ℝ)) (X := (25011888006013893387/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(267874059699/762650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(107129895529/305060000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (15253/100000 : ℝ)) (alpha := (267874059699/762650000000000 : ℝ)) (beta := (107129895529/305060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15253/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(267874059699/762650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(107129895529/305060000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2569/100000 : ℝ) ^ (71/16 : ℝ) ≤ (4388319270863/50000000000000000000 : ℝ) := by
    have hpowers : (2569/100000 : ℝ)^71 ≤ (4388319270863/50000000000000000000 : ℝ)^16 := by
      have hnat : (2569 : ℕ)^71*50000000000000000000^16 ≤ 4388319270863^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2569 100000 4388319270863 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2569/100000 : ℝ)) (X := (4388319270863/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50000004388319270863/50000000000000000000 : ℝ) ≤ (5000000098891699/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (50000004388319270863/50000000000000000000 : ℝ)^16 ≤ (5000000098891699/5000000000000000 : ℝ)^71 := by
      have hnat : (50000004388319270863 : ℕ)^16*5000000000000000^71 ≤ 5000000098891699^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004388319270863 50000000000000000000 5000000098891699 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000098891699/5000000000000000 : ℝ)) (X := (50000004388319270863/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25000004388319270863/25000000000000000000 : ℝ) ≤ (10000000395566781/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (25000004388319270863/25000000000000000000 : ℝ)^16 ≤ (10000000395566781/10000000000000000 : ℝ)^71 := by
      have hnat : (25000004388319270863 : ℕ)^16*10000000000000000^71 ≤ 10000000395566781^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000004388319270863 25000000000000000000 10000000395566781 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000395566781/10000000000000000 : ℝ)) (X := (25000004388319270863/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(98891699/128450000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(28254769/36700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (2569/100000 : ℝ)) (alpha := (98891699/128450000000000 : ℝ)) (beta := (28254769/36700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (2569/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(98891699/128450000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(28254769/36700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (29581/100000 : ℝ) ^ (71/16 : ℝ) ≤ (56173248684952583/12500000000000000000 : ℝ) := by
    have hpowers : (29581/100000 : ℝ)^71 ≤ (56173248684952583/12500000000000000000 : ℝ)^16 := by
      have hnat : (29581 : ℕ)^71*12500000000000000000^16 ≤ 56173248684952583^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29581 100000 56173248684952583 12500000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29581/100000 : ℝ)) (X := (56173248684952583/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (12556173248684952583/12500000000000000000 : ℝ) ≤ (10010109428062977/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (12556173248684952583/12500000000000000000 : ℝ)^16 ≤ (10010109428062977/10000000000000000 : ℝ)^71 := by
      have hnat : (12556173248684952583 : ℕ)^16*10000000000000000^71 ≤ 10010109428062977^71*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12556173248684952583 12500000000000000000 10010109428062977 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010109428062977/10000000000000000 : ℝ)) (X := (12556173248684952583/12500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6306173248684952583/6250000000000000000 : ℝ) ≤ (10020183881518377/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (6306173248684952583/6250000000000000000 : ℝ)^16 ≤ (10020183881518377/10000000000000000 : ℝ)^71 := by
      have hnat : (6306173248684952583 : ℕ)^16*10000000000000000^71 ≤ 10020183881518377^71*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6306173248684952583 6250000000000000000 10020183881518377 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020183881518377/10000000000000000 : ℝ)) (X := (6306173248684952583/6250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(10109428062977/2958100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(50372267277/14790500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (29581/100000 : ℝ)) (alpha := (10109428062977/2958100000000000 : ℝ)) (beta := (50372267277/14790500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29581/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(10109428062977/2958100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(50372267277/14790500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-655382169/2000000000 : ℝ)*X 0 0+(-1088602523/2000000000 : ℝ)*X 0 1+(1981860833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2607585261/5000000000 : ℝ)*X 1 0+(168112507/500000000 : ℝ)*X 1 1+(4129562941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1999193749/5000000000 : ℝ)*X 2 0+(-978283481/2500000000 : ℝ)*X 2 1+(-604551661/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4750229029/10000000000 : ℝ)*X 0 0+(-264818793/625000000 : ℝ)*X 0 1+(1880702623/5000000000 : ℝ)*X 0 2+(4750229029/10000000000 : ℝ)*X 1 0+(-264818793/625000000 : ℝ)*X 1 1+(1880702623/5000000000 : ℝ)*X 1 2+(4750229029/10000000000 : ℝ)*X 2 0+(-264818793/625000000 : ℝ)*X 2 1+(1880702623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311069_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-55918090618045410530215138409952069/8279501521550000000000000000000000 : ℝ) := by norm_num
    linear_combination (60397/500000000000 : ℝ)*(base1) + (20721/1000000000000 : ℝ)*(base3) + (116723/1000000000000 : ℝ)*(base22) + (237763/1000000000000 : ℝ)*(base24) + (1352968177/4000000000 : ℝ)*(base40) + (34579/1000000000000 : ℝ)*(base43) + (160827851169/250000000000 : ℝ)*(base49) + (187499445377/500000000000 : ℝ)*(base50) + (41087/25000 : ℝ)*(major_s1_0) + (1643479965421/1000000000000 : ℝ)*(major_s1_1) + (41087/25000 : ℝ)*(major_s1_2) + (281408310099/125000000000 : ℝ)*(sp_s1_0) + (1125633207649/500000000000 : ℝ)*(sp_s1_1) + (2251266005511/1000000000000 : ℝ)*(sp_s1_2) + (249999964621/250000000000 : ℝ)*(sp_s1_6) + (2251266394577/1000000000000 : ℝ)*(f.sum) + (327741818893234911/1085622700000000000000000000000 : ℝ)*base63 + (2138735425271/36976250000000000000000000 : ℝ)*base64 + (4059430043543/18350000000000000000000000 : ℝ)*base67 + (3772396831381/36976250000000000000000000 : ℝ)*base69 + (69206343333454863/563998741250000000000000000000 : ℝ)*base70 + (10274939357027/76265000000000000000000000 : ℝ)*base73 + (17616144660871/36700000000000000000000000 : ℝ)*base75 + (17597129586133/38132500000000000000000000 : ℝ)*base76 + (56654742350120421/279892550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c311070_s0_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106744849/10000000000 : ℝ)*x 0 + (-2103829467/5000000000 : ℝ)*x 1 + (-6160536923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106744849/10000000000 : ℝ)^9 ≤ (2700151953673/20000000000000 : ℝ)^7 := by
    have hnat : (2106744849 : ℕ)^9*20000000000000^7 ≤ 2700151953673^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106744849 10000000000 2700151953673 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103829467/5000000000 : ℝ)^9 ≤ (32856669384409/100000000000000 : ℝ)^7 := by
    have hnat : (2103829467 : ℕ)^9*100000000000000^7 ≤ 32856669384409^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103829467 5000000000 32856669384409 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6160536923/10000000000 : ℝ)^9 ≤ (2145702833477/4000000000000 : ℝ)^7 := by
    have hnat : (6160536923 : ℕ)^9*4000000000000^7 ≤ 2145702833477^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6160536923 10000000000 2145702833477 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106744849/10000000000 : ℝ), (-2103829467/5000000000 : ℝ), (-6160536923/10000000000 : ℝ)] ![(2700151953673/20000000000000 : ℝ), (32856669384409/100000000000000 : ℝ), (2145702833477/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106744849/10000000000 : ℝ)|^9 ≤ (2700151953673/20000000000000 : ℝ)^7
        have hw : |(-2106744849/10000000000 : ℝ)|=(2106744849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103829467/5000000000 : ℝ)|^9 ≤ (32856669384409/100000000000000 : ℝ)^7
        have hw : |(-2103829467/5000000000 : ℝ)|=(2103829467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6160536923/10000000000 : ℝ)|^9 ≤ (2145702833477/4000000000000 : ℝ)^7
        have hw : |(-6160536923/10000000000 : ℝ)|=(6160536923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311070_s0_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (246421479/400000000 : ℝ)*x 0 + (4207658897/10000000000 : ℝ)*x 1 + (-1053372411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246421479/400000000 : ℝ)^9 ≤ (53642571419081/100000000000000 : ℝ)^7 := by
    have hnat : (246421479 : ℕ)^9*100000000000000^7 ≤ 53642571419081^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246421479 400000000 53642571419081 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4207658897/10000000000 : ℝ)^9 ≤ (6571333802587/20000000000000 : ℝ)^7 := by
    have hnat : (4207658897 : ℕ)^9*20000000000000^7 ≤ 6571333802587^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207658897 10000000000 6571333802587 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053372411/5000000000 : ℝ)^9 ≤ (843797471619/6250000000000 : ℝ)^7 := by
    have hnat : (1053372411 : ℕ)^9*6250000000000^7 ≤ 843797471619^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053372411 5000000000 843797471619 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(246421479/400000000 : ℝ), (4207658897/10000000000 : ℝ), (-1053372411/5000000000 : ℝ)] ![(53642571419081/100000000000000 : ℝ), (6571333802587/20000000000000 : ℝ), (843797471619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(246421479/400000000 : ℝ)|^9 ≤ (53642571419081/100000000000000 : ℝ)^7
        have hw : |(246421479/400000000 : ℝ)|=(246421479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4207658897/10000000000 : ℝ)|^9 ≤ (6571333802587/20000000000000 : ℝ)^7
        have hw : |(4207658897/10000000000 : ℝ)|=(4207658897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053372411/5000000000 : ℝ)|^9 ≤ (843797471619/6250000000000 : ℝ)^7
        have hw : |(-1053372411/5000000000 : ℝ)|=(1053372411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311070_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (774926247/2000000000 : ℝ)*x 0 + (-4988610137/10000000000 : ℝ)*x 1 + (3874631221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (774926247/2000000000 : ℝ)^9 ≤ (29551662006471/100000000000000 : ℝ)^7 := by
    have hnat : (774926247 : ℕ)^9*100000000000000^7 ≤ 29551662006471^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774926247 2000000000 29551662006471 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988610137/10000000000 : ℝ)^9 ≤ (40896676106747/100000000000000 : ℝ)^7 := by
    have hnat : (4988610137 : ℕ)^9*100000000000000^7 ≤ 40896676106747^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988610137 10000000000 40896676106747 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3874631221/10000000000 : ℝ)^9 ≤ (14775830934593/50000000000000 : ℝ)^7 := by
    have hnat : (3874631221 : ℕ)^9*50000000000000^7 ≤ 14775830934593^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3874631221 10000000000 14775830934593 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(774926247/2000000000 : ℝ), (-4988610137/10000000000 : ℝ), (3874631221/10000000000 : ℝ)] ![(29551662006471/100000000000000 : ℝ), (40896676106747/100000000000000 : ℝ), (14775830934593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(774926247/2000000000 : ℝ)|^9 ≤ (29551662006471/100000000000000 : ℝ)^7
        have hw : |(774926247/2000000000 : ℝ)|=(774926247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4988610137/10000000000 : ℝ)|^9 ≤ (40896676106747/100000000000000 : ℝ)^7
        have hw : |(-4988610137/10000000000 : ℝ)|=(4988610137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3874631221/10000000000 : ℝ)|^9 ≤ (14775830934593/50000000000000 : ℝ)^7
        have hw : |(3874631221/10000000000 : ℝ)|=(3874631221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311070_s0_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1029593901/2000000000 : ℝ)*x 0 + (-1133309497/5000000000 : ℝ)*x 1 + (-5147969417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029593901/2000000000 : ℝ)^9 ≤ (42583979245701/100000000000000 : ℝ)^7 := by
    have hnat : (1029593901 : ℕ)^9*100000000000000^7 ≤ 42583979245701^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029593901 2000000000 42583979245701 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133309497/5000000000 : ℝ)^9 ≤ (3708010607179/25000000000000 : ℝ)^7 := by
    have hnat : (1133309497 : ℕ)^9*25000000000000^7 ≤ 3708010607179^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133309497 5000000000 3708010607179 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147969417/10000000000 : ℝ)^9 ≤ (5322997288723/12500000000000 : ℝ)^7 := by
    have hnat : (5147969417 : ℕ)^9*12500000000000^7 ≤ 5322997288723^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147969417 10000000000 5322997288723 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1029593901/2000000000 : ℝ), (-1133309497/5000000000 : ℝ), (-5147969417/10000000000 : ℝ)] ![(42583979245701/100000000000000 : ℝ), (3708010607179/25000000000000 : ℝ), (5322997288723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1029593901/2000000000 : ℝ)|^9 ≤ (42583979245701/100000000000000 : ℝ)^7
        have hw : |(1029593901/2000000000 : ℝ)|=(1029593901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133309497/5000000000 : ℝ)|^9 ≤ (3708010607179/25000000000000 : ℝ)^7
        have hw : |(-1133309497/5000000000 : ℝ)|=(1133309497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5147969417/10000000000 : ℝ)|^9 ≤ (5322997288723/12500000000000 : ℝ)^7
        have hw : |(-5147969417/10000000000 : ℝ)|=(5147969417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311070 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2106744849/10000000000 : ℝ)*X 0 0+(-2103829467/5000000000 : ℝ)*X 0 1+(-6160536923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((246421479/400000000 : ℝ)*X 1 0+(4207658897/10000000000 : ℝ)*X 1 1+(-1053372411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((774926247/2000000000 : ℝ)*X 2 0+(-4988610137/10000000000 : ℝ)*X 2 1+(3874631221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1029593901/2000000000 : ℝ)*X 0 0+(-1133309497/5000000000 : ℝ)*X 0 1+(-5147969417/10000000000 : ℝ)*X 0 2+(1029593901/2000000000 : ℝ)*X 1 0+(-1133309497/5000000000 : ℝ)*X 1 1+(-5147969417/10000000000 : ℝ)*X 1 2+(1029593901/2000000000 : ℝ)*X 2 0+(-1133309497/5000000000 : ℝ)*X 2 1+(-5147969417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-17123514908884071566263880373/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13417/250000000000 : ℝ)*(base12) + (8011/500000000000 : ℝ)*(base21) + (6933/500000000000 : ℝ)*(base25) + (46385757651/100000000000 : ℝ)*(base39) + (8297/1000000000000 : ℝ)*(base40) + (60225163891/1000000000000 : ℝ)*(base49) + (272325511673/1000000000000 : ℝ)*(base59) + (821740000087/500000000000 : ℝ)*(major_s0_0) + (41087/25000 : ℝ)*(major_s0_1) + (41087/25000 : ℝ)*(major_s0_2) + (142695954187/62500000000 : ℝ)*(sp_s0_0) + (2283135320833/1000000000000 : ℝ)*(sp_s0_1) + (1141567645473/500000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (114156766033/50000000000 : ℝ)*(f.sum) + (497835519/1250000000000000000000 : ℝ)*base62 + (139268109/312500000000000000000 : ℝ)*base65 + (275635127/1250000000000000000000 : ℝ)*base67 + (211590577/400000000000000000000 : ℝ)*base69 + (681345953681323/1000000000000000000000000000 : ℝ)*base71 + (1653771232511/312500000000000000000000000 : ℝ)*base72 + (527677127/1000000000000000000000 : ℝ)*base74 + (530280737981323/1000000000000000000000000000 : ℝ)*base77 + (64021470982511/312500000000000000000000000 : ℝ)*base78 + (173/1000000000000 : ℝ)*base83 + (87/500000000000 : ℝ)*base85 + (87/500000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p011_b030 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=69 ∨ c=70 := by omega
  rcases hc with rfl|rfl
  · exact collision_c311069 p hpa (by linarith only [hpb]) X hX
  · exact collision_c311070 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
