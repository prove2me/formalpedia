-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:49.24853+00:00
-- url     : https://prove2.me/submissions/a0bb88eb-68db-4dcc-8c11-2251cdea3fe7

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
theorem collision_support_c310026_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1256414489/2500000000 : ℝ)*x 0 + (675164243/2000000000 : ℝ)*x 1 + (-863415103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1256414489/2500000000 : ℝ)^9 ≤ (20643792369783/50000000000000 : ℝ)^7 := by
    have hnat : (1256414489 : ℕ)^9*50000000000000^7 ≤ 20643792369783^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256414489 2500000000 20643792369783 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675164243/2000000000 : ℝ)^9 ≤ (24753163255913/100000000000000 : ℝ)^7 := by
    have hnat : (675164243 : ℕ)^9*100000000000000^7 ≤ 24753163255913^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675164243 2000000000 24753163255913 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863415103/2000000000 : ℝ)^9 ≤ (33959251990219/100000000000000 : ℝ)^7 := by
    have hnat : (863415103 : ℕ)^9*100000000000000^7 ≤ 33959251990219^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863415103 2000000000 33959251990219 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1256414489/2500000000 : ℝ), (675164243/2000000000 : ℝ), (-863415103/2000000000 : ℝ)] ![(20643792369783/50000000000000 : ℝ), (24753163255913/100000000000000 : ℝ), (33959251990219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1256414489/2500000000 : ℝ)|^9 ≤ (20643792369783/50000000000000 : ℝ)^7
        have hw : |(-1256414489/2500000000 : ℝ)|=(1256414489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675164243/2000000000 : ℝ)|^9 ≤ (24753163255913/100000000000000 : ℝ)^7
        have hw : |(675164243/2000000000 : ℝ)|=(675164243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-863415103/2000000000 : ℝ)|^9 ≤ (33959251990219/100000000000000 : ℝ)^7
        have hw : |(-863415103/2000000000 : ℝ)|=(863415103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4427158627/10000000000 : ℝ)*x 0 + (-1301216933/5000000000 : ℝ)*x 1 + (-5577735923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4427158627/10000000000 : ℝ)^9 ≤ (8769159568381/25000000000000 : ℝ)^7 := by
    have hnat : (4427158627 : ℕ)^9*25000000000000^7 ≤ 8769159568381^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427158627 10000000000 8769159568381 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301216933/5000000000 : ℝ)^9 ≤ (17715170272159/100000000000000 : ℝ)^7 := by
    have hnat : (1301216933 : ℕ)^9*100000000000000^7 ≤ 17715170272159^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301216933 5000000000 17715170272159 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5577735923/10000000000 : ℝ)^9 ≤ (23604095718071/50000000000000 : ℝ)^7 := by
    have hnat : (5577735923 : ℕ)^9*50000000000000^7 ≤ 23604095718071^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577735923 10000000000 23604095718071 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4427158627/10000000000 : ℝ), (-1301216933/5000000000 : ℝ), (-5577735923/10000000000 : ℝ)] ![(8769159568381/25000000000000 : ℝ), (17715170272159/100000000000000 : ℝ), (23604095718071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4427158627/10000000000 : ℝ)|^9 ≤ (8769159568381/25000000000000 : ℝ)^7
        have hw : |(4427158627/10000000000 : ℝ)|=(4427158627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1301216933/5000000000 : ℝ)|^9 ≤ (17715170272159/100000000000000 : ℝ)^7
        have hw : |(-1301216933/5000000000 : ℝ)|=(1301216933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5577735923/10000000000 : ℝ)|^9 ≤ (23604095718071/50000000000000 : ℝ)^7
        have hw : |(-5577735923/10000000000 : ℝ)|=(5577735923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (270761313/625000000 : ℝ)*x 0 + (4695211003/10000000000 : ℝ)*x 1 + (1860686971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270761313/625000000 : ℝ)^9 ≤ (34112101726817/100000000000000 : ℝ)^7 := by
    have hnat : (270761313 : ℕ)^9*100000000000000^7 ≤ 34112101726817^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270761313 625000000 34112101726817 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4695211003/10000000000 : ℝ)^9 ≤ (37830518155131/100000000000000 : ℝ)^7 := by
    have hnat : (4695211003 : ℕ)^9*100000000000000^7 ≤ 37830518155131^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4695211003 10000000000 37830518155131 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1860686971/5000000000 : ℝ)^9 ≤ (28057380105361/100000000000000 : ℝ)^7 := by
    have hnat : (1860686971 : ℕ)^9*100000000000000^7 ≤ 28057380105361^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860686971 5000000000 28057380105361 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270761313/625000000 : ℝ), (4695211003/10000000000 : ℝ), (1860686971/5000000000 : ℝ)] ![(34112101726817/100000000000000 : ℝ), (37830518155131/100000000000000 : ℝ), (28057380105361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270761313/625000000 : ℝ)|^9 ≤ (34112101726817/100000000000000 : ℝ)^7
        have hw : |(270761313/625000000 : ℝ)|=(270761313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4695211003/10000000000 : ℝ)|^9 ≤ (37830518155131/100000000000000 : ℝ)^7
        have hw : |(4695211003/10000000000 : ℝ)|=(4695211003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1860686971/5000000000 : ℝ)|^9 ≤ (28057380105361/100000000000000 : ℝ)^7
        have hw : |(1860686971/5000000000 : ℝ)|=(1860686971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-51070631/100000000 : ℝ)*x 0 + (3038120389/10000000000 : ℝ)*x 1 + (-2270203131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51070631/100000000 : ℝ)^9 ≤ (5268677143063/12500000000000 : ℝ)^7 := by
    have hnat : (51070631 : ℕ)^9*12500000000000^7 ≤ 5268677143063^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51070631 100000000 5268677143063 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3038120389/10000000000 : ℝ)^9 ≤ (864644974953/4000000000000 : ℝ)^7 := by
    have hnat : (3038120389 : ℕ)^9*4000000000000^7 ≤ 864644974953^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3038120389 10000000000 864644974953 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270203131/5000000000 : ℝ)^9 ≤ (36234458470353/100000000000000 : ℝ)^7 := by
    have hnat : (2270203131 : ℕ)^9*100000000000000^7 ≤ 36234458470353^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270203131 5000000000 36234458470353 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51070631/100000000 : ℝ), (3038120389/10000000000 : ℝ), (-2270203131/5000000000 : ℝ)] ![(5268677143063/12500000000000 : ℝ), (864644974953/4000000000000 : ℝ), (36234458470353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51070631/100000000 : ℝ)|^9 ≤ (5268677143063/12500000000000 : ℝ)^7
        have hw : |(-51070631/100000000 : ℝ)|=(51070631/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3038120389/10000000000 : ℝ)|^9 ≤ (864644974953/4000000000000 : ℝ)^7
        have hw : |(3038120389/10000000000 : ℝ)|=(3038120389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270203131/5000000000 : ℝ)|^9 ≤ (36234458470353/100000000000000 : ℝ)^7
        have hw : |(-2270203131/5000000000 : ℝ)|=(2270203131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (280358133/625000000 : ℝ)*x 0 + (-2050648323/10000000000 : ℝ)*x 1 + (-1189785261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280358133/625000000 : ℝ)^9 ≤ (7134883600133/20000000000000 : ℝ)^7 := by
    have hnat : (280358133 : ℕ)^9*20000000000000^7 ≤ 7134883600133^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280358133 625000000 7134883600133 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050648323/10000000000 : ℝ)^9 ≤ (652016631237/5000000000000 : ℝ)^7 := by
    have hnat : (2050648323 : ℕ)^9*5000000000000^7 ≤ 652016631237^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050648323 10000000000 652016631237 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1189785261/2000000000 : ℝ)^9 ≤ (25642624680181/50000000000000 : ℝ)^7 := by
    have hnat : (1189785261 : ℕ)^9*50000000000000^7 ≤ 25642624680181^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189785261 2000000000 25642624680181 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280358133/625000000 : ℝ), (-2050648323/10000000000 : ℝ), (-1189785261/2000000000 : ℝ)] ![(7134883600133/20000000000000 : ℝ), (652016631237/5000000000000 : ℝ), (25642624680181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280358133/625000000 : ℝ)|^9 ≤ (7134883600133/20000000000000 : ℝ)^7
        have hw : |(280358133/625000000 : ℝ)|=(280358133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050648323/10000000000 : ℝ)|^9 ≤ (652016631237/5000000000000 : ℝ)^7
        have hw : |(-2050648323/10000000000 : ℝ)|=(2050648323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1189785261/2000000000 : ℝ)|^9 ≤ (25642624680181/50000000000000 : ℝ)^7
        have hw : |(-1189785261/2000000000 : ℝ)|=(1189785261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1979207311/5000000000 : ℝ)*x 0 + (5234940637/10000000000 : ℝ)*x 1 + (219950417/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1979207311/5000000000 : ℝ)^9 ≤ (30375774691617/100000000000000 : ℝ)^7 := by
    have hnat : (1979207311 : ℕ)^9*100000000000000^7 ≤ 30375774691617^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979207311 5000000000 30375774691617 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234940637/10000000000 : ℝ)^9 ≤ (21755588727581/50000000000000 : ℝ)^7 := by
    have hnat : (5234940637 : ℕ)^9*50000000000000^7 ≤ 21755588727581^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234940637 10000000000 21755588727581 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219950417/625000000 : ℝ)^9 ≤ (26113047843071/100000000000000 : ℝ)^7 := by
    have hnat : (219950417 : ℕ)^9*100000000000000^7 ≤ 26113047843071^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219950417 625000000 26113047843071 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1979207311/5000000000 : ℝ), (5234940637/10000000000 : ℝ), (219950417/625000000 : ℝ)] ![(30375774691617/100000000000000 : ℝ), (21755588727581/50000000000000 : ℝ), (26113047843071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1979207311/5000000000 : ℝ)|^9 ≤ (30375774691617/100000000000000 : ℝ)^7
        have hw : |(1979207311/5000000000 : ℝ)|=(1979207311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234940637/10000000000 : ℝ)|^9 ≤ (21755588727581/50000000000000 : ℝ)^7
        have hw : |(5234940637/10000000000 : ℝ)|=(5234940637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219950417/625000000 : ℝ)|^9 ≤ (26113047843071/100000000000000 : ℝ)^7
        have hw : |(219950417/625000000 : ℝ)|=(219950417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (782292381/10000000000 : ℝ)*x 0 + (11595289/12500000 : ℝ)*x 1 + (-259366903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782292381/10000000000 : ℝ)^9 ≤ (3777364057073/100000000000000 : ℝ)^7 := by
    have hnat : (782292381 : ℕ)^9*100000000000000^7 ≤ 3777364057073^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782292381 10000000000 3777364057073 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11595289/12500000 : ℝ)^9 ≤ (90792328480219/100000000000000 : ℝ)^7 := by
    have hnat : (11595289 : ℕ)^9*100000000000000^7 ≤ 90792328480219^7*12500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11595289 12500000 90792328480219 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259366903/2500000000 : ℝ)^9 ≤ (5430307443609/100000000000000 : ℝ)^7 := by
    have hnat : (259366903 : ℕ)^9*100000000000000^7 ≤ 5430307443609^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259366903 2500000000 5430307443609 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(782292381/10000000000 : ℝ), (11595289/12500000 : ℝ), (-259366903/2500000000 : ℝ)] ![(3777364057073/100000000000000 : ℝ), (90792328480219/100000000000000 : ℝ), (5430307443609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(782292381/10000000000 : ℝ)|^9 ≤ (3777364057073/100000000000000 : ℝ)^7
        have hw : |(782292381/10000000000 : ℝ)|=(782292381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11595289/12500000 : ℝ)|^9 ≤ (90792328480219/100000000000000 : ℝ)^7
        have hw : |(11595289/12500000 : ℝ)|=(11595289/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259366903/2500000000 : ℝ)|^9 ≤ (5430307443609/100000000000000 : ℝ)^7
        have hw : |(-259366903/2500000000 : ℝ)|=(259366903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-5283578833/10000000000 : ℝ)*x 0 + (3394546231/10000000000 : ℝ)*x 1 + (-4025427599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283578833/10000000000 : ℝ)^9 ≤ (44031635575691/100000000000000 : ℝ)^7 := by
    have hnat : (5283578833 : ℕ)^9*100000000000000^7 ≤ 44031635575691^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283578833 10000000000 44031635575691 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3394546231/10000000000 : ℝ)^9 ≤ (1558114544723/6250000000000 : ℝ)^7 := by
    have hnat : (3394546231 : ℕ)^9*6250000000000^7 ≤ 1558114544723^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394546231 10000000000 1558114544723 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025427599/10000000000 : ℝ)^9 ≤ (3879816461941/12500000000000 : ℝ)^7 := by
    have hnat : (4025427599 : ℕ)^9*12500000000000^7 ≤ 3879816461941^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025427599 10000000000 3879816461941 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5283578833/10000000000 : ℝ), (3394546231/10000000000 : ℝ), (-4025427599/10000000000 : ℝ)] ![(44031635575691/100000000000000 : ℝ), (1558114544723/6250000000000 : ℝ), (3879816461941/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5283578833/10000000000 : ℝ)|^9 ≤ (44031635575691/100000000000000 : ℝ)^7
        have hw : |(-5283578833/10000000000 : ℝ)|=(5283578833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3394546231/10000000000 : ℝ)|^9 ≤ (1558114544723/6250000000000 : ℝ)^7
        have hw : |(3394546231/10000000000 : ℝ)|=(3394546231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4025427599/10000000000 : ℝ)|^9 ≤ (3879816461941/12500000000000 : ℝ)^7
        have hw : |(-4025427599/10000000000 : ℝ)|=(4025427599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4585566417/10000000000 : ℝ)*x 0 + (-2544001139/10000000000 : ℝ)*x 1 + (-1095053887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4585566417/10000000000 : ℝ)^9 ≤ (18349242147457/50000000000000 : ℝ)^7 := by
    have hnat : (4585566417 : ℕ)^9*50000000000000^7 ≤ 18349242147457^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585566417 10000000000 18349242147457 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544001139/10000000000 : ℝ)^9 ≤ (2150676624531/12500000000000 : ℝ)^7 := by
    have hnat : (2544001139 : ℕ)^9*12500000000000^7 ≤ 2150676624531^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544001139 10000000000 2150676624531 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095053887/2000000000 : ℝ)^9 ≤ (23048051343921/50000000000000 : ℝ)^7 := by
    have hnat : (1095053887 : ℕ)^9*50000000000000^7 ≤ 23048051343921^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095053887 2000000000 23048051343921 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4585566417/10000000000 : ℝ), (-2544001139/10000000000 : ℝ), (-1095053887/2000000000 : ℝ)] ![(18349242147457/50000000000000 : ℝ), (2150676624531/12500000000000 : ℝ), (23048051343921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4585566417/10000000000 : ℝ)|^9 ≤ (18349242147457/50000000000000 : ℝ)^7
        have hw : |(4585566417/10000000000 : ℝ)|=(4585566417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2544001139/10000000000 : ℝ)|^9 ≤ (2150676624531/12500000000000 : ℝ)^7
        have hw : |(-2544001139/10000000000 : ℝ)|=(2544001139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095053887/2000000000 : ℝ)|^9 ≤ (23048051343921/50000000000000 : ℝ)^7
        have hw : |(-1095053887/2000000000 : ℝ)|=(1095053887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1012969979/2500000000 : ℝ)*x 0 + (583799047/1250000000 : ℝ)*x 1 + (1008546219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012969979/2500000000 : ℝ)^9 ≤ (7825254131123/25000000000000 : ℝ)^7 := by
    have hnat : (1012969979 : ℕ)^9*25000000000000^7 ≤ 7825254131123^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012969979 2500000000 7825254131123 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583799047/1250000000 : ℝ)^9 ≤ (9393402053717/25000000000000 : ℝ)^7 := by
    have hnat : (583799047 : ℕ)^9*25000000000000^7 ≤ 9393402053717^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583799047 1250000000 9393402053717 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008546219/2500000000 : ℝ)^9 ≤ (31125375249087/100000000000000 : ℝ)^7 := by
    have hnat : (1008546219 : ℕ)^9*100000000000000^7 ≤ 31125375249087^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008546219 2500000000 31125375249087 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1012969979/2500000000 : ℝ), (583799047/1250000000 : ℝ), (1008546219/2500000000 : ℝ)] ![(7825254131123/25000000000000 : ℝ), (9393402053717/25000000000000 : ℝ), (31125375249087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1012969979/2500000000 : ℝ)|^9 ≤ (7825254131123/25000000000000 : ℝ)^7
        have hw : |(1012969979/2500000000 : ℝ)|=(1012969979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(583799047/1250000000 : ℝ)|^9 ≤ (9393402053717/25000000000000 : ℝ)^7
        have hw : |(583799047/1250000000 : ℝ)|=(583799047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008546219/2500000000 : ℝ)|^9 ≤ (31125375249087/100000000000000 : ℝ)^7
        have hw : |(1008546219/2500000000 : ℝ)|=(1008546219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (616569329/5000000000 : ℝ)*x 0 + (8390553619/10000000000 : ℝ)*x 1 + (-2096497111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (616569329/5000000000 : ℝ)^9 ≤ (3390556884341/50000000000000 : ℝ)^7 := by
    have hnat : (616569329 : ℕ)^9*50000000000000^7 ≤ 3390556884341^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616569329 5000000000 3390556884341 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8390553619/10000000000 : ℝ)^9 ≤ (3192100079297/4000000000000 : ℝ)^7 := by
    have hnat : (8390553619 : ℕ)^9*4000000000000^7 ≤ 3192100079297^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8390553619 10000000000 3192100079297 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096497111/10000000000 : ℝ)^9 ≤ (13416384239503/100000000000000 : ℝ)^7 := by
    have hnat : (2096497111 : ℕ)^9*100000000000000^7 ≤ 13416384239503^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096497111 10000000000 13416384239503 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(616569329/5000000000 : ℝ), (8390553619/10000000000 : ℝ), (-2096497111/10000000000 : ℝ)] ![(3390556884341/50000000000000 : ℝ), (3192100079297/4000000000000 : ℝ), (13416384239503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(616569329/5000000000 : ℝ)|^9 ≤ (3390556884341/50000000000000 : ℝ)^7
        have hw : |(616569329/5000000000 : ℝ)|=(616569329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8390553619/10000000000 : ℝ)|^9 ≤ (3192100079297/4000000000000 : ℝ)^7
        have hw : |(8390553619/10000000000 : ℝ)|=(8390553619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096497111/10000000000 : ℝ)|^9 ≤ (13416384239503/100000000000000 : ℝ)^7
        have hw : |(-2096497111/10000000000 : ℝ)|=(2096497111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-5095504857/10000000000 : ℝ)*x 0 + (3560334287/10000000000 : ℝ)*x 1 + (-4068594131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5095504857/10000000000 : ℝ)^9 ≤ (10506702475251/25000000000000 : ℝ)^7 := by
    have hnat : (5095504857 : ℕ)^9*25000000000000^7 ≤ 10506702475251^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095504857 10000000000 10506702475251 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3560334287/10000000000 : ℝ)^9 ≤ (6626516641477/25000000000000 : ℝ)^7 := by
    have hnat : (3560334287 : ℕ)^9*25000000000000^7 ≤ 6626516641477^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3560334287 10000000000 6626516641477 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4068594131/10000000000 : ℝ)^9 ≤ (31467123522831/100000000000000 : ℝ)^7 := by
    have hnat : (4068594131 : ℕ)^9*100000000000000^7 ≤ 31467123522831^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068594131 10000000000 31467123522831 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5095504857/10000000000 : ℝ), (3560334287/10000000000 : ℝ), (-4068594131/10000000000 : ℝ)] ![(10506702475251/25000000000000 : ℝ), (6626516641477/25000000000000 : ℝ), (31467123522831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5095504857/10000000000 : ℝ)|^9 ≤ (10506702475251/25000000000000 : ℝ)^7
        have hw : |(-5095504857/10000000000 : ℝ)|=(5095504857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3560334287/10000000000 : ℝ)|^9 ≤ (6626516641477/25000000000000 : ℝ)^7
        have hw : |(3560334287/10000000000 : ℝ)|=(3560334287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4068594131/10000000000 : ℝ)|^9 ≤ (31467123522831/100000000000000 : ℝ)^7
        have hw : |(-4068594131/10000000000 : ℝ)|=(4068594131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1089887651/2500000000 : ℝ)*x 0 + (-2433658381/10000000000 : ℝ)*x 1 + (-5774369581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089887651/2500000000 : ℝ)^9 ≤ (3438943753161/10000000000000 : ℝ)^7 := by
    have hnat : (1089887651 : ℕ)^9*10000000000000^7 ≤ 3438943753161^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089887651 2500000000 3438943753161 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2433658381/10000000000 : ℝ)^9 ≤ (8125970170987/50000000000000 : ℝ)^7 := by
    have hnat : (2433658381 : ℕ)^9*50000000000000^7 ≤ 8125970170987^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2433658381 10000000000 8125970170987 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5774369581/10000000000 : ℝ)^9 ≤ (49358622104253/100000000000000 : ℝ)^7 := by
    have hnat : (5774369581 : ℕ)^9*100000000000000^7 ≤ 49358622104253^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5774369581 10000000000 49358622104253 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089887651/2500000000 : ℝ), (-2433658381/10000000000 : ℝ), (-5774369581/10000000000 : ℝ)] ![(3438943753161/10000000000000 : ℝ), (8125970170987/50000000000000 : ℝ), (49358622104253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089887651/2500000000 : ℝ)|^9 ≤ (3438943753161/10000000000000 : ℝ)^7
        have hw : |(1089887651/2500000000 : ℝ)|=(1089887651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2433658381/10000000000 : ℝ)|^9 ≤ (8125970170987/50000000000000 : ℝ)^7
        have hw : |(-2433658381/10000000000 : ℝ)|=(2433658381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5774369581/10000000000 : ℝ)|^9 ≤ (49358622104253/100000000000000 : ℝ)^7
        have hw : |(-5774369581/10000000000 : ℝ)|=(5774369581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (94190179/200000000 : ℝ)*x 0 + (107001031/250000000 : ℝ)*x 1 + (3760389011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94190179/200000000 : ℝ)^9 ≤ (18989349843767/50000000000000 : ℝ)^7 := by
    have hnat : (94190179 : ℕ)^9*50000000000000^7 ≤ 18989349843767^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94190179 200000000 18989349843767 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107001031/250000000 : ℝ)^9 ≤ (33585155928273/100000000000000 : ℝ)^7 := by
    have hnat : (107001031 : ℕ)^9*100000000000000^7 ≤ 33585155928273^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107001031 250000000 33585155928273 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3760389011/10000000000 : ℝ)^9 ≤ (7109036093807/25000000000000 : ℝ)^7 := by
    have hnat : (3760389011 : ℕ)^9*25000000000000^7 ≤ 7109036093807^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760389011 10000000000 7109036093807 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(94190179/200000000 : ℝ), (107001031/250000000 : ℝ), (3760389011/10000000000 : ℝ)] ![(18989349843767/50000000000000 : ℝ), (33585155928273/100000000000000 : ℝ), (7109036093807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(94190179/200000000 : ℝ)|^9 ≤ (18989349843767/50000000000000 : ℝ)^7
        have hw : |(94190179/200000000 : ℝ)|=(94190179/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107001031/250000000 : ℝ)|^9 ≤ (33585155928273/100000000000000 : ℝ)^7
        have hw : |(107001031/250000000 : ℝ)|=(107001031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3760389011/10000000000 : ℝ)|^9 ≤ (7109036093807/25000000000000 : ℝ)^7
        have hw : |(3760389011/10000000000 : ℝ)|=(3760389011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (688616747/10000000000 : ℝ)*x 0 + (9387294269/10000000000 : ℝ)*x 1 + (-456047877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688616747/10000000000 : ℝ)^9 ≤ (32060565239/1000000000000 : ℝ)^7 := by
    have hnat : (688616747 : ℕ)^9*1000000000000^7 ≤ 32060565239^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688616747 10000000000 32060565239 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9387294269/10000000000 : ℝ)^9 ≤ (92192340657069/100000000000000 : ℝ)^7 := by
    have hnat : (9387294269 : ℕ)^9*100000000000000^7 ≤ 92192340657069^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9387294269 10000000000 92192340657069 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456047877/5000000000 : ℝ)^9 ≤ (230080140423/5000000000000 : ℝ)^7 := by
    have hnat : (456047877 : ℕ)^9*5000000000000^7 ≤ 230080140423^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456047877 5000000000 230080140423 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(688616747/10000000000 : ℝ), (9387294269/10000000000 : ℝ), (-456047877/5000000000 : ℝ)] ![(32060565239/1000000000000 : ℝ), (92192340657069/100000000000000 : ℝ), (230080140423/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(688616747/10000000000 : ℝ)|^9 ≤ (32060565239/1000000000000 : ℝ)^7
        have hw : |(688616747/10000000000 : ℝ)|=(688616747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9387294269/10000000000 : ℝ)|^9 ≤ (92192340657069/100000000000000 : ℝ)^7
        have hw : |(9387294269/10000000000 : ℝ)|=(9387294269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456047877/5000000000 : ℝ)|^9 ≤ (230080140423/5000000000000 : ℝ)^7
        have hw : |(-456047877/5000000000 : ℝ)|=(456047877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-4601015391/10000000000 : ℝ)*x 0 + (3713031433/10000000000 : ℝ)*x 1 + (-1108980609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4601015391/10000000000 : ℝ)^9 ≤ (18428762456703/50000000000000 : ℝ)^7 := by
    have hnat : (4601015391 : ℕ)^9*50000000000000^7 ≤ 18428762456703^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601015391 10000000000 18428762456703 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3713031433/10000000000 : ℝ)^9 ≤ (5595307296203/20000000000000 : ℝ)^7 := by
    have hnat : (3713031433 : ℕ)^9*20000000000000^7 ≤ 5595307296203^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713031433 10000000000 5595307296203 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108980609/2500000000 : ℝ)^9 ≤ (1098935580917/3125000000000 : ℝ)^7 := by
    have hnat : (1108980609 : ℕ)^9*3125000000000^7 ≤ 1098935580917^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108980609 2500000000 1098935580917 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4601015391/10000000000 : ℝ), (3713031433/10000000000 : ℝ), (-1108980609/2500000000 : ℝ)] ![(18428762456703/50000000000000 : ℝ), (5595307296203/20000000000000 : ℝ), (1098935580917/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4601015391/10000000000 : ℝ)|^9 ≤ (18428762456703/50000000000000 : ℝ)^7
        have hw : |(-4601015391/10000000000 : ℝ)|=(4601015391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3713031433/10000000000 : ℝ)|^9 ≤ (5595307296203/20000000000000 : ℝ)^7
        have hw : |(3713031433/10000000000 : ℝ)|=(3713031433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108980609/2500000000 : ℝ)|^9 ≤ (1098935580917/3125000000000 : ℝ)^7
        have hw : |(-1108980609/2500000000 : ℝ)|=(1108980609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1116537909/2500000000 : ℝ)*x 0 + (-896120361/2500000000 : ℝ)*x 1 + (-4691127843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116537909/2500000000 : ℝ)^9 ≤ (17737175305503/50000000000000 : ℝ)^7 := by
    have hnat : (1116537909 : ℕ)^9*50000000000000^7 ≤ 17737175305503^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116537909 2500000000 17737175305503 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896120361/2500000000 : ℝ)^9 ≤ (13368712380751/50000000000000 : ℝ)^7 := by
    have hnat : (896120361 : ℕ)^9*50000000000000^7 ≤ 13368712380751^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896120361 2500000000 13368712380751 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4691127843/10000000000 : ℝ)^9 ≤ (9447056152889/25000000000000 : ℝ)^7 := by
    have hnat : (4691127843 : ℕ)^9*25000000000000^7 ≤ 9447056152889^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4691127843 10000000000 9447056152889 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1116537909/2500000000 : ℝ), (-896120361/2500000000 : ℝ), (-4691127843/10000000000 : ℝ)] ![(17737175305503/50000000000000 : ℝ), (13368712380751/50000000000000 : ℝ), (9447056152889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1116537909/2500000000 : ℝ)|^9 ≤ (17737175305503/50000000000000 : ℝ)^7
        have hw : |(1116537909/2500000000 : ℝ)|=(1116537909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-896120361/2500000000 : ℝ)|^9 ≤ (13368712380751/50000000000000 : ℝ)^7
        have hw : |(-896120361/2500000000 : ℝ)|=(896120361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4691127843/10000000000 : ℝ)|^9 ≤ (9447056152889/25000000000000 : ℝ)^7
        have hw : |(-4691127843/10000000000 : ℝ)|=(4691127843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (990599817/2500000000 : ℝ)*x 0 + (1239295713/2500000000 : ℝ)*x 1 + (3820221043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990599817/2500000000 : ℝ)^9 ≤ (30415093715537/100000000000000 : ℝ)^7 := by
    have hnat : (990599817 : ℕ)^9*100000000000000^7 ≤ 30415093715537^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990599817 2500000000 30415093715537 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1239295713/2500000000 : ℝ)^9 ≤ (20282860851969/50000000000000 : ℝ)^7 := by
    have hnat : (1239295713 : ℕ)^9*50000000000000^7 ≤ 20282860851969^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239295713 2500000000 20282860851969 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3820221043/10000000000 : ℝ)^9 ≤ (906849517587/3125000000000 : ℝ)^7 := by
    have hnat : (3820221043 : ℕ)^9*3125000000000^7 ≤ 906849517587^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3820221043 10000000000 906849517587 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(990599817/2500000000 : ℝ), (1239295713/2500000000 : ℝ), (3820221043/10000000000 : ℝ)] ![(30415093715537/100000000000000 : ℝ), (20282860851969/50000000000000 : ℝ), (906849517587/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(990599817/2500000000 : ℝ)|^9 ≤ (30415093715537/100000000000000 : ℝ)^7
        have hw : |(990599817/2500000000 : ℝ)|=(990599817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1239295713/2500000000 : ℝ)|^9 ≤ (20282860851969/50000000000000 : ℝ)^7
        have hw : |(1239295713/2500000000 : ℝ)|=(1239295713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3820221043/10000000000 : ℝ)|^9 ≤ (906849517587/3125000000000 : ℝ)^7
        have hw : |(3820221043/10000000000 : ℝ)|=(3820221043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310026_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3605201507/10000000000 : ℝ)*x 0 + (166099103/312500000 : ℝ)*x 1 + (-3786808543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3605201507/10000000000 : ℝ)^9 ≤ (26936302775137/100000000000000 : ℝ)^7 := by
    have hnat : (3605201507 : ℕ)^9*100000000000000^7 ≤ 26936302775137^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3605201507 10000000000 26936302775137 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166099103/312500000 : ℝ)^9 ≤ (22185214459577/50000000000000 : ℝ)^7 := by
    have hnat : (166099103 : ℕ)^9*50000000000000^7 ≤ 22185214459577^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166099103 312500000 22185214459577 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3786808543/10000000000 : ℝ)^9 ≤ (7173317072567/25000000000000 : ℝ)^7 := by
    have hnat : (3786808543 : ℕ)^9*25000000000000^7 ≤ 7173317072567^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3786808543 10000000000 7173317072567 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3605201507/10000000000 : ℝ), (166099103/312500000 : ℝ), (-3786808543/10000000000 : ℝ)] ![(26936302775137/100000000000000 : ℝ), (22185214459577/50000000000000 : ℝ), (7173317072567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3605201507/10000000000 : ℝ)|^9 ≤ (26936302775137/100000000000000 : ℝ)^7
        have hw : |(3605201507/10000000000 : ℝ)|=(3605201507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166099103/312500000 : ℝ)|^9 ≤ (22185214459577/50000000000000 : ℝ)^7
        have hw : |(166099103/312500000 : ℝ)|=(166099103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3786808543/10000000000 : ℝ)|^9 ≤ (7173317072567/25000000000000 : ℝ)^7
        have hw : |(-3786808543/10000000000 : ℝ)|=(3786808543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310026 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1256414489/2500000000 : ℝ)*X 0 0+(675164243/2000000000 : ℝ)*X 0 1+(-863415103/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4427158627/10000000000 : ℝ)*X 1 0+(-1301216933/5000000000 : ℝ)*X 1 1+(-5577735923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((270761313/625000000 : ℝ)*X 2 0+(4695211003/10000000000 : ℝ)*X 2 1+(1860686971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-51070631/100000000 : ℝ)*X 0 0+(3038120389/10000000000 : ℝ)*X 0 1+(-2270203131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((280358133/625000000 : ℝ)*X 1 0+(-2050648323/10000000000 : ℝ)*X 1 1+(-1189785261/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1979207311/5000000000 : ℝ)*X 2 0+(5234940637/10000000000 : ℝ)*X 2 1+(219950417/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((782292381/10000000000 : ℝ)*X 0 0+(11595289/12500000 : ℝ)*X 0 1+(-259366903/2500000000 : ℝ)*X 0 2+(782292381/10000000000 : ℝ)*X 1 0+(11595289/12500000 : ℝ)*X 1 1+(-259366903/2500000000 : ℝ)*X 1 2+(782292381/10000000000 : ℝ)*X 2 0+(11595289/12500000 : ℝ)*X 2 1+(-259366903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5283578833/10000000000 : ℝ)*X 0 0+(3394546231/10000000000 : ℝ)*X 0 1+(-4025427599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((4585566417/10000000000 : ℝ)*X 1 0+(-2544001139/10000000000 : ℝ)*X 1 1+(-1095053887/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1012969979/2500000000 : ℝ)*X 2 0+(583799047/1250000000 : ℝ)*X 2 1+(1008546219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((616569329/5000000000 : ℝ)*X 0 0+(8390553619/10000000000 : ℝ)*X 0 1+(-2096497111/10000000000 : ℝ)*X 0 2+(616569329/5000000000 : ℝ)*X 1 0+(8390553619/10000000000 : ℝ)*X 1 1+(-2096497111/10000000000 : ℝ)*X 1 2+(616569329/5000000000 : ℝ)*X 2 0+(8390553619/10000000000 : ℝ)*X 2 1+(-2096497111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5095504857/10000000000 : ℝ)*X 0 0+(3560334287/10000000000 : ℝ)*X 0 1+(-4068594131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1089887651/2500000000 : ℝ)*X 1 0+(-2433658381/10000000000 : ℝ)*X 1 1+(-5774369581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((94190179/200000000 : ℝ)*X 2 0+(107001031/250000000 : ℝ)*X 2 1+(3760389011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((688616747/10000000000 : ℝ)*X 0 0+(9387294269/10000000000 : ℝ)*X 0 1+(-456047877/5000000000 : ℝ)*X 0 2+(688616747/10000000000 : ℝ)*X 1 0+(9387294269/10000000000 : ℝ)*X 1 1+(-456047877/5000000000 : ℝ)*X 1 2+(688616747/10000000000 : ℝ)*X 2 0+(9387294269/10000000000 : ℝ)*X 2 1+(-456047877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6313/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6313/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8548395035896105251381/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3102553399591/1000000000000 : ℝ)*(base49) + (1546549783511/1000000000000 : ℝ)*(base50) + (192804627909/200000000000 : ℝ)*(base60) + (1998493549509/250000000000 : ℝ)*(major_s0_0) + (1998493549509/250000000000 : ℝ)*(major_s0_1) + (1998493549509/250000000000 : ℝ)*(major_s0_2) + (70651123/500000000000 : ℝ)*(sp_s0_0) + (11046939512267/1000000000000 : ℝ)*(sp_s0_7) + (5523454073641/500000000000 : ℝ)*(sp_s0_8) + (2209397369207/200000000000 : ℝ)*(sp_s0_9) + (2470411653563/500000000000 : ℝ)*(sp_s0_12) + (93968479/1000000000000 : ℝ)*(sp_s0_15) + (5249357/125000000000 : ℝ)*(sp_s0_19) + (172667231/1000000000000 : ℝ)*(sp_s0_21) + (2470432650991/500000000000 : ℝ)*(f.failure) + (11047080814513/1000000000000 : ℝ)*(f.sum) + (290465714582873/1250000000000000000000000000 : ℝ)*base62 + (652002810968869/2500000000000000000000000000 : ℝ)*base64 + (1649087836281131/2500000000000000000000000000 : ℝ)*base67 + (955304010832873/2500000000000000000000000000 : ℝ)*base68 + (199770826533999/625000000000000000000000000 : ℝ)*base70 + (277854519468869/2500000000000000000000000000 : ℝ)*base72 + (124834489332873/2500000000000000000000000000 : ℝ)*base74 + (632889823417127/2500000000000000000000000000 : ℝ)*base76 + (509915518781131/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (13137/50000000000000000 : ℝ)*base86 + (13137/50000000000000000 : ℝ)*base88 + (13137/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(997/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(997/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27306159878951857110063/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2669803/250000000000 : ℝ)*(base5) + (16979/125000000000 : ℝ)*(base39) + (1042619720519/1000000000000 : ℝ)*(base49) + (154055298489/250000000000 : ℝ)*(base60) + (2601888862701/500000000000 : ℝ)*(major_s0_0) + (2601888862701/500000000000 : ℝ)*(major_s0_1) + (2601888862701/500000000000 : ℝ)*(major_s0_2) + (670207/500000000000 : ℝ)*(sp_s0_2) + (94001959/1000000000000 : ℝ)*(sp_s0_8) + (7191233597569/1000000000000 : ℝ)*(sp_s0_13) + (719113959561/100000000000 : ℝ)*(sp_s0_14) + (7191207650959/1000000000000 : ℝ)*(sp_s0_15) + (3216307533197/1000000000000 : ℝ)*(sp_s0_19) + (1102669/31250000000 : ℝ)*(sp_s0_22) + (3216318212409/1000000000000 : ℝ)*(f.failure) + (7191233597569/1000000000000 : ℝ)*(f.sum) + (90700144446497/2500000000000000000000000000 : ℝ)*base62 + (3431763404591741/5000000000000000000000000000 : ℝ)*base64 + (16911864591741/5000000000000000000000000000 : ℝ)*base66 + (2929596856196497/5000000000000000000000000000 : ℝ)*base68 + (344516982348811/1250000000000000000000000000 : ℝ)*base70 + (3982040642408259/5000000000000000000000000000 : ℝ)*base73 + (2634770973196497/5000000000000000000000000000 : ℝ)*base74 + (3269532862303503/5000000000000000000000000000 : ℝ)*base76 + (561548636841741/2500000000000000000000000000 : ℝ)*base78 + (89337/100000000000000000 : ℝ)*base87 + (89337/100000000000000000 : ℝ)*base89 + (89337/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-11243/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-11243/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6087601823828319056553/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2615119165851/1000000000000 : ℝ)*(base49) + (952055003591/1000000000000 : ℝ)*(base50) + (73310720697/250000000000 : ℝ)*(base60) + (881889751797/125000000000 : ℝ)*(major_s0_0) + (881889751797/125000000000 : ℝ)*(major_s0_1) + (881889751797/125000000000 : ℝ)*(major_s0_2) + (25567247/62500000000 : ℝ)*(sp_s0_1) + (85961571/500000000000 : ℝ)*(sp_s0_2) + (24628491/50000000000 : ℝ)*(sp_s0_12) + (101647147/500000000000 : ℝ)*(sp_s0_13) + (9749446511721/1000000000000 : ℝ)*(sp_s0_20) + (4874620365031/500000000000 : ℝ)*(sp_s0_21) + (1218684735359/125000000000 : ℝ)*(sp_s0_22) + (436009040619/100000000000 : ℝ)*(sp_s0_25) + (436058297601/100000000000 : ℝ)*(f.failure) + (1949929961203/200000000000 : ℝ)*(f.sum) + (402956958868309/625000000000000000000000000 : ℝ)*base62 + (514492575935677/1250000000000000000000000000 : ℝ)*base64 + (609516374935677/1250000000000000000000000000 : ℝ)*base66 + (81094699680809/1250000000000000000000000000 : ℝ)*base68 + (153661244282467/312500000000000000000000000 : ℝ)*base70 + (524424104810677/1250000000000000000000000000 : ℝ)*base72 + (100556722680809/1250000000000000000000000000 : ℝ)*base74 + (490971884930809/1250000000000000000000000000 : ℝ)*base77 + (206562098060677/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1407/10000000000000000 : ℝ)*base86 + (1407/10000000000000000 : ℝ)*base88 + (1407/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (6313/20000 : ℝ) ^ (35/8 : ℝ) ≤ (644206863076615437/100000000000000000000 : ℝ) := by
    have hpowers : (6313/20000 : ℝ)^35 ≤ (644206863076615437/100000000000000000000 : ℝ)^8 := by
      have hnat : (6313 : ℕ)^35*100000000000000000000^8 ≤ 644206863076615437^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6313 20000 644206863076615437 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6313/20000 : ℝ)) (X := (644206863076615437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100644206863076615437/100000000000000000000 : ℝ) ≤ (10014688278883291/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100644206863076615437/100000000000000000000 : ℝ)^8 ≤ (10014688278883291/10000000000000000 : ℝ)^35 := by
      have hnat : (100644206863076615437 : ℕ)^8*10000000000000000^35 ≤ 10014688278883291^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100644206863076615437 100000000000000000000 10014688278883291 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014688278883291/10000000000000000 : ℝ)) (X := (100644206863076615437/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50644206863076615437/50000000000000000000 : ℝ) ≤ (5014652104135377/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50644206863076615437/50000000000000000000 : ℝ)^8 ≤ (5014652104135377/5000000000000000 : ℝ)^35 := by
      have hnat : (50644206863076615437 : ℕ)^8*5000000000000000^35 ≤ 5014652104135377^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50644206863076615437 50000000000000000000 5014652104135377 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014652104135377/5000000000000000 : ℝ)) (X := (50644206863076615437/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14688278883291/3156500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14615929387463/3156500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (6313/20000 : ℝ)) (alpha := (14688278883291/3156500000000000 : ℝ)) (beta := (14615929387463/3156500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6313/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14688278883291/3156500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14615929387463/3156500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (997/25000 : ℝ) ^ (35/8 : ℝ) ≤ (75562058324513/100000000000000000000 : ℝ) := by
    have hpowers : (997/25000 : ℝ)^35 ≤ (75562058324513/100000000000000000000 : ℝ)^8 := by
      have hnat : (997 : ℕ)^35*100000000000000000000^8 ≤ 75562058324513^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        997 25000 75562058324513 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (997/25000 : ℝ)) (X := (75562058324513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000075562058324513/100000000000000000000 : ℝ) ≤ (10000001727132259/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100000075562058324513/100000000000000000000 : ℝ)^8 ≤ (10000001727132259/10000000000000000 : ℝ)^35 := by
      have hnat : (100000075562058324513 : ℕ)^8*10000000000000000^35 ≤ 10000001727132259^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000075562058324513 100000000000000000000 10000001727132259 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001727132259/10000000000000000 : ℝ)) (X := (100000075562058324513/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000075562058324513/50000000000000000000 : ℝ) ≤ (1000000345426351/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50000075562058324513/50000000000000000000 : ℝ)^8 ≤ (1000000345426351/1000000000000000 : ℝ)^35 := by
      have hnat : (50000075562058324513 : ℕ)^8*1000000000000000^35 ≤ 1000000345426351^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000075562058324513 50000000000000000000 1000000345426351 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000345426351/1000000000000000 : ℝ)) (X := (50000075562058324513/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1727132259/398800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1727131251/398800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (997/25000 : ℝ)) (alpha := (1727132259/398800000000000 : ℝ)) (beta := (1727131251/398800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (997/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1727132259/398800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1727131251/398800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11243/50000 : ℝ) ^ (35/8 : ℝ) ≤ (36522114303838461/25000000000000000000 : ℝ) := by
    have hpowers : (11243/50000 : ℝ)^35 ≤ (36522114303838461/25000000000000000000 : ℝ)^8 := by
      have hnat : (11243 : ℕ)^35*25000000000000000000^8 ≤ 36522114303838461^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 50000 36522114303838461 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/50000 : ℝ)) (X := (36522114303838461/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25036522114303838461/25000000000000000000 : ℝ) ≤ (2500834321197929/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25036522114303838461/25000000000000000000 : ℝ)^8 ≤ (2500834321197929/2500000000000000 : ℝ)^35 := by
      have hnat : (25036522114303838461 : ℕ)^8*2500000000000000^35 ≤ 2500834321197929^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036522114303838461 25000000000000000000 2500834321197929 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500834321197929/2500000000000000 : ℝ)) (X := (25036522114303838461/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12536522114303838461/12500000000000000000 : ℝ) ≤ (10006670816166783/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (12536522114303838461/12500000000000000000 : ℝ)^8 ≤ (10006670816166783/10000000000000000 : ℝ)^35 := by
      have hnat : (12536522114303838461 : ℕ)^8*10000000000000000^35 ≤ 10006670816166783^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12536522114303838461 12500000000000000000 10006670816166783 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006670816166783/10000000000000000 : ℝ)) (X := (12536522114303838461/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(834321197929/562150000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3333531375067/2248600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (11243/50000 : ℝ)) (alpha := (834321197929/562150000000000 : ℝ)) (beta := (3333531375067/2248600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (11243/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(834321197929/562150000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3333531375067/2248600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4601015391/10000000000 : ℝ)*X 0 0+(3713031433/10000000000 : ℝ)*X 0 1+(-1108980609/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1116537909/2500000000 : ℝ)*X 1 0+(-896120361/2500000000 : ℝ)*X 1 1+(-4691127843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((990599817/2500000000 : ℝ)*X 2 0+(1239295713/2500000000 : ℝ)*X 2 1+(3820221043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3605201507/10000000000 : ℝ)*X 0 0+(166099103/312500000 : ℝ)*X 0 1+(-3786808543/10000000000 : ℝ)*X 0 2+(3605201507/10000000000 : ℝ)*X 1 0+(166099103/312500000 : ℝ)*X 1 1+(-3786808543/10000000000 : ℝ)*X 1 2+(3605201507/10000000000 : ℝ)*X 2 0+(166099103/312500000 : ℝ)*X 2 1+(-3786808543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310026_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-1174731152324106513647437927839/177442647500000000000000000000 : ℝ) := by norm_num
    linear_combination (3201/1000000000000 : ℝ)*(base1) + (69921/1000000000000 : ℝ)*(base5) + (27/1600000000 : ℝ)*(base8) + (6691/500000000000 : ℝ)*(base18) + (98264159867/500000000000 : ℝ)*(base39) + (128663878991/200000000000 : ℝ)*(base49) + (2992094739/7812500000 : ℝ)*(base50) + (269426786429/1000000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2206780916903/1000000000000 : ℝ)*(sp_s1_0) + (441356183439/200000000000 : ℝ)*(sp_s1_1) + (2206781000499/1000000000000 : ℝ)*(sp_s1_2) + (499999963439/500000000000 : ℝ)*(sp_s1_6) + (2206780930577/1000000000000 : ℝ)*(f.sum) + (939955289352217/112092710000000000000000000000 : ℝ)*base63 + (37767014187541/112430000000000000000000000 : ℝ)*base64 + (1602675024307/4985000000000000000000000 : ℝ)*base67 + (18475171032169/56215000000000000000000000 : ℝ)*base68 + (109029655306752543/177442647500000000000000000000 : ℝ)*base70 + (17913529795493/63130000000000000000000000 : ℝ)*base72 + (226867354183/4985000000000000000000000 : ℝ)*base74 + (6398417577067/15782500000000000000000000 : ℝ)*base76 + (4361044161815883/62940610000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b014 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 26 ≤ c.val) (hhi : c.val < 27)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=26 := by omega
  rcases hc with rfl
  · exact collision_c310026 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 26 ≤ c.val) (hhi : c.val < 27)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b014 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
