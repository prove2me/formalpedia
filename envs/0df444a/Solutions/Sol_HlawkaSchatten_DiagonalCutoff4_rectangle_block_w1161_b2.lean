-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:19.009656+00:00
-- url     : https://prove2.me/submissions/75c5d60e-be73-4fd3-aaef-fc49af698e10

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1161_s6_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215780363/1000000000 : ℝ)*x 0 + (5393003661/10000000000 : ℝ)*x 1 + (263287339/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215780363/1000000000 : ℝ)^4177 ≤ (13113509351187/100000000000000 : ℝ)^3153 := by
    have hnat : (215780363 : ℕ)^4177*100000000000000^3153 ≤ 13113509351187^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215780363 1000000000 13113509351187 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393003661/10000000000 : ℝ)^4177 ≤ (22065174411597/50000000000000 : ℝ)^3153 := by
    have hnat : (5393003661 : ℕ)^4177*50000000000000^3153 ≤ 22065174411597^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393003661 10000000000 22065174411597 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263287339/500000000 : ℝ)^4177 ≤ (42756141807343/100000000000000 : ℝ)^3153 := by
    have hnat : (263287339 : ℕ)^4177*100000000000000^3153 ≤ 42756141807343^3153*500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263287339 500000000 42756141807343 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215780363/1000000000 : ℝ), (5393003661/10000000000 : ℝ), (263287339/500000000 : ℝ)] ![(13113509351187/100000000000000 : ℝ), (22065174411597/50000000000000 : ℝ), (42756141807343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215780363/1000000000 : ℝ)|^4177 ≤ (13113509351187/100000000000000 : ℝ)^3153
        have hw : |(-215780363/1000000000 : ℝ)|=(215780363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393003661/10000000000 : ℝ)|^4177 ≤ (22065174411597/50000000000000 : ℝ)^3153
        have hw : |(5393003661/10000000000 : ℝ)|=(5393003661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263287339/500000000 : ℝ)|^4177 ≤ (42756141807343/100000000000000 : ℝ)^3153
        have hw : |(263287339/500000000 : ℝ)|=(263287339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344764901/10000000000 : ℝ)*x 0 + (-1111175069/5000000000 : ℝ)*x 1 + (5265746779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344764901/10000000000 : ℝ)^4177 ≤ (2180409011657/5000000000000 : ℝ)^3153 := by
    have hnat : (5344764901 : ℕ)^4177*5000000000000^3153 ≤ 2180409011657^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344764901 10000000000 2180409011657 5000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111175069/5000000000 : ℝ)^4177 ≤ (1704459744449/12500000000000 : ℝ)^3153 := by
    have hnat : (1111175069 : ℕ)^4177*12500000000000^3153 ≤ 1704459744449^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111175069 5000000000 1704459744449 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265746779/10000000000 : ℝ)^4177 ≤ (21378070898293/50000000000000 : ℝ)^3153 := by
    have hnat : (5265746779 : ℕ)^4177*50000000000000^3153 ≤ 21378070898293^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265746779 10000000000 21378070898293 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344764901/10000000000 : ℝ), (-1111175069/5000000000 : ℝ), (5265746779/10000000000 : ℝ)] ![(2180409011657/5000000000000 : ℝ), (1704459744449/12500000000000 : ℝ), (21378070898293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344764901/10000000000 : ℝ)|^4177 ≤ (2180409011657/5000000000000 : ℝ)^3153
        have hw : |(5344764901/10000000000 : ℝ)|=(5344764901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111175069/5000000000 : ℝ)|^4177 ≤ (1704459744449/12500000000000 : ℝ)^3153
        have hw : |(-1111175069/5000000000 : ℝ)|=(1111175069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265746779/10000000000 : ℝ)|^4177 ≤ (21378070898293/50000000000000 : ℝ)^3153
        have hw : |(5265746779/10000000000 : ℝ)|=(5265746779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53447649/100000000 : ℝ)*x 0 + (263287339/500000000 : ℝ)*x 1 + (-1111175069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53447649/100000000 : ℝ)^4177 ≤ (43608180222331/100000000000000 : ℝ)^3153 := by
    have hnat : (53447649 : ℕ)^4177*100000000000000^3153 ≤ 43608180222331^3153*100000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53447649 100000000 43608180222331 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263287339/500000000 : ℝ)^4177 ≤ (42756141807343/100000000000000 : ℝ)^3153 := by
    have hnat : (263287339 : ℕ)^4177*100000000000000^3153 ≤ 42756141807343^3153*500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263287339 500000000 42756141807343 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111175069/5000000000 : ℝ)^4177 ≤ (1704459744449/12500000000000 : ℝ)^3153 := by
    have hnat : (1111175069 : ℕ)^4177*12500000000000^3153 ≤ 1704459744449^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111175069 5000000000 1704459744449 12500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53447649/100000000 : ℝ), (263287339/500000000 : ℝ), (-1111175069/5000000000 : ℝ)] ![(43608180222331/100000000000000 : ℝ), (42756141807343/100000000000000 : ℝ), (1704459744449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53447649/100000000 : ℝ)|^4177 ≤ (43608180222331/100000000000000 : ℝ)^3153
        have hw : |(53447649/100000000 : ℝ)|=(53447649/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263287339/500000000 : ℝ)|^4177 ≤ (42756141807343/100000000000000 : ℝ)^3153
        have hw : |(263287339/500000000 : ℝ)|=(263287339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111175069/5000000000 : ℝ)|^4177 ≤ (1704459744449/12500000000000 : ℝ)^3153
        have hw : |(-1111175069/5000000000 : ℝ)|=(1111175069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361987823/10000000000 : ℝ)*x 0 + (1059190509/2500000000 : ℝ)*x 1 + (2245440087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361987823/10000000000 : ℝ)^4177 ≤ (33316912297281/100000000000000 : ℝ)^3153 := by
    have hnat : (4361987823 : ℕ)^4177*100000000000000^3153 ≤ 33316912297281^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361987823 10000000000 33316912297281 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059190509/2500000000 : ℝ)^4177 ≤ (16027873617369/50000000000000 : ℝ)^3153 := by
    have hnat : (1059190509 : ℕ)^4177*50000000000000^3153 ≤ 16027873617369^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059190509 2500000000 16027873617369 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245440087/5000000000 : ℝ)^4177 ≤ (173136702313/500000000000 : ℝ)^3153 := by
    have hnat : (2245440087 : ℕ)^4177*500000000000^3153 ≤ 173136702313^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245440087 5000000000 173136702313 500000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361987823/10000000000 : ℝ), (1059190509/2500000000 : ℝ), (2245440087/5000000000 : ℝ)] ![(33316912297281/100000000000000 : ℝ), (16027873617369/50000000000000 : ℝ), (173136702313/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361987823/10000000000 : ℝ)|^4177 ≤ (33316912297281/100000000000000 : ℝ)^3153
        have hw : |(4361987823/10000000000 : ℝ)|=(4361987823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059190509/2500000000 : ℝ)|^4177 ≤ (16027873617369/50000000000000 : ℝ)^3153
        have hw : |(1059190509/2500000000 : ℝ)|=(1059190509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245440087/5000000000 : ℝ)|^4177 ≤ (173136702313/500000000000 : ℝ)^3153
        have hw : |(2245440087/5000000000 : ℝ)|=(2245440087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431561711/2000000000 : ℝ)*x 0 + (1053213639/2000000000 : ℝ)*x 1 + (1078536213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431561711/2000000000 : ℝ)^4177 ≤ (6556774501083/50000000000000 : ℝ)^3153 := by
    have hnat : (431561711 : ℕ)^4177*50000000000000^3153 ≤ 6556774501083^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431561711 2000000000 6556774501083 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053213639/2000000000 : ℝ)^4177 ≤ (4275959920623/10000000000000 : ℝ)^3153 := by
    have hnat : (1053213639 : ℕ)^4177*10000000000000^3153 ≤ 4275959920623^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053213639 2000000000 4275959920623 10000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078536213/2000000000 : ℝ)^4177 ≤ (44126851772651/100000000000000 : ℝ)^3153 := by
    have hnat : (1078536213 : ℕ)^4177*100000000000000^3153 ≤ 44126851772651^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078536213 2000000000 44126851772651 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431561711/2000000000 : ℝ), (1053213639/2000000000 : ℝ), (1078536213/2000000000 : ℝ)] ![(6556774501083/50000000000000 : ℝ), (4275959920623/10000000000000 : ℝ), (44126851772651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431561711/2000000000 : ℝ)|^4177 ≤ (6556774501083/50000000000000 : ℝ)^3153
        have hw : |(-431561711/2000000000 : ℝ)|=(431561711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053213639/2000000000 : ℝ)|^4177 ≤ (4275959920623/10000000000000 : ℝ)^3153
        have hw : |(1053213639/2000000000 : ℝ)|=(1053213639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078536213/2000000000 : ℝ)|^4177 ≤ (44126851772651/100000000000000 : ℝ)^3153
        have hw : |(1078536213/2000000000 : ℝ)|=(1078536213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312478753/10000000000 : ℝ)*x 0 + (-2095415907/10000000000 : ℝ)*x 1 + (1348170253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312478753/10000000000 : ℝ)^4177 ≤ (10814886647043/25000000000000 : ℝ)^3153 := by
    have hnat : (5312478753 : ℕ)^4177*25000000000000^3153 ≤ 10814886647043^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312478753 10000000000 10814886647043 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095415907/10000000000 : ℝ)^4177 ≤ (630680109847/5000000000000 : ℝ)^3153 := by
    have hnat : (2095415907 : ℕ)^4177*5000000000000^3153 ≤ 630680109847^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095415907 10000000000 630680109847 5000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348170253/2500000000 : ℝ)^4177 ≤ (44126851198119/100000000000000 : ℝ)^3153 := by
    have hnat : (1348170253 : ℕ)^4177*100000000000000^3153 ≤ 44126851198119^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348170253 2500000000 44126851198119 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312478753/10000000000 : ℝ), (-2095415907/10000000000 : ℝ), (1348170253/2500000000 : ℝ)] ![(10814886647043/25000000000000 : ℝ), (630680109847/5000000000000 : ℝ), (44126851198119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312478753/10000000000 : ℝ)|^4177 ≤ (10814886647043/25000000000000 : ℝ)^3153
        have hw : |(5312478753/10000000000 : ℝ)|=(5312478753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095415907/10000000000 : ℝ)|^4177 ≤ (630680109847/5000000000000 : ℝ)^3153
        have hw : |(-2095415907/10000000000 : ℝ)|=(2095415907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348170253/2500000000 : ℝ)|^4177 ≤ (44126851198119/100000000000000 : ℝ)^3153
        have hw : |(1348170253/2500000000 : ℝ)|=(1348170253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328119693/2500000000 : ℝ)*x 0 + (5392680961/10000000000 : ℝ)*x 1 + (-2095415951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328119693/2500000000 : ℝ)^4177 ≤ (2703721674571/6250000000000 : ℝ)^3153 := by
    have hnat : (1328119693 : ℕ)^4177*6250000000000^3153 ≤ 2703721674571^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328119693 2500000000 2703721674571 6250000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392680961/10000000000 : ℝ)^4177 ≤ (44126850645267/100000000000000 : ℝ)^3153 := by
    have hnat : (5392680961 : ℕ)^4177*100000000000000^3153 ≤ 44126850645267^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392680961 10000000000 44126850645267 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095415951/10000000000 : ℝ)^4177 ≤ (12613602547823/100000000000000 : ℝ)^3153 := by
    have hnat : (2095415951 : ℕ)^4177*100000000000000^3153 ≤ 12613602547823^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095415951 10000000000 12613602547823 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328119693/2500000000 : ℝ), (5392680961/10000000000 : ℝ), (-2095415951/10000000000 : ℝ)] ![(2703721674571/6250000000000 : ℝ), (44126850645267/100000000000000 : ℝ), (12613602547823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328119693/2500000000 : ℝ)|^4177 ≤ (2703721674571/6250000000000 : ℝ)^3153
        have hw : |(1328119693/2500000000 : ℝ)|=(1328119693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392680961/10000000000 : ℝ)|^4177 ≤ (44126850645267/100000000000000 : ℝ)^3153
        have hw : |(5392680961/10000000000 : ℝ)|=(5392680961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095415951/10000000000 : ℝ)|^4177 ≤ (12613602547823/100000000000000 : ℝ)^3153
        have hw : |(-2095415951/10000000000 : ℝ)|=(2095415951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s6_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2180998773/5000000000 : ℝ)*x 0 + (1122559573/2500000000 : ℝ)*x 1 + (423740633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180998773/5000000000 : ℝ)^4177 ≤ (33317010680549/100000000000000 : ℝ)^3153 := by
    have hnat : (2180998773 : ℕ)^4177*100000000000000^3153 ≤ 33317010680549^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180998773 5000000000 33317010680549 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122559573/2500000000 : ℝ)^4177 ≤ (34620783944099/100000000000000 : ℝ)^3153 := by
    have hnat : (1122559573 : ℕ)^4177*100000000000000^3153 ≤ 34620783944099^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122559573 2500000000 34620783944099 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423740633/1000000000 : ℝ)^4177 ≤ (500971958909/1562500000000 : ℝ)^3153 := by
    have hnat : (423740633 : ℕ)^4177*1562500000000^3153 ≤ 500971958909^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423740633 1000000000 500971958909 1562500000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180998773/5000000000 : ℝ), (1122559573/2500000000 : ℝ), (423740633/1000000000 : ℝ)] ![(33317010680549/100000000000000 : ℝ), (34620783944099/100000000000000 : ℝ), (500971958909/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180998773/5000000000 : ℝ)|^4177 ≤ (33317010680549/100000000000000 : ℝ)^3153
        have hw : |(2180998773/5000000000 : ℝ)|=(2180998773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122559573/2500000000 : ℝ)|^4177 ≤ (34620783944099/100000000000000 : ℝ)^3153
        have hw : |(1122559573/2500000000 : ℝ)|=(1122559573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423740633/1000000000 : ℝ)|^4177 ≤ (500971958909/1562500000000 : ℝ)^3153
        have hw : |(423740633/1000000000 : ℝ)|=(423740633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11343/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (6975426930667083/50000000000000000000 : ℝ) := by
    have hpowers : (11343/100000 : ℝ)^8353 ≤ (6975426930667083/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11343 : ℕ)^8353*50000000000000000000^2048 ≤ 6975426930667083^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11343 100000 6975426930667083 50000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11343/100000 : ℝ)) (X := (6975426930667083/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (3385453530180599/10000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^8353 ≤ (3385453530180599/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14097 : ℕ)^8353*10000000000000000000^2048 ≤ 3385453530180599^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 3385453530180599 10000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (3385453530180599/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006975426930667083/25000000000000000000 : ℝ) ≤ (10000684025871707/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25006975426930667083/25000000000000000000 : ℝ)^2048 ≤ (10000684025871707/10000000000000000 : ℝ)^8353 := by
      have hnat : (25006975426930667083 : ℕ)^2048*10000000000000000^8353 ≤ 10000684025871707^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006975426930667083 25000000000000000000 10000684025871707 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000684025871707/10000000000000000 : ℝ)) (X := (25006975426930667083/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011951347290785039/25000000000000000000 : ℝ) ≤ (2500292971919221/2500000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25011951347290785039/25000000000000000000 : ℝ)^2048 ≤ (2500292971919221/2500000000000000 : ℝ)^8353 := by
      have hnat : (25011951347290785039 : ℕ)^2048*2500000000000000^8353 ≤ 2500292971919221^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011951347290785039 25000000000000000000 2500292971919221 2500000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500292971919221/2500000000000000 : ℝ)) (X := (25011951347290785039/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003385453530180599/5000000000000000000 : ℝ) ≤ (10001659749482061/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (5003385453530180599/5000000000000000000 : ℝ)^2048 ≤ (10001659749482061/10000000000000000 : ℝ)^8353 := by
      have hnat : (5003385453530180599 : ℕ)^2048*10000000000000000^8353 ≤ 10001659749482061^8353*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003385453530180599 5000000000000000000 10001659749482061 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001659749482061/10000000000000000 : ℝ)) (X := (5003385453530180599/5000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6975426930667083/50000000000000000000 : ℝ) ≤ ((1147117340597434819/1147500000000000000 : ℝ)+2*(487861805177/275400000000000 : ℝ)*(11343/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (1147117340597434819/1147500000000000000 : ℝ)+2*(487861805177/275400000000000 : ℝ)*(11343/100000 : ℝ)=(10000684025871707/10000000000000000 : ℝ) by norm_num, show 1+2*(6975426930667083/50000000000000000000 : ℝ)=(25006975426930667083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3385453530180599/10000000000000000000 : ℝ)+(6975426930667083/50000000000000000000 : ℝ) ≤ ((1147117340597434819/1147500000000000000 : ℝ)+(487861805177/275400000000000 : ℝ)*((14097/100000 : ℝ)+(11343/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (1147117340597434819/1147500000000000000 : ℝ)+(487861805177/275400000000000 : ℝ)*((14097/100000 : ℝ)+(11343/100000 : ℝ))=(2500292971919221/2500000000000000 : ℝ) by norm_num, show 1+(3385453530180599/10000000000000000000 : ℝ)+(6975426930667083/50000000000000000000 : ℝ)=(25011951347290785039/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3385453530180599/10000000000000000000 : ℝ) ≤ ((1147117340597434819/1147500000000000000 : ℝ)+2*(487861805177/275400000000000 : ℝ)*(14097/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (1147117340597434819/1147500000000000000 : ℝ)+2*(487861805177/275400000000000 : ℝ)*(14097/100000 : ℝ)=(10001659749482061/10000000000000000 : ℝ) by norm_num, show 1+2*(3385453530180599/10000000000000000000 : ℝ)=(5003385453530180599/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1147117340597434819/1147500000000000000 : ℝ)*(X 1 0+X 2 0)+(487861805177/275400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (1147117340597434819/1147500000000000000 : ℝ)) (alpha := (487861805177/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1147117340597434819/1147500000000000000 : ℝ)*(X 0 1+X 2 1)+(487861805177/275400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (1147117340597434819/1147500000000000000 : ℝ)) (alpha := (487861805177/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1147117340597434819/1147500000000000000 : ℝ)*(X 0 2+X 1 2)+(487861805177/275400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (1147117340597434819/1147500000000000000 : ℝ)) (alpha := (487861805177/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215780363/1000000000 : ℝ)*X 0 0+(5393003661/10000000000 : ℝ)*X 0 1+(263287339/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344764901/10000000000 : ℝ)*X 1 0+(-1111175069/5000000000 : ℝ)*X 1 1+(5265746779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53447649/100000000 : ℝ)*X 2 0+(263287339/500000000 : ℝ)*X 2 1+(-1111175069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361987823/10000000000 : ℝ)*X 0 0+(1059190509/2500000000 : ℝ)*X 0 1+(2245440087/5000000000 : ℝ)*X 0 2+(4361987823/10000000000 : ℝ)*X 1 0+(1059190509/2500000000 : ℝ)*X 1 1+(2245440087/5000000000 : ℝ)*X 1 2+(4361987823/10000000000 : ℝ)*X 2 0+(1059190509/2500000000 : ℝ)*X 2 1+(2245440087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431561711/2000000000 : ℝ)*X 0 0+(1053213639/2000000000 : ℝ)*X 0 1+(1078536213/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312478753/10000000000 : ℝ)*X 1 0+(-2095415907/10000000000 : ℝ)*X 1 1+(1348170253/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328119693/2500000000 : ℝ)*X 2 0+(5392680961/10000000000 : ℝ)*X 2 1+(-2095415951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180998773/5000000000 : ℝ)*X 0 0+(1122559573/2500000000 : ℝ)*X 0 1+(423740633/1000000000 : ℝ)*X 0 2+(2180998773/5000000000 : ℝ)*X 1 0+(1122559573/2500000000 : ℝ)*X 1 1+(423740633/1000000000 : ℝ)*X 1 2+(2180998773/5000000000 : ℝ)*X 2 0+(1122559573/2500000000 : ℝ)*X 2 1+(423740633/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8311100648166980096189/918000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444959263/25000000000000 : ℝ)*(base19) + (1655925389/100000000000000 : ℝ)*(base23) + (65442047/100000000000000 : ℝ)*(lower2) + (45598687/20000000000000 : ℝ)*(upper3) + (17150403/12500000000000 : ℝ)*(upper5) + (1179344798238497/20000000000000 : ℝ)*(major0) + (1179344798238497/20000000000000 : ℝ)*(major1) + (1179344798238497/20000000000000 : ℝ)*(major2) + (7858171944309989/100000000000000 : ℝ)*(sp0) + (3929109261703531/50000000000000 : ℝ)*(sp1) + (314328745892749/4000000000000 : ℝ)*(sp2) + (1967600584561003/50000000000000 : ℝ)*(sp3) + (24179467063/50000000000000 : ℝ)*(sp4) + (13104117979/50000000000000 : ℝ)*(sp7) + (983806844339491/25000000000000 : ℝ)*(f.failure) + (3929110151622057/50000000000000 : ℝ)*(f.sum) + (1525429810711/550800000000000000000000000 : ℝ)*base66 + (554861193122156371/68850000000000000000000000000000 : ℝ)*base68 + (70945887292293629/68850000000000000000000000000000 : ℝ)*base69 + (17718459302606371/68850000000000000000000000000000 : ℝ)*base72 + (289230697277/550800000000000000000000000 : ℝ)*base73 + (479140759373493629/68850000000000000000000000000000 : ℝ)*base75 + (1296925409078906371/68850000000000000000000000000000 : ℝ)*base78 + (961362925488993629/68850000000000000000000000000000 : ℝ)*base79 + (6756978823933/2754000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4290249/625000000000000000000 : ℝ)*base89 + (4290249/625000000000000000000 : ℝ)*base91 + (4290249/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11500433281986644447753/1530000000000000000000000000 : ℝ) := by norm_num
    linear_combination (694458579/50000000000000 : ℝ)*(base19) + (705555511/50000000000000 : ℝ)*(base23) + (5816693/5000000000000 : ℝ)*(upper3) + (5106443/50000000000000 : ℝ)*(lower4) + (8393859/5000000000000 : ℝ)*(upper5) + (5926644384144709/100000000000000 : ℝ)*(major0) + (5926644384144709/100000000000000 : ℝ)*(major1) + (5926644384144709/100000000000000 : ℝ)*(major2) + (37950730377/100000000000000 : ℝ)*(sp1) + (33791438707/100000000000000 : ℝ)*(sp2) + (394904675971503/5000000000000 : ℝ)*(sp4) + (315922167191301/4000000000000 : ℝ)*(sp5) + (7898058316880331/100000000000000 : ℝ)*(sp6) + (15820779993221/400000000000 : ℝ)*(sp7) + (15820779993221/400000000000 : ℝ)*(f.failure) + (394904675971503/5000000000000 : ℝ)*(f.sum) + (56697258205507/13770000000000000000000000000 : ℝ)*base66 + (2284801161420169487/344250000000000000000000000000000 : ℝ)*base68 + (912714194145169487/344250000000000000000000000000000 : ℝ)*base70 + (2024991684991330513/344250000000000000000000000000000 : ℝ)*base71 + (125210066693737/13770000000000000000000000000 : ℝ)*base74 + (3876386092532080513/344250000000000000000000000000000 : ℝ)*base75 + (3109541385263830513/344250000000000000000000000000000 : ℝ)*base77 + (687050797626919487/344250000000000000000000000000000 : ℝ)*base80 + (74597266118317/13770000000000000000000000000 : ℝ)*base82 + (38719/10000000000000000000 : ℝ)*base89 + (38719/10000000000000000000 : ℝ)*base91 + (38719/10000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1161_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_s7_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157830923/10000000000 : ℝ)*x 0 + (5392711253/10000000000 : ℝ)*x 1 + (658252629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157830923/10000000000 : ℝ)^4177 ≤ (3278432271603/25000000000000 : ℝ)^3153 := by
    have hnat : (2157830923 : ℕ)^4177*25000000000000^3153 ≤ 3278432271603^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157830923 10000000000 3278432271603 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392711253/10000000000 : ℝ)^4177 ≤ (22063589508987/50000000000000 : ℝ)^3153 := by
    have hnat : (5392711253 : ℕ)^4177*50000000000000^3153 ≤ 22063589508987^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392711253 10000000000 22063589508987 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658252629/1250000000 : ℝ)^4177 ≤ (8551818375737/20000000000000 : ℝ)^3153 := by
    have hnat : (658252629 : ℕ)^4177*20000000000000^3153 ≤ 8551818375737^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658252629 1250000000 8551818375737 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157830923/10000000000 : ℝ), (5392711253/10000000000 : ℝ), (658252629/1250000000 : ℝ)] ![(3278432271603/25000000000000 : ℝ), (22063589508987/50000000000000 : ℝ), (8551818375737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157830923/10000000000 : ℝ)|^4177 ≤ (3278432271603/25000000000000 : ℝ)^3153
        have hw : |(-2157830923/10000000000 : ℝ)|=(2157830923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392711253/10000000000 : ℝ)|^4177 ≤ (22063589508987/50000000000000 : ℝ)^3153
        have hw : |(5392711253/10000000000 : ℝ)|=(5392711253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658252629/1250000000 : ℝ)|^4177 ≤ (8551818375737/20000000000000 : ℝ)^3153
        have hw : |(658252629/1250000000 : ℝ)|=(658252629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672345319/5000000000 : ℝ)*x 0 + (-1111042973/5000000000 : ℝ)*x 1 + (1053204207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672345319/5000000000 : ℝ)^4177 ≤ (43607377536637/100000000000000 : ℝ)^3153 := by
    have hnat : (2672345319 : ℕ)^4177*100000000000000^3153 ≤ 43607377536637^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672345319 5000000000 43607377536637 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111042973/5000000000 : ℝ)^4177 ≤ (2726706108067/20000000000000 : ℝ)^3153 := by
    have hnat : (1111042973 : ℕ)^4177*20000000000000^3153 ≤ 2726706108067^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111042973 5000000000 2726706108067 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053204207/2000000000 : ℝ)^4177 ≤ (10689772977739/25000000000000 : ℝ)^3153 := by
    have hnat : (1053204207 : ℕ)^4177*25000000000000^3153 ≤ 10689772977739^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053204207 2000000000 10689772977739 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672345319/5000000000 : ℝ), (-1111042973/5000000000 : ℝ), (1053204207/2000000000 : ℝ)] ![(43607377536637/100000000000000 : ℝ), (2726706108067/20000000000000 : ℝ), (10689772977739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672345319/5000000000 : ℝ)|^4177 ≤ (43607377536637/100000000000000 : ℝ)^3153
        have hw : |(2672345319/5000000000 : ℝ)|=(2672345319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111042973/5000000000 : ℝ)|^4177 ≤ (2726706108067/20000000000000 : ℝ)^3153
        have hw : |(-1111042973/5000000000 : ℝ)|=(1111042973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053204207/2000000000 : ℝ)|^4177 ≤ (10689772977739/25000000000000 : ℝ)^3153
        have hw : |(1053204207/2000000000 : ℝ)|=(1053204207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344690639/10000000000 : ℝ)*x 0 + (1053204207/2000000000 : ℝ)*x 1 + (-277760743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344690639/10000000000 : ℝ)^4177 ≤ (21803688773723/50000000000000 : ℝ)^3153 := by
    have hnat : (5344690639 : ℕ)^4177*50000000000000^3153 ≤ 21803688773723^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344690639 10000000000 21803688773723 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053204207/2000000000 : ℝ)^4177 ≤ (10689772977739/25000000000000 : ℝ)^3153 := by
    have hnat : (1053204207 : ℕ)^4177*25000000000000^3153 ≤ 10689772977739^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053204207 2000000000 10689772977739 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277760743/1250000000 : ℝ)^4177 ≤ (13633530524079/100000000000000 : ℝ)^3153 := by
    have hnat : (277760743 : ℕ)^4177*100000000000000^3153 ≤ 13633530524079^3153*1250000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277760743 1250000000 13633530524079 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344690639/10000000000 : ℝ), (1053204207/2000000000 : ℝ), (-277760743/1250000000 : ℝ)] ![(21803688773723/50000000000000 : ℝ), (10689772977739/25000000000000 : ℝ), (13633530524079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344690639/10000000000 : ℝ)|^4177 ≤ (21803688773723/50000000000000 : ℝ)^3153
        have hw : |(5344690639/10000000000 : ℝ)|=(5344690639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053204207/2000000000 : ℝ)|^4177 ≤ (10689772977739/25000000000000 : ℝ)^3153
        have hw : |(1053204207/2000000000 : ℝ)|=(1053204207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277760743/1250000000 : ℝ)|^4177 ≤ (13633530524079/100000000000000 : ℝ)^3153
        have hw : |(-277760743/1250000000 : ℝ)|=(277760743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362002237/10000000000 : ℝ)*x 0 + (4237325957/10000000000 : ℝ)*x 1 + (2245156259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362002237/10000000000 : ℝ)^4177 ≤ (6663411629397/20000000000000 : ℝ)^3153 := by
    have hnat : (4362002237 : ℕ)^4177*20000000000000^3153 ≤ 6663411629397^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362002237 10000000000 6663411629397 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237325957/10000000000 : ℝ)^4177 ≤ (32061399727197/100000000000000 : ℝ)^3153 := by
    have hnat : (4237325957 : ℕ)^4177*100000000000000^3153 ≤ 32061399727197^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237325957 10000000000 32061399727197 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245156259/5000000000 : ℝ)^4177 ≤ (1384861684469/4000000000000 : ℝ)^3153 := by
    have hnat : (2245156259 : ℕ)^4177*4000000000000^3153 ≤ 1384861684469^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245156259 5000000000 1384861684469 4000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362002237/10000000000 : ℝ), (4237325957/10000000000 : ℝ), (2245156259/5000000000 : ℝ)] ![(6663411629397/20000000000000 : ℝ), (32061399727197/100000000000000 : ℝ), (1384861684469/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362002237/10000000000 : ℝ)|^4177 ≤ (6663411629397/20000000000000 : ℝ)^3153
        have hw : |(4362002237/10000000000 : ℝ)|=(4362002237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237325957/10000000000 : ℝ)|^4177 ≤ (32061399727197/100000000000000 : ℝ)^3153
        have hw : |(4237325957/10000000000 : ℝ)|=(4237325957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245156259/5000000000 : ℝ)|^4177 ≤ (1384861684469/4000000000000 : ℝ)^3153
        have hw : |(2245156259/5000000000 : ℝ)|=(2245156259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157836063/10000000000 : ℝ)*x 0 + (1316584853/2500000000 : ℝ)*x 1 + (5392391499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157836063/10000000000 : ℝ)^4177 ≤ (6556885234259/50000000000000 : ℝ)^3153 := by
    have hnat : (2157836063 : ℕ)^4177*50000000000000^3153 ≤ 6556885234259^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157836063 10000000000 6556885234259 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316584853/2500000000 : ℝ)^4177 ≤ (42762516688271/100000000000000 : ℝ)^3153 := by
    have hnat : (1316584853 : ℕ)^4177*100000000000000^3153 ≤ 42762516688271^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316584853 2500000000 42762516688271 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392391499/10000000000 : ℝ)^4177 ≤ (44123712836423/100000000000000 : ℝ)^3153 := by
    have hnat : (5392391499 : ℕ)^4177*100000000000000^3153 ≤ 44123712836423^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392391499 10000000000 44123712836423 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157836063/10000000000 : ℝ), (1316584853/2500000000 : ℝ), (5392391499/10000000000 : ℝ)] ![(6556885234259/50000000000000 : ℝ), (42762516688271/100000000000000 : ℝ), (44123712836423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157836063/10000000000 : ℝ)|^4177 ≤ (6556885234259/50000000000000 : ℝ)^3153
        have hw : |(-2157836063/10000000000 : ℝ)|=(2157836063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316584853/2500000000 : ℝ)|^4177 ≤ (42762516688271/100000000000000 : ℝ)^3153
        have hw : |(1316584853/2500000000 : ℝ)|=(1316584853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392391499/10000000000 : ℝ)|^4177 ≤ (44123712836423/100000000000000 : ℝ)^3153
        have hw : |(5392391499/10000000000 : ℝ)|=(5392391499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656274297/5000000000 : ℝ)*x 0 + (-523928833/2500000000 : ℝ)*x 1 + (539239123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656274297/5000000000 : ℝ)^4177 ≤ (10815075001823/25000000000000 : ℝ)^3153 := by
    have hnat : (2656274297 : ℕ)^4177*25000000000000^3153 ≤ 10815075001823^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656274297 5000000000 10815075001823 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523928833/2500000000 : ℝ)^4177 ≤ (12615990049643/100000000000000 : ℝ)^3153 := by
    have hnat : (523928833 : ℕ)^4177*100000000000000^3153 ≤ 12615990049643^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523928833 2500000000 12615990049643 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539239123/1000000000 : ℝ)^4177 ≤ (882474198409/2000000000000 : ℝ)^3153 := by
    have hnat : (539239123 : ℕ)^4177*2000000000000^3153 ≤ 882474198409^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539239123 1000000000 882474198409 2000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656274297/5000000000 : ℝ), (-523928833/2500000000 : ℝ), (539239123/1000000000 : ℝ)] ![(10815075001823/25000000000000 : ℝ), (12615990049643/100000000000000 : ℝ), (882474198409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656274297/5000000000 : ℝ)|^4177 ≤ (10815075001823/25000000000000 : ℝ)^3153
        have hw : |(2656274297/5000000000 : ℝ)|=(2656274297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523928833/2500000000 : ℝ)|^4177 ≤ (12615990049643/100000000000000 : ℝ)^3153
        have hw : |(-523928833/2500000000 : ℝ)|=(523928833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539239123/1000000000 : ℝ)|^4177 ≤ (882474198409/2000000000000 : ℝ)^3153
        have hw : |(539239123/1000000000 : ℝ)|=(539239123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312548633/10000000000 : ℝ)*x 0 + (5392391107/10000000000 : ℝ)*x 1 + (-2095715447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312548633/10000000000 : ℝ)^4177 ≤ (43260300428011/100000000000000 : ℝ)^3153 := by
    have hnat : (5312548633 : ℕ)^4177*100000000000000^3153 ≤ 43260300428011^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312548633 10000000000 43260300428011 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392391107/10000000000 : ℝ)^4177 ≤ (352989668697/800000000000 : ℝ)^3153 := by
    have hnat : (5392391107 : ℕ)^4177*800000000000^3153 ≤ 352989668697^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392391107 10000000000 352989668697 800000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095715447/10000000000 : ℝ)^4177 ≤ (6307995483383/50000000000000 : ℝ)^3153 := by
    have hnat : (2095715447 : ℕ)^4177*50000000000000^3153 ≤ 6307995483383^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095715447 10000000000 6307995483383 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312548633/10000000000 : ℝ), (5392391107/10000000000 : ℝ), (-2095715447/10000000000 : ℝ)] ![(43260300428011/100000000000000 : ℝ), (352989668697/800000000000 : ℝ), (6307995483383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312548633/10000000000 : ℝ)|^4177 ≤ (43260300428011/100000000000000 : ℝ)^3153
        have hw : |(5312548633/10000000000 : ℝ)|=(5312548633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392391107/10000000000 : ℝ)|^4177 ≤ (352989668697/800000000000 : ℝ)^3153
        have hw : |(5392391107/10000000000 : ℝ)|=(5392391107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095715447/10000000000 : ℝ)|^4177 ≤ (6307995483383/50000000000000 : ℝ)^3153
        have hw : |(-2095715447/10000000000 : ℝ)|=(2095715447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s7_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362011883/10000000000 : ℝ)*x 0 + (4489676319/10000000000 : ℝ)*x 1 + (4237964483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362011883/10000000000 : ℝ)^4177 ≤ (1332686230049/4000000000000 : ℝ)^3153 := by
    have hnat : (4362011883 : ℕ)^4177*4000000000000^3153 ≤ 1332686230049^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362011883 10000000000 1332686230049 4000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489676319/10000000000 : ℝ)^4177 ≤ (17307521953913/50000000000000 : ℝ)^3153 := by
    have hnat : (4489676319 : ℕ)^4177*50000000000000^3153 ≤ 17307521953913^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489676319 10000000000 17307521953913 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237964483/10000000000 : ℝ)^4177 ≤ (1603390016091/5000000000000 : ℝ)^3153 := by
    have hnat : (4237964483 : ℕ)^4177*5000000000000^3153 ≤ 1603390016091^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237964483 10000000000 1603390016091 5000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362011883/10000000000 : ℝ), (4489676319/10000000000 : ℝ), (4237964483/10000000000 : ℝ)] ![(1332686230049/4000000000000 : ℝ), (17307521953913/50000000000000 : ℝ), (1603390016091/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362011883/10000000000 : ℝ)|^4177 ≤ (1332686230049/4000000000000 : ℝ)^3153
        have hw : |(4362011883/10000000000 : ℝ)|=(4362011883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489676319/10000000000 : ℝ)|^4177 ≤ (17307521953913/50000000000000 : ℝ)^3153
        have hw : |(4489676319/10000000000 : ℝ)|=(4489676319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237964483/10000000000 : ℝ)|^4177 ≤ (1603390016091/5000000000000 : ℝ)^3153
        have hw : |(4237964483/10000000000 : ℝ)|=(4237964483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11371/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (14091845486120243/100000000000000000000 : ℝ) := by
    have hpowers : (11371/100000 : ℝ)^8353 ≤ (14091845486120243/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11371 : ℕ)^8353*100000000000000000000^2048 ≤ 14091845486120243^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11371 100000 14091845486120243 100000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11371/100000 : ℝ)) (X := (14091845486120243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14067/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (6712329533034271/20000000000000000000 : ℝ) := by
    have hpowers : (14067/100000 : ℝ)^8353 ≤ (6712329533034271/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14067 : ℕ)^8353*20000000000000000000^2048 ≤ 6712329533034271^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14067 100000 6712329533034271 20000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14067/100000 : ℝ)) (X := (6712329533034271/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014091845486120243/50000000000000000000 : ℝ) ≤ (10000690938112633/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50014091845486120243/50000000000000000000 : ℝ)^2048 ≤ (10000690938112633/10000000000000000 : ℝ)^8353 := by
      have hnat : (50014091845486120243 : ℕ)^2048*10000000000000000^8353 ≤ 10000690938112633^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014091845486120243 50000000000000000000 10000690938112633 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690938112633/10000000000000000 : ℝ)) (X := (50014091845486120243/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023826746575645799/50000000000000000000 : ℝ) ≤ (10001168164810787/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (50023826746575645799/50000000000000000000 : ℝ)^2048 ≤ (10001168164810787/10000000000000000 : ℝ)^8353 := by
      have hnat : (50023826746575645799 : ℕ)^2048*10000000000000000^8353 ≤ 10001168164810787^8353*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023826746575645799 50000000000000000000 10001168164810787 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001168164810787/10000000000000000 : ℝ)) (X := (50023826746575645799/50000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006712329533034271/10000000000000000000 : ℝ) ≤ (10001645391508941/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (10006712329533034271/10000000000000000000 : ℝ)^2048 ≤ (10001645391508941/10000000000000000 : ℝ)^8353 := by
      have hnat : (10006712329533034271 : ℕ)^2048*10000000000000000^8353 ≤ 10001645391508941^8353*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006712329533034271 10000000000000000000 10001645391508941 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001645391508941/10000000000000000 : ℝ)) (X := (10006712329533034271/10000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14091845486120243/100000000000000000000 : ℝ) ≤ ((269510096795822403/269600000000000000 : ℝ)+2*(238613349077/134800000000000 : ℝ)*(11371/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (269510096795822403/269600000000000000 : ℝ)+2*(238613349077/134800000000000 : ℝ)*(11371/100000 : ℝ)=(10000690938112633/10000000000000000 : ℝ) by norm_num, show 1+2*(14091845486120243/100000000000000000000 : ℝ)=(50014091845486120243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6712329533034271/20000000000000000000 : ℝ)+(14091845486120243/100000000000000000000 : ℝ) ≤ ((269510096795822403/269600000000000000 : ℝ)+(238613349077/134800000000000 : ℝ)*((14067/100000 : ℝ)+(11371/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (269510096795822403/269600000000000000 : ℝ)+(238613349077/134800000000000 : ℝ)*((14067/100000 : ℝ)+(11371/100000 : ℝ))=(10001168164810787/10000000000000000 : ℝ) by norm_num, show 1+(6712329533034271/20000000000000000000 : ℝ)+(14091845486120243/100000000000000000000 : ℝ)=(50023826746575645799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6712329533034271/20000000000000000000 : ℝ) ≤ ((269510096795822403/269600000000000000 : ℝ)+2*(238613349077/134800000000000 : ℝ)*(14067/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (269510096795822403/269600000000000000 : ℝ)+2*(238613349077/134800000000000 : ℝ)*(14067/100000 : ℝ)=(10001645391508941/10000000000000000 : ℝ) by norm_num, show 1+2*(6712329533034271/20000000000000000000 : ℝ)=(10006712329533034271/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (269510096795822403/269600000000000000 : ℝ)*(X 1 0+X 2 0)+(238613349077/134800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (269510096795822403/269600000000000000 : ℝ)) (alpha := (238613349077/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (269510096795822403/269600000000000000 : ℝ)*(X 0 1+X 2 1)+(238613349077/134800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (269510096795822403/269600000000000000 : ℝ)) (alpha := (238613349077/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (269510096795822403/269600000000000000 : ℝ)*(X 0 2+X 1 2)+(238613349077/134800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (269510096795822403/269600000000000000 : ℝ)) (alpha := (238613349077/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2157830923/10000000000 : ℝ)*X 0 0+(5392711253/10000000000 : ℝ)*X 0 1+(658252629/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672345319/5000000000 : ℝ)*X 1 0+(-1111042973/5000000000 : ℝ)*X 1 1+(1053204207/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344690639/10000000000 : ℝ)*X 2 0+(1053204207/2000000000 : ℝ)*X 2 1+(-277760743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362002237/10000000000 : ℝ)*X 0 0+(4237325957/10000000000 : ℝ)*X 0 1+(2245156259/5000000000 : ℝ)*X 0 2+(4362002237/10000000000 : ℝ)*X 1 0+(4237325957/10000000000 : ℝ)*X 1 1+(2245156259/5000000000 : ℝ)*X 1 2+(4362002237/10000000000 : ℝ)*X 2 0+(4237325957/10000000000 : ℝ)*X 2 1+(2245156259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157836063/10000000000 : ℝ)*X 0 0+(1316584853/2500000000 : ℝ)*X 0 1+(5392391499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656274297/5000000000 : ℝ)*X 1 0+(-523928833/2500000000 : ℝ)*X 1 1+(539239123/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312548633/10000000000 : ℝ)*X 2 0+(5392391107/10000000000 : ℝ)*X 2 1+(-2095715447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362011883/10000000000 : ℝ)*X 0 0+(4489676319/10000000000 : ℝ)*X 0 1+(4237964483/10000000000 : ℝ)*X 0 2+(4362011883/10000000000 : ℝ)*X 1 0+(4489676319/10000000000 : ℝ)*X 1 1+(4237964483/10000000000 : ℝ)*X 1 2+(4362011883/10000000000 : ℝ)*X 2 0+(4489676319/10000000000 : ℝ)*X 2 1+(4237964483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12814296496852826164062009/1685000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374993321/25000000000000 : ℝ)*(base19) + (280041807/20000000000000 : ℝ)*(base23) + (54110241/100000000000000 : ℝ)*(lower2) + (190874733/100000000000000 : ℝ)*(upper3) + (14889401/12500000000000 : ℝ)*(upper5) + (1480771848515201/25000000000000 : ℝ)*(major0) + (1480771848515201/25000000000000 : ℝ)*(major1) + (1480771848515201/25000000000000 : ℝ)*(major2) + (3946656024648477/50000000000000 : ℝ)*(sp0) + (3946675911503751/50000000000000 : ℝ)*(sp1) + (7893351922771751/100000000000000 : ℝ)*(sp2) + (988199776700141/25000000000000 : ℝ)*(sp3) + (41273683833/100000000000000 : ℝ)*(sp4) + (22104842791/100000000000000 : ℝ)*(sp7) + (1976410605821677/50000000000000 : ℝ)*(f.failure) + (3946676661490393/50000000000000 : ℝ)*(f.sum) + (683196885977/1685000000000000000000000000 : ℝ)*base65 + (147265482099097997/6740000000000000000000000000000 : ℝ)*base68 + (100709395575197997/6740000000000000000000000000000 : ℝ)*base70 + (61824913414977997/6740000000000000000000000000000 : ℝ)*base72 + (649400262953/105312500000000000000000000 : ℝ)*base74 + (90156795782697997/6740000000000000000000000000000 : ℝ)*base76 + (8539523173402003/6740000000000000000000000000000 : ℝ)*base77 + (36326650679077997/6740000000000000000000000000000 : ℝ)*base80 + (3109270290077/421250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1310103/1250000000000000000000 : ℝ)*base89 + (1310103/1250000000000000000000 : ℝ)*base91 + (1310103/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60309827559097237550168619/13480000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1281236677/50000000000000 : ℝ)*(base19) + (3004025417/100000000000000 : ℝ)*(base23) + (213939209/100000000000000 : ℝ)*(upper2) + (115714151/100000000000000 : ℝ)*(upper3) + (74920393/25000000000000 : ℝ)*(upper5) + (5953011402397491/100000000000000 : ℝ)*(major0) + (5953011402397491/100000000000000 : ℝ)*(major1) + (5953011402397491/100000000000000 : ℝ)*(major2) + (67386886067/100000000000000 : ℝ)*(sp1) + (64181776833/100000000000000 : ℝ)*(sp2) + (991653926289201/12500000000000 : ℝ)*(sp4) + (7933161460954187/100000000000000 : ℝ)*(sp5) + (3966582112255679/50000000000000 : ℝ)*(sp6) + (496598905668409/12500000000000 : ℝ)*(sp7) + (496598905668409/12500000000000 : ℝ)*(f.failure) + (991653926289201/12500000000000 : ℝ)*(f.sum) + (9144909708527/6740000000000000000000000000 : ℝ)*base65 + (69230012862964873/26960000000000000000000000000000 : ℝ)*base67 + (82715714795124873/26960000000000000000000000000000 : ℝ)*base69 + (82567370339595127/26960000000000000000000000000000 : ℝ)*base72 + (26961058850327/6740000000000000000000000000 : ℝ)*base73 + (97317259967355127/26960000000000000000000000000000 : ℝ)*base76 + (229370934975515127/26960000000000000000000000000000 : ℝ)*base78 + (401574002913435127/26960000000000000000000000000000 : ℝ)*base80 + (64738653059287/6740000000000000000000000000 : ℝ)*base81 + (1917149/312500000000000000000 : ℝ)*base90 + (1917149/312500000000000000000 : ℝ)*base92 + (1917149/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1161_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1161_s8_0 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215783521/1000000000 : ℝ)*x 0 + (5392652081/10000000000 : ℝ)*x 1 + (2633038727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215783521/1000000000 : ℝ)^4177 ≤ (6556881800509/50000000000000 : ℝ)^3153 := by
    have hnat : (215783521 : ℕ)^4177*50000000000000^3153 ≤ 6556881800509^3153*1000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215783521 1000000000 6556881800509 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392652081/10000000000 : ℝ)^4177 ≤ (44126537579543/100000000000000 : ℝ)^3153 := by
    have hnat : (5392652081 : ℕ)^4177*100000000000000^3153 ≤ 44126537579543^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392652081 10000000000 44126537579543 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633038727/5000000000 : ℝ)^4177 ≤ (21379849402257/50000000000000 : ℝ)^3153 := by
    have hnat : (2633038727 : ℕ)^4177*50000000000000^3153 ≤ 21379849402257^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633038727 5000000000 21379849402257 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215783521/1000000000 : ℝ), (5392652081/10000000000 : ℝ), (2633038727/5000000000 : ℝ)] ![(6556881800509/50000000000000 : ℝ), (44126537579543/100000000000000 : ℝ), (21379849402257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215783521/1000000000 : ℝ)|^4177 ≤ (6556881800509/50000000000000 : ℝ)^3153
        have hw : |(-215783521/1000000000 : ℝ)|=(215783521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392652081/10000000000 : ℝ)|^4177 ≤ (44126537579543/100000000000000 : ℝ)^3153
        have hw : |(5392652081/10000000000 : ℝ)|=(5392652081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633038727/5000000000 : ℝ)|^4177 ≤ (21379849402257/50000000000000 : ℝ)^3153
        have hw : |(2633038727/5000000000 : ℝ)|=(2633038727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_1 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344675959/10000000000 : ℝ)*x 0 + (-2222030687/10000000000 : ℝ)*x 1 + (5266077539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344675959/10000000000 : ℝ)^4177 ≤ (21803609437089/50000000000000 : ℝ)^3153 := by
    have hnat : (5344675959 : ℕ)^4177*50000000000000^3153 ≤ 21803609437089^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344675959 10000000000 21803609437089 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222030687/10000000000 : ℝ)^4177 ≤ (6816540696279/50000000000000 : ℝ)^3153 := by
    have hnat : (2222030687 : ℕ)^4177*50000000000000^3153 ≤ 6816540696279^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222030687 10000000000 6816540696279 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266077539/10000000000 : ℝ)^4177 ≤ (42759699718853/100000000000000 : ℝ)^3153 := by
    have hnat : (5266077539 : ℕ)^4177*100000000000000^3153 ≤ 42759699718853^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266077539 10000000000 42759699718853 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344675959/10000000000 : ℝ), (-2222030687/10000000000 : ℝ), (5266077539/10000000000 : ℝ)] ![(21803609437089/50000000000000 : ℝ), (6816540696279/50000000000000 : ℝ), (42759699718853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344675959/10000000000 : ℝ)|^4177 ≤ (21803609437089/50000000000000 : ℝ)^3153
        have hw : |(5344675959/10000000000 : ℝ)|=(5344675959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222030687/10000000000 : ℝ)|^4177 ≤ (6816540696279/50000000000000 : ℝ)^3153
        have hw : |(-2222030687/10000000000 : ℝ)|=(2222030687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266077539/10000000000 : ℝ)|^4177 ≤ (42759699718853/100000000000000 : ℝ)^3153
        have hw : |(5266077539/10000000000 : ℝ)|=(5266077539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_2 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672337969/5000000000 : ℝ)*x 0 + (164564923/312500000 : ℝ)*x 1 + (-3471923/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672337969/5000000000 : ℝ)^4177 ≤ (21803609323597/50000000000000 : ℝ)^3153 := by
    have hnat : (2672337969 : ℕ)^4177*50000000000000^3153 ≤ 21803609323597^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672337969 5000000000 21803609323597 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164564923/312500000 : ℝ)^4177 ≤ (21379849843291/50000000000000 : ℝ)^3153 := by
    have hnat : (164564923 : ℕ)^4177*50000000000000^3153 ≤ 21379849843291^3153*312500000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164564923 312500000 21379849843291 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3471923/15625000 : ℝ)^4177 ≤ (6816540830391/50000000000000 : ℝ)^3153 := by
    have hnat : (3471923 : ℕ)^4177*50000000000000^3153 ≤ 6816540830391^3153*15625000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3471923 15625000 6816540830391 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672337969/5000000000 : ℝ), (164564923/312500000 : ℝ), (-3471923/15625000 : ℝ)] ![(21803609323597/50000000000000 : ℝ), (21379849843291/50000000000000 : ℝ), (6816540830391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672337969/5000000000 : ℝ)|^4177 ≤ (21803609323597/50000000000000 : ℝ)^3153
        have hw : |(2672337969/5000000000 : ℝ)|=(2672337969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164564923/312500000 : ℝ)|^4177 ≤ (21379849843291/50000000000000 : ℝ)^3153
        have hw : |(164564923/312500000 : ℝ)|=(164564923/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3471923/15625000 : ℝ)|^4177 ≤ (6816540830391/50000000000000 : ℝ)^3153
        have hw : |(-3471923/15625000 : ℝ)|=(3471923/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_3 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181002577/5000000000 : ℝ)*x 0 + (847488229/2000000000 : ℝ)*x 1 + (1122549147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181002577/5000000000 : ℝ)^4177 ≤ (16658543831501/50000000000000 : ℝ)^3153 := by
    have hnat : (2181002577 : ℕ)^4177*50000000000000^3153 ≤ 16658543831501^3153*5000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181002577 5000000000 16658543831501 50000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847488229/2000000000 : ℝ)^4177 ≤ (32062554350357/100000000000000 : ℝ)^3153 := by
    have hnat : (847488229 : ℕ)^4177*100000000000000^3153 ≤ 32062554350357^3153*2000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847488229 2000000000 32062554350357 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122549147/2500000000 : ℝ)^4177 ≤ (34620357968159/100000000000000 : ℝ)^3153 := by
    have hnat : (1122549147 : ℕ)^4177*100000000000000^3153 ≤ 34620357968159^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122549147 2500000000 34620357968159 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181002577/5000000000 : ℝ), (847488229/2000000000 : ℝ), (1122549147/2500000000 : ℝ)] ![(16658543831501/50000000000000 : ℝ), (32062554350357/100000000000000 : ℝ), (34620357968159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181002577/5000000000 : ℝ)|^4177 ≤ (16658543831501/50000000000000 : ℝ)^3153
        have hw : |(2181002577/5000000000 : ℝ)|=(2181002577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847488229/2000000000 : ℝ)|^4177 ≤ (32062554350357/100000000000000 : ℝ)^3153
        have hw : |(847488229/2000000000 : ℝ)|=(847488229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122549147/2500000000 : ℝ)|^4177 ≤ (34620357968159/100000000000000 : ℝ)^3153
        have hw : |(1122549147/2500000000 : ℝ)|=(1122549147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_4 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157840019/10000000000 : ℝ)*x 0 + (5266395579/10000000000 : ℝ)*x 1 + (5392332823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157840019/10000000000 : ℝ)^4177 ≤ (13113802318269/100000000000000 : ℝ)^3153 := by
    have hnat : (2157840019 : ℕ)^4177*100000000000000^3153 ≤ 13113802318269^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157840019 10000000000 13113802318269 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266395579/10000000000 : ℝ)^4177 ≤ (42763120882949/100000000000000 : ℝ)^3153 := by
    have hnat : (5266395579 : ℕ)^4177*100000000000000^3153 ≤ 42763120882949^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266395579 10000000000 42763120882949 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392332823/10000000000 : ℝ)^4177 ≤ (11030769196747/25000000000000 : ℝ)^3153 := by
    have hnat : (5392332823 : ℕ)^4177*25000000000000^3153 ≤ 11030769196747^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392332823 10000000000 11030769196747 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157840019/10000000000 : ℝ), (5266395579/10000000000 : ℝ), (5392332823/10000000000 : ℝ)] ![(13113802318269/100000000000000 : ℝ), (42763120882949/100000000000000 : ℝ), (11030769196747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157840019/10000000000 : ℝ)|^4177 ≤ (13113802318269/100000000000000 : ℝ)^3153
        have hw : |(-2157840019/10000000000 : ℝ)|=(2157840019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266395579/10000000000 : ℝ)|^4177 ≤ (42763120882949/100000000000000 : ℝ)^3153
        have hw : |(5266395579/10000000000 : ℝ)|=(5266395579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392332823/10000000000 : ℝ)|^4177 ≤ (11030769196747/25000000000000 : ℝ)^3153
        have hw : |(5392332823/10000000000 : ℝ)|=(5392332823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_5 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312562881/10000000000 : ℝ)*x 0 + (-523943849/2500000000 : ℝ)*x 1 + (5392332823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312562881/10000000000 : ℝ)^4177 ≤ (43260454130611/100000000000000 : ℝ)^3153 := by
    have hnat : (5312562881 : ℕ)^4177*100000000000000^3153 ≤ 43260454130611^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312562881 10000000000 43260454130611 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523943849/2500000000 : ℝ)^4177 ≤ (2523293812203/20000000000000 : ℝ)^3153 := by
    have hnat : (523943849 : ℕ)^4177*20000000000000^3153 ≤ 2523293812203^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523943849 2500000000 2523293812203 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392332823/10000000000 : ℝ)^4177 ≤ (11030769196747/25000000000000 : ℝ)^3153 := by
    have hnat : (5392332823 : ℕ)^4177*25000000000000^3153 ≤ 11030769196747^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392332823 10000000000 11030769196747 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312562881/10000000000 : ℝ), (-523943849/2500000000 : ℝ), (5392332823/10000000000 : ℝ)] ![(43260454130611/100000000000000 : ℝ), (2523293812203/20000000000000 : ℝ), (11030769196747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312562881/10000000000 : ℝ)|^4177 ≤ (43260454130611/100000000000000 : ℝ)^3153
        have hw : |(5312562881/10000000000 : ℝ)|=(5312562881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523943849/2500000000 : ℝ)|^4177 ≤ (2523293812203/20000000000000 : ℝ)^3153
        have hw : |(-523943849/2500000000 : ℝ)|=(523943849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392332823/10000000000 : ℝ)|^4177 ≤ (11030769196747/25000000000000 : ℝ)^3153
        have hw : |(5392332823/10000000000 : ℝ)|=(5392332823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_6 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312562881/10000000000 : ℝ)*x 0 + (5392332823/10000000000 : ℝ)*x 1 + (-523943849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312562881/10000000000 : ℝ)^4177 ≤ (43260454130611/100000000000000 : ℝ)^3153 := by
    have hnat : (5312562881 : ℕ)^4177*100000000000000^3153 ≤ 43260454130611^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312562881 10000000000 43260454130611 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392332823/10000000000 : ℝ)^4177 ≤ (11030769196747/25000000000000 : ℝ)^3153 := by
    have hnat : (5392332823 : ℕ)^4177*25000000000000^3153 ≤ 11030769196747^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392332823 10000000000 11030769196747 25000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523943849/2500000000 : ℝ)^4177 ≤ (2523293812203/20000000000000 : ℝ)^3153 := by
    have hnat : (523943849 : ℕ)^4177*20000000000000^3153 ≤ 2523293812203^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523943849 2500000000 2523293812203 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312562881/10000000000 : ℝ), (5392332823/10000000000 : ℝ), (-523943849/2500000000 : ℝ)] ![(43260454130611/100000000000000 : ℝ), (11030769196747/25000000000000 : ℝ), (2523293812203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312562881/10000000000 : ℝ)|^4177 ≤ (43260454130611/100000000000000 : ℝ)^3153
        have hw : |(5312562881/10000000000 : ℝ)|=(5312562881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392332823/10000000000 : ℝ)|^4177 ≤ (11030769196747/25000000000000 : ℝ)^3153
        have hw : |(5392332823/10000000000 : ℝ)|=(5392332823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523943849/2500000000 : ℝ)|^4177 ≤ (2523293812203/20000000000000 : ℝ)^3153
        have hw : |(-523943849/2500000000 : ℝ)|=(523943849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1161_s8_7 (p : ℝ) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362014817/10000000000 : ℝ)*x 0 + (280597593/625000000 : ℝ)*x 1 + (1059519631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362014817/10000000000 : ℝ)^4177 ≤ (33317185439279/100000000000000 : ℝ)^3153 := by
    have hnat : (4362014817 : ℕ)^4177*100000000000000^3153 ≤ 33317185439279^3153*10000000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362014817 10000000000 33317185439279 100000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280597593/625000000 : ℝ)^4177 ≤ (346138710437/1000000000000 : ℝ)^3153 := by
    have hnat : (280597593 : ℕ)^4177*1000000000000^3153 ≤ 346138710437^3153*625000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280597593 625000000 346138710437 1000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059519631/2500000000 : ℝ)^4177 ≤ (6413788700711/20000000000000 : ℝ)^3153 := by
    have hnat : (1059519631 : ℕ)^4177*20000000000000^3153 ≤ 6413788700711^3153*2500000000^4177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059519631 2500000000 6413788700711 20000000000000 4177 3153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4177/1024 : ℝ)) 4177 3153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362014817/10000000000 : ℝ), (280597593/625000000 : ℝ), (1059519631/2500000000 : ℝ)] ![(33317185439279/100000000000000 : ℝ), (346138710437/1000000000000 : ℝ), (6413788700711/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362014817/10000000000 : ℝ)|^4177 ≤ (33317185439279/100000000000000 : ℝ)^3153
        have hw : |(4362014817/10000000000 : ℝ)|=(4362014817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280597593/625000000 : ℝ)|^4177 ≤ (346138710437/1000000000000 : ℝ)^3153
        have hw : |(280597593/625000000 : ℝ)|=(280597593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059519631/2500000000 : ℝ)|^4177 ≤ (6413788700711/20000000000000 : ℝ)^3153
        have hw : |(1059519631/2500000000 : ℝ)|=(1059519631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1161_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5689/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11377/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (7061098687522303/50000000000000000000 : ℝ) := by
    have hpowers : (11377/100000 : ℝ)^8353 ≤ (7061098687522303/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11377 : ℕ)^8353*50000000000000000000^2048 ≤ 7061098687522303^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11377 100000 7061098687522303 50000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11377/100000 : ℝ)) (X := (7061098687522303/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (8353/2048 : ℝ) ≤ (16751650205978541/50000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^8353 ≤ (16751650205978541/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14061 : ℕ)^8353*50000000000000000000^2048 ≤ 16751650205978541^2048*100000^8353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 16751650205978541 50000000000000000000 8353 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (16751650205978541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007061098687522303/25000000000000000000 : ℝ) ≤ (100006924261393/100000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25007061098687522303/25000000000000000000 : ℝ)^2048 ≤ (100006924261393/100000000000000 : ℝ)^8353 := by
      have hnat : (25007061098687522303 : ℕ)^2048*100000000000000^8353 ≤ 100006924261393^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007061098687522303 25000000000000000000 100006924261393 100000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100006924261393/100000000000000 : ℝ)) (X := (25007061098687522303/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505953187223375211/12500000000000000000 : ℝ) ≤ (10001167478663323/10000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (12505953187223375211/12500000000000000000 : ℝ)^2048 ≤ (10001167478663323/10000000000000000 : ℝ)^8353 := by
      have hnat : (12505953187223375211 : ℕ)^2048*10000000000000000^8353 ≤ 10001167478663323^8353*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505953187223375211 12500000000000000000 10001167478663323 10000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001167478663323/10000000000000000 : ℝ)) (X := (12505953187223375211/12500000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016751650205978541/25000000000000000000 : ℝ) ≤ (5000821265593673/5000000000000000 : ℝ) ^ (8353/2048 : ℝ) := by
    have hpowers : (25016751650205978541/25000000000000000000 : ℝ)^2048 ≤ (5000821265593673/5000000000000000 : ℝ)^8353 := by
      have hnat : (25016751650205978541 : ℕ)^2048*5000000000000000^8353 ≤ 5000821265593673^8353*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016751650205978541 25000000000000000000 5000821265593673 5000000000000000 2048 8353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000821265593673/5000000000000000 : ℝ)) (X := (25016751650205978541/25000000000000000000 : ℝ)) (by norm_num) 8353 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7061098687522303/50000000000000000000 : ℝ) ≤ ((1219593142119375539/1220000000000000000 : ℝ)+2*(43186593093/24400000000000 : ℝ)*(11377/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (1219593142119375539/1220000000000000000 : ℝ)+2*(43186593093/24400000000000 : ℝ)*(11377/100000 : ℝ)=(100006924261393/100000000000000 : ℝ) by norm_num, show 1+2*(7061098687522303/50000000000000000000 : ℝ)=(25007061098687522303/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16751650205978541/50000000000000000000 : ℝ)+(7061098687522303/50000000000000000000 : ℝ) ≤ ((1219593142119375539/1220000000000000000 : ℝ)+(43186593093/24400000000000 : ℝ)*((14061/100000 : ℝ)+(11377/100000 : ℝ)))^(8353/2048 : ℝ) := by
    rw [show (1219593142119375539/1220000000000000000 : ℝ)+(43186593093/24400000000000 : ℝ)*((14061/100000 : ℝ)+(11377/100000 : ℝ))=(10001167478663323/10000000000000000 : ℝ) by norm_num, show 1+(16751650205978541/50000000000000000000 : ℝ)+(7061098687522303/50000000000000000000 : ℝ)=(12505953187223375211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16751650205978541/50000000000000000000 : ℝ) ≤ ((1219593142119375539/1220000000000000000 : ℝ)+2*(43186593093/24400000000000 : ℝ)*(14061/100000 : ℝ))^(8353/2048 : ℝ) := by
    rw [show (1219593142119375539/1220000000000000000 : ℝ)+2*(43186593093/24400000000000 : ℝ)*(14061/100000 : ℝ)=(5000821265593673/5000000000000000 : ℝ) by norm_num, show 1+2*(16751650205978541/50000000000000000000 : ℝ)=(25016751650205978541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1219593142119375539/1220000000000000000 : ℝ)*(X 1 0+X 2 0)+(43186593093/24400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (1219593142119375539/1220000000000000000 : ℝ)) (alpha := (43186593093/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1219593142119375539/1220000000000000000 : ℝ)*(X 0 1+X 2 1)+(43186593093/24400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (1219593142119375539/1220000000000000000 : ℝ)) (alpha := (43186593093/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1219593142119375539/1220000000000000000 : ℝ)*(X 0 2+X 1 2)+(43186593093/24400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8353/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (1219593142119375539/1220000000000000000 : ℝ)) (alpha := (43186593093/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215783521/1000000000 : ℝ)*X 0 0+(5392652081/10000000000 : ℝ)*X 0 1+(2633038727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344675959/10000000000 : ℝ)*X 1 0+(-2222030687/10000000000 : ℝ)*X 1 1+(5266077539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672337969/5000000000 : ℝ)*X 2 0+(164564923/312500000 : ℝ)*X 2 1+(-3471923/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181002577/5000000000 : ℝ)*X 0 0+(847488229/2000000000 : ℝ)*X 0 1+(1122549147/2500000000 : ℝ)*X 0 2+(2181002577/5000000000 : ℝ)*X 1 0+(847488229/2000000000 : ℝ)*X 1 1+(1122549147/2500000000 : ℝ)*X 1 2+(2181002577/5000000000 : ℝ)*X 2 0+(847488229/2000000000 : ℝ)*X 2 1+(1122549147/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157840019/10000000000 : ℝ)*X 0 0+(5266395579/10000000000 : ℝ)*X 0 1+(5392332823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312562881/10000000000 : ℝ)*X 1 0+(-523943849/2500000000 : ℝ)*X 1 1+(5392332823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312562881/10000000000 : ℝ)*X 2 0+(5392332823/10000000000 : ℝ)*X 2 1+(-523943849/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362014817/10000000000 : ℝ)*X 0 0+(280597593/625000000 : ℝ)*X 0 1+(1059519631/2500000000 : ℝ)*X 0 2+(4362014817/10000000000 : ℝ)*X 1 0+(280597593/625000000 : ℝ)*X 1 1+(1059519631/2500000000 : ℝ)*X 1 2+(4362014817/10000000000 : ℝ)*X 2 0+(280597593/625000000 : ℝ)*X 2 1+(1059519631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1161_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (585509406352658898325311411/61000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1842882683/100000000000000 : ℝ)*(base19) + (345428509/20000000000000 : ℝ)*(base23) + (22634059/50000000000000 : ℝ)*(lower2) + (130057457/50000000000000 : ℝ)*(upper3) + (139331261/100000000000000 : ℝ)*(upper5) + (5928517726165561/100000000000000 : ℝ)*(major0) + (5928517726165561/100000000000000 : ℝ)*(major1) + (5928517726165561/100000000000000 : ℝ)*(major2) + (1975134032144281/25000000000000 : ℝ)*(sp0) + (987573512618537/12500000000000 : ℝ)*(sp1) + (1580117643337687/20000000000000 : ℝ)*(sp2) + (494552240885983/12500000000000 : ℝ)*(sp3) + (10763050771/20000000000000 : ℝ)*(sp4) + (2726146177/10000000000000 : ℝ)*(sp7) + (1978222594274817/50000000000000 : ℝ)*(f.failure) + (395029497191549/5000000000000 : ℝ)*(f.sum) + (7007851120247/1220000000000000000000000000 : ℝ)*base66 + (1771823191981737621/122000000000000000000000000000000 : ℝ)*base68 + (1119818633949737621/122000000000000000000000000000000 : ℝ)*base70 + (1539478203463737621/122000000000000000000000000000000 : ℝ)*base72 + (5020640270813/1220000000000000000000000000 : ℝ)*base73 + (872839221075737621/122000000000000000000000000000000 : ℝ)*base76 + (2253685865715737621/122000000000000000000000000000000 : ℝ)*base78 + (3214130868643737621/122000000000000000000000000000000 : ℝ)*base80 + (38203950467/1220000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (11336563/1250000000000000000000 : ℝ)*base89 + (11336563/1250000000000000000000 : ℝ)*base91 + (11336563/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6708093391381699894323/610000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2002524681/100000000000000 : ℝ)*(base19) + (87049189/4000000000000 : ℝ)*(base23) + (175515359/25000000000000 : ℝ)*(lower1) + (44127061/20000000000000 : ℝ)*(upper3) + (39522397/50000000000000 : ℝ)*(lower4) + (56137331/25000000000000 : ℝ)*(upper5) + (2979197324502409/50000000000000 : ℝ)*(major0) + (2979197324502409/50000000000000 : ℝ)*(major1) + (2979197324502409/50000000000000 : ℝ)*(major2) + (4122027481/100000000000000 : ℝ)*(sp2) + (3970202566044261/50000000000000 : ℝ)*(sp4) + (24813759779887/312500000000 : ℝ)*(sp5) + (1985099708457829/25000000000000 : ℝ)*(sp6) + (795276759871719/20000000000000 : ℝ)*(sp7) + (795276759871719/20000000000000 : ℝ)*(f.failure) + (3970202566044261/50000000000000 : ℝ)*(f.sum) + (1908944259133/610000000000000000000000000 : ℝ)*base66 + (1941106775444976549/61000000000000000000000000000000 : ℝ)*base68 + (335168180512976549/61000000000000000000000000000000 : ℝ)*base70 + (7075878860421976549/61000000000000000000000000000000 : ℝ)*base72 + (973429058163/610000000000000000000000000 : ℝ)*base74 + (10133422293933023451/61000000000000000000000000000000 : ℝ)*base75 + (258235897004023451/61000000000000000000000000000000 : ℝ)*base77 + (786605358149023451/61000000000000000000000000000000 : ℝ)*base79 + (6683326496603/610000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2372059/500000000000000000000 : ℝ)*base90 + (2372059/500000000000000000000 : ℝ)*base92 + (2372059/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1161_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1161_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1161_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1161_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1161_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1161_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8353/2048 : ℝ) ≤ p) (hpb : p ≤ (4177/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37461139/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1161_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
