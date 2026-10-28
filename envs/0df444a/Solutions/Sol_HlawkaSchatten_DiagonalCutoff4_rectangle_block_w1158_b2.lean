-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:44.870227+00:00
-- url     : https://prove2.me/submissions/a80e1c51-2d9d-4483-8f47-bda27cb0fb96

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
theorem support_rectangle_w1158_s6_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269904117/1250000000 : ℝ)*x 0 + (5393059811/10000000000 : ℝ)*x 1 + (1053139/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269904117/1250000000 : ℝ)^8351 ≤ (13121908352937/100000000000000 : ℝ)^6303 := by
    have hnat : (269904117 : ℕ)^8351*100000000000000^6303 ≤ 13121908352937^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269904117 1250000000 13121908352937 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393059811/10000000000 : ℝ)^8351 ≤ (8825349099959/20000000000000 : ℝ)^6303 := by
    have hnat : (5393059811 : ℕ)^8351*20000000000000^6303 ≤ 8825349099959^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393059811 10000000000 8825349099959 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053139/2000000 : ℝ)^8351 ≤ (5343918267571/12500000000000 : ℝ)^6303 := by
    have hnat : (1053139 : ℕ)^8351*12500000000000^6303 ≤ 5343918267571^6303*2000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053139 2000000 5343918267571 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269904117/1250000000 : ℝ), (5393059811/10000000000 : ℝ), (1053139/2000000 : ℝ)] ![(13121908352937/100000000000000 : ℝ), (8825349099959/20000000000000 : ℝ), (5343918267571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269904117/1250000000 : ℝ)|^8351 ≤ (13121908352937/100000000000000 : ℝ)^6303
        have hw : |(-269904117/1250000000 : ℝ)|=(269904117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393059811/10000000000 : ℝ)|^8351 ≤ (8825349099959/20000000000000 : ℝ)^6303
        have hw : |(5393059811/10000000000 : ℝ)|=(5393059811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053139/2000000 : ℝ)|^8351 ≤ (5343918267571/12500000000000 : ℝ)^6303
        have hw : |(1053139/2000000 : ℝ)|=(1053139/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344775901/10000000000 : ℝ)*x 0 + (-2223834981/10000000000 : ℝ)*x 1 + (1053139/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344775901/10000000000 : ℝ)^8351 ≤ (5450509547791/12500000000000 : ℝ)^6303 := by
    have hnat : (5344775901 : ℕ)^8351*12500000000000^6303 ≤ 5450509547791^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344775901 10000000000 5450509547791 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223834981/10000000000 : ℝ)^8351 ≤ (13644577472233/100000000000000 : ℝ)^6303 := by
    have hnat : (2223834981 : ℕ)^8351*100000000000000^6303 ≤ 13644577472233^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223834981 10000000000 13644577472233 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053139/2000000 : ℝ)^8351 ≤ (5343918267571/12500000000000 : ℝ)^6303 := by
    have hnat : (1053139 : ℕ)^8351*12500000000000^6303 ≤ 5343918267571^6303*2000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053139 2000000 5343918267571 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344775901/10000000000 : ℝ), (-2223834981/10000000000 : ℝ), (1053139/2000000 : ℝ)] ![(5450509547791/12500000000000 : ℝ), (13644577472233/100000000000000 : ℝ), (5343918267571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344775901/10000000000 : ℝ)|^8351 ≤ (5450509547791/12500000000000 : ℝ)^6303
        have hw : |(5344775901/10000000000 : ℝ)|=(5344775901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2223834981/10000000000 : ℝ)|^8351 ≤ (13644577472233/100000000000000 : ℝ)^6303
        have hw : |(-2223834981/10000000000 : ℝ)|=(2223834981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053139/2000000 : ℝ)|^8351 ≤ (5343918267571/12500000000000 : ℝ)^6303
        have hw : |(1053139/2000000 : ℝ)|=(1053139/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344775899/10000000000 : ℝ)*x 0 + (5265694999/10000000000 : ℝ)*x 1 + (-2223834983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344775899/10000000000 : ℝ)^8351 ≤ (4360407636071/10000000000000 : ℝ)^6303 := by
    have hnat : (5344775899 : ℕ)^8351*10000000000000^6303 ≤ 4360407636071^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344775899 10000000000 4360407636071 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265694999/10000000000 : ℝ)^8351 ≤ (10687836532453/25000000000000 : ℝ)^6303 := by
    have hnat : (5265694999 : ℕ)^8351*25000000000000^6303 ≤ 10687836532453^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265694999 10000000000 10687836532453 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223834983/10000000000 : ℝ)^8351 ≤ (3411144372123/25000000000000 : ℝ)^6303 := by
    have hnat : (2223834983 : ℕ)^8351*25000000000000^6303 ≤ 3411144372123^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223834983 10000000000 3411144372123 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344775899/10000000000 : ℝ), (5265694999/10000000000 : ℝ), (-2223834983/10000000000 : ℝ)] ![(4360407636071/10000000000000 : ℝ), (10687836532453/25000000000000 : ℝ), (3411144372123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344775899/10000000000 : ℝ)|^8351 ≤ (4360407636071/10000000000000 : ℝ)^6303
        have hw : |(5344775899/10000000000 : ℝ)|=(5344775899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265694999/10000000000 : ℝ)|^8351 ≤ (10687836532453/25000000000000 : ℝ)^6303
        have hw : |(5265694999/10000000000 : ℝ)|=(5265694999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223834983/10000000000 : ℝ)|^8351 ≤ (3411144372123/25000000000000 : ℝ)^6303
        have hw : |(-2223834983/10000000000 : ℝ)|=(2223834983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362408297/10000000000 : ℝ)*x 0 + (423715141/1000000000 : ℝ)*x 1 + (35930687/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362408297/10000000000 : ℝ)^8351 ≤ (6663378878513/20000000000000 : ℝ)^6303 := by
    have hnat : (4362408297 : ℕ)^8351*20000000000000^6303 ≤ 6663378878513^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362408297 10000000000 6663378878513 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423715141/1000000000 : ℝ)^8351 ≤ (8013848734169/25000000000000 : ℝ)^6303 := by
    have hnat : (423715141 : ℕ)^8351*25000000000000^6303 ≤ 8013848734169^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423715141 1000000000 8013848734169 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35930687/80000000 : ℝ)^8351 ≤ (34627710654699/100000000000000 : ℝ)^6303 := by
    have hnat : (35930687 : ℕ)^8351*100000000000000^6303 ≤ 34627710654699^6303*80000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35930687 80000000 34627710654699 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362408297/10000000000 : ℝ), (423715141/1000000000 : ℝ), (35930687/80000000 : ℝ)] ![(6663378878513/20000000000000 : ℝ), (8013848734169/25000000000000 : ℝ), (34627710654699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362408297/10000000000 : ℝ)|^8351 ≤ (6663378878513/20000000000000 : ℝ)^6303
        have hw : |(4362408297/10000000000 : ℝ)|=(4362408297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423715141/1000000000 : ℝ)|^8351 ≤ (8013848734169/25000000000000 : ℝ)^6303
        have hw : |(423715141/1000000000 : ℝ)|=(423715141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35930687/80000000 : ℝ)|^8351 ≤ (34627710654699/100000000000000 : ℝ)^6303
        have hw : |(35930687/80000000 : ℝ)|=(35930687/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-107961893/500000000 : ℝ)*x 0 + (2633008359/5000000000 : ℝ)*x 1 + (5392736917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107961893/500000000 : ℝ)^8351 ≤ (6560973999811/50000000000000 : ℝ)^6303 := by
    have hnat : (107961893 : ℕ)^8351*50000000000000^6303 ≤ 6560973999811^6303*500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107961893 500000000 6560973999811 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633008359/5000000000 : ℝ)^8351 ≤ (8550961369689/20000000000000 : ℝ)^6303 := by
    have hnat : (2633008359 : ℕ)^8351*20000000000000^6303 ≤ 8550961369689^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633008359 5000000000 8550961369689 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392736917/10000000000 : ℝ)^8351 ≤ (8824649026547/20000000000000 : ℝ)^6303 := by
    have hnat : (5392736917 : ℕ)^8351*20000000000000^6303 ≤ 8824649026547^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392736917 10000000000 8824649026547 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107961893/500000000 : ℝ), (2633008359/5000000000 : ℝ), (5392736917/10000000000 : ℝ)] ![(6560973999811/50000000000000 : ℝ), (8550961369689/20000000000000 : ℝ), (8824649026547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107961893/500000000 : ℝ)|^8351 ≤ (6560973999811/50000000000000 : ℝ)^6303
        have hw : |(-107961893/500000000 : ℝ)|=(107961893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633008359/5000000000 : ℝ)|^8351 ≤ (8550961369689/20000000000000 : ℝ)^6303
        have hw : |(2633008359/5000000000 : ℝ)|=(2633008359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392736917/10000000000 : ℝ)|^8351 ≤ (8824649026547/20000000000000 : ℝ)^6303
        have hw : |(5392736917/10000000000 : ℝ)|=(5392736917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312469517/10000000000 : ℝ)*x 0 + (-2096793059/10000000000 : ℝ)*x 1 + (1348184229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312469517/10000000000 : ℝ)^8351 ≤ (43255217448039/100000000000000 : ℝ)^6303 := by
    have hnat : (5312469517 : ℕ)^8351*100000000000000^6303 ≤ 43255217448039^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312469517 10000000000 43255217448039 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096793059/10000000000 : ℝ)^8351 ≤ (1577692176193/12500000000000 : ℝ)^6303 := by
    have hnat : (2096793059 : ℕ)^8351*12500000000000^6303 ≤ 1577692176193^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096793059 10000000000 1577692176193 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348184229/2500000000 : ℝ)^8351 ≤ (22061622560947/50000000000000 : ℝ)^6303 := by
    have hnat : (1348184229 : ℕ)^8351*50000000000000^6303 ≤ 22061622560947^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348184229 2500000000 22061622560947 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312469517/10000000000 : ℝ), (-2096793059/10000000000 : ℝ), (1348184229/2500000000 : ℝ)] ![(43255217448039/100000000000000 : ℝ), (1577692176193/12500000000000 : ℝ), (22061622560947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312469517/10000000000 : ℝ)|^8351 ≤ (43255217448039/100000000000000 : ℝ)^6303
        have hw : |(5312469517/10000000000 : ℝ)|=(5312469517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096793059/10000000000 : ℝ)|^8351 ≤ (1577692176193/12500000000000 : ℝ)^6303
        have hw : |(-2096793059/10000000000 : ℝ)|=(2096793059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348184229/2500000000 : ℝ)|^8351 ≤ (22061622560947/50000000000000 : ℝ)^6303
        have hw : |(1348184229/2500000000 : ℝ)|=(1348184229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312469519/10000000000 : ℝ)*x 0 + (1348184227/2500000000 : ℝ)*x 1 + (-524198267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312469519/10000000000 : ℝ)^8351 ≤ (21627608734807/50000000000000 : ℝ)^6303 := by
    have hnat : (5312469519 : ℕ)^8351*50000000000000^6303 ≤ 21627608734807^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312469519 10000000000 21627608734807 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348184227/2500000000 : ℝ)^8351 ≤ (4412324503517/10000000000000 : ℝ)^6303 := by
    have hnat : (1348184227 : ℕ)^8351*10000000000000^6303 ≤ 4412324503517^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348184227 2500000000 4412324503517 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524198267/2500000000 : ℝ)^8351 ≤ (6310768740661/50000000000000 : ℝ)^6303 := by
    have hnat : (524198267 : ℕ)^8351*50000000000000^6303 ≤ 6310768740661^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524198267 2500000000 6310768740661 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312469519/10000000000 : ℝ), (1348184227/2500000000 : ℝ), (-524198267/2500000000 : ℝ)] ![(21627608734807/50000000000000 : ℝ), (4412324503517/10000000000000 : ℝ), (6310768740661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312469519/10000000000 : ℝ)|^8351 ≤ (21627608734807/50000000000000 : ℝ)^6303
        have hw : |(5312469519/10000000000 : ℝ)|=(5312469519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348184227/2500000000 : ℝ)|^8351 ≤ (4412324503517/10000000000000 : ℝ)^6303
        have hw : |(1348184227/2500000000 : ℝ)|=(1348184227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524198267/2500000000 : ℝ)|^8351 ≤ (6310768740661/50000000000000 : ℝ)^6303
        have hw : |(-524198267/2500000000 : ℝ)|=(524198267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s6_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362418113/10000000000 : ℝ)*x 0 + (4490693797/10000000000 : ℝ)*x 1 + (4237795817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362418113/10000000000 : ℝ)^8351 ≤ (16658496859413/50000000000000 : ℝ)^6303 := by
    have hnat : (4362418113 : ℕ)^8351*50000000000000^6303 ≤ 16658496859413^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362418113 10000000000 16658496859413 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490693797/10000000000 : ℝ)^8351 ≤ (34621151964387/100000000000000 : ℝ)^6303 := by
    have hnat : (4490693797 : ℕ)^8351*100000000000000^6303 ≤ 34621151964387^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490693797 10000000000 34621151964387 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237795817/10000000000 : ℝ)^8351 ≤ (32061854293923/100000000000000 : ℝ)^6303 := by
    have hnat : (4237795817 : ℕ)^8351*100000000000000^6303 ≤ 32061854293923^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237795817 10000000000 32061854293923 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362418113/10000000000 : ℝ), (4490693797/10000000000 : ℝ), (4237795817/10000000000 : ℝ)] ![(16658496859413/50000000000000 : ℝ), (34621151964387/100000000000000 : ℝ), (32061854293923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362418113/10000000000 : ℝ)|^8351 ≤ (16658496859413/50000000000000 : ℝ)^6303
        have hw : |(4362418113/10000000000 : ℝ)|=(4362418113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490693797/10000000000 : ℝ)|^8351 ≤ (34621151964387/100000000000000 : ℝ)^6303
        have hw : |(4490693797/10000000000 : ℝ)|=(4490693797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237795817/10000000000 : ℝ)|^8351 ≤ (32061854293923/100000000000000 : ℝ)^6303
        have hw : |(4237795817/10000000000 : ℝ)|=(4237795817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5669/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (13970269212859929/100000000000000000000 : ℝ) := by
    have hpowers : (5669/50000 : ℝ)^4175 ≤ (13970269212859929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5669 : ℕ)^4175*100000000000000000000^1024 ≤ 13970269212859929^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5669 50000 13970269212859929 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5669/50000 : ℝ)) (X := (13970269212859929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (4175/1024 : ℝ) ≤ (33932200253086279/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^4175 ≤ (33932200253086279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2819 : ℕ)^4175*100000000000000000000^1024 ≤ 33932200253086279^1024*20000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 33932200253086279 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (33932200253086279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013970269212859929/50000000000000000000 : ℝ) ≤ (5000342611917913/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50013970269212859929/50000000000000000000 : ℝ)^1024 ≤ (5000342611917913/5000000000000000 : ℝ)^4175 := by
      have hnat : (50013970269212859929 : ℕ)^1024*5000000000000000^4175 ≤ 5000342611917913^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013970269212859929 50000000000000000000 5000342611917913 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000342611917913/5000000000000000 : ℝ)) (X := (50013970269212859929/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126496952170810819/3125000000000000000 : ℝ) ≤ (2500293672240699/2500000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (3126496952170810819/3125000000000000000 : ℝ)^1024 ≤ (2500293672240699/2500000000000000 : ℝ)^4175 := by
      have hnat : (3126496952170810819 : ℕ)^1024*2500000000000000^4175 ≤ 2500293672240699^4175*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126496952170810819 3125000000000000000 2500293672240699 2500000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500293672240699/2500000000000000 : ℝ)) (X := (3126496952170810819/3125000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033932200253086279/50000000000000000000 : ℝ) ≤ (5000832077044883/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50033932200253086279/50000000000000000000 : ℝ)^1024 ≤ (5000832077044883/5000000000000000 : ℝ)^4175 := by
      have hnat : (50033932200253086279 : ℕ)^1024*5000000000000000^4175 ≤ 5000832077044883^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033932200253086279 50000000000000000000 5000832077044883 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000832077044883/5000000000000000 : ℝ)) (X := (50033932200253086279/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13970269212859929/100000000000000000000 : ℝ) ≤ ((13780395025448100281/13785000000000000000 : ℝ)+2*(48946512697/27570000000000 : ℝ)*(5669/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (13780395025448100281/13785000000000000000 : ℝ)+2*(48946512697/27570000000000 : ℝ)*(5669/50000 : ℝ)=(5000342611917913/5000000000000000 : ℝ) by norm_num, show 1+2*(13970269212859929/100000000000000000000 : ℝ)=(50013970269212859929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33932200253086279/100000000000000000000 : ℝ)+(13970269212859929/100000000000000000000 : ℝ) ≤ ((13780395025448100281/13785000000000000000 : ℝ)+(48946512697/27570000000000 : ℝ)*((2819/20000 : ℝ)+(5669/50000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (13780395025448100281/13785000000000000000 : ℝ)+(48946512697/27570000000000 : ℝ)*((2819/20000 : ℝ)+(5669/50000 : ℝ))=(2500293672240699/2500000000000000 : ℝ) by norm_num, show 1+(33932200253086279/100000000000000000000 : ℝ)+(13970269212859929/100000000000000000000 : ℝ)=(3126496952170810819/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33932200253086279/100000000000000000000 : ℝ) ≤ ((13780395025448100281/13785000000000000000 : ℝ)+2*(48946512697/27570000000000 : ℝ)*(2819/20000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (13780395025448100281/13785000000000000000 : ℝ)+2*(48946512697/27570000000000 : ℝ)*(2819/20000 : ℝ)=(5000832077044883/5000000000000000 : ℝ) by norm_num, show 1+2*(33932200253086279/100000000000000000000 : ℝ)=(50033932200253086279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13780395025448100281/13785000000000000000 : ℝ)*(X 1 0+X 2 0)+(48946512697/27570000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (13780395025448100281/13785000000000000000 : ℝ)) (alpha := (48946512697/27570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13780395025448100281/13785000000000000000 : ℝ)*(X 0 1+X 2 1)+(48946512697/27570000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (13780395025448100281/13785000000000000000 : ℝ)) (alpha := (48946512697/27570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13780395025448100281/13785000000000000000 : ℝ)*(X 0 2+X 1 2)+(48946512697/27570000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (13780395025448100281/13785000000000000000 : ℝ)) (alpha := (48946512697/27570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-269904117/1250000000 : ℝ)*X 0 0+(5393059811/10000000000 : ℝ)*X 0 1+(1053139/2000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344775901/10000000000 : ℝ)*X 1 0+(-2223834981/10000000000 : ℝ)*X 1 1+(1053139/2000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344775899/10000000000 : ℝ)*X 2 0+(5265694999/10000000000 : ℝ)*X 2 1+(-2223834983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362408297/10000000000 : ℝ)*X 0 0+(423715141/1000000000 : ℝ)*X 0 1+(35930687/80000000 : ℝ)*X 0 2+(4362408297/10000000000 : ℝ)*X 1 0+(423715141/1000000000 : ℝ)*X 1 1+(35930687/80000000 : ℝ)*X 1 2+(4362408297/10000000000 : ℝ)*X 2 0+(423715141/1000000000 : ℝ)*X 2 1+(35930687/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107961893/500000000 : ℝ)*X 0 0+(2633008359/5000000000 : ℝ)*X 0 1+(5392736917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312469517/10000000000 : ℝ)*X 1 0+(-2096793059/10000000000 : ℝ)*X 1 1+(1348184229/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312469519/10000000000 : ℝ)*X 2 0+(1348184227/2500000000 : ℝ)*X 2 1+(-524198267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362418113/10000000000 : ℝ)*X 0 0+(4490693797/10000000000 : ℝ)*X 0 1+(4237795817/10000000000 : ℝ)*X 0 2+(4362418113/10000000000 : ℝ)*X 1 0+(4490693797/10000000000 : ℝ)*X 1 1+(4237795817/10000000000 : ℝ)*X 1 2+(4362418113/10000000000 : ℝ)*X 2 0+(4490693797/10000000000 : ℝ)*X 2 1+(4237795817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (546632482193763463701448887/57437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374139899/20000000000000 : ℝ)*(base19) + (1739169157/100000000000000 : ℝ)*(base23) + (68729707/100000000000000 : ℝ)*(lower2) + (48384503/20000000000000 : ℝ)*(upper3) + (8857167/6250000000000 : ℝ)*(upper5) + (1473221201372327/25000000000000 : ℝ)*(major0) + (1473221201372327/25000000000000 : ℝ)*(major1) + (1473221201372327/25000000000000 : ℝ)*(major2) + (7851515537187389/100000000000000 : ℝ)*(sp0) + (785156433666813/10000000000000 : ℝ)*(sp1) + (1962891117049617/25000000000000 : ℝ)*(sp2) + (3934175476299861/100000000000000 : ℝ)*(sp3) + (50670180237/100000000000000 : ℝ)*(sp4) + (13805038953/50000000000000 : ℝ)*(sp7) + (491775385797221/12500000000000 : ℝ)*(f.failure) + (62812529658941/800000000000 : ℝ)*(f.sum) + (3138649804219/551400000000000000000000000 : ℝ)*base66 + (981969500714801113/344625000000000000000000000000000 : ℝ)*base68 + (1297876268456426113/344625000000000000000000000000000 : ℝ)*base70 + (5610098699891801113/344625000000000000000000000000000 : ℝ)*base72 + (4252461179459/1378500000000000000000000000 : ℝ)*base73 + (3745267532175198887/344625000000000000000000000000000 : ℝ)*base75 + (642643722768948887/344625000000000000000000000000000 : ℝ)*base77 + (1595379905772176113/344625000000000000000000000000000 : ℝ)*base80 + (4271784764129/2757000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5359/305175781250000000 : ℝ)*base89 + (5359/305175781250000000 : ℝ)*base91 + (5359/305175781250000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (488261311629022789884541301/114875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (817708647/100000000000000 : ℝ)*(base19) + (218614231/25000000000000 : ℝ)*(base23) + (69359/80000000000 : ℝ)*(upper3) + (13251569/50000000000000 : ℝ)*(lower4) + (92956649/100000000000000 : ℝ)*(upper5) + (2961391183166579/50000000000000 : ℝ)*(major0) + (2961391183166579/50000000000000 : ℝ)*(major1) + (2961391183166579/50000000000000 : ℝ)*(major2) + (355753643/1562500000000 : ℝ)*(sp1) + (2340771659/10000000000000 : ℝ)*(sp2) + (7891401318719333/100000000000000 : ℝ)*(sp4) + (3945688866388767/50000000000000 : ℝ)*(sp5) + (7891377036545819/100000000000000 : ℝ)*(sp6) + (988540818066989/25000000000000 : ℝ)*(sp7) + (988540818066989/25000000000000 : ℝ)*(f.failure) + (7891401318719333/100000000000000 : ℝ)*(f.sum) + (546902451179/689250000000000000000000000 : ℝ)*base65 + (5958383311119291301/689250000000000000000000000000000 : ℝ)*base68 + (8215575360640958699/689250000000000000000000000000000 : ℝ)*base69 + (1951297500675291301/689250000000000000000000000000000 : ℝ)*base72 + (1319814422723/1378500000000000000000000000 : ℝ)*base74 + (9658059276958208699/689250000000000000000000000000000 : ℝ)*base75 + (2830336850865458699/689250000000000000000000000000000 : ℝ)*base77 + (4381116614936708699/689250000000000000000000000000000 : ℝ)*base79 + (4128710916989/1378500000000000000000000000 : ℝ)*base82 + (48277/4882812500000000000 : ℝ)*base90 + (48277/4882812500000000000 : ℝ)*base92 + (48277/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s7_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079628729/5000000000 : ℝ)*x 0 + (21571053/40000000 : ℝ)*x 1 + (658246939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079628729/5000000000 : ℝ)^8351 ≤ (6561052898793/50000000000000 : ℝ)^6303 := by
    have hnat : (1079628729 : ℕ)^8351*50000000000000^6303 ≤ 6561052898793^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079628729 5000000000 6561052898793 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21571053/40000000 : ℝ)^8351 ≤ (44123530595897/100000000000000 : ℝ)^6303 := by
    have hnat : (21571053 : ℕ)^8351*100000000000000^6303 ≤ 44123530595897^6303*40000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21571053 40000000 44123530595897 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658246939/1250000000 : ℝ)^8351 ≤ (42754363593287/100000000000000 : ℝ)^6303 := by
    have hnat : (658246939 : ℕ)^8351*100000000000000^6303 ≤ 42754363593287^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658246939 1250000000 42754363593287 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079628729/5000000000 : ℝ), (21571053/40000000 : ℝ), (658246939/1250000000 : ℝ)] ![(6561052898793/50000000000000 : ℝ), (44123530595897/100000000000000 : ℝ), (42754363593287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079628729/5000000000 : ℝ)|^8351 ≤ (6561052898793/50000000000000 : ℝ)^6303
        have hw : |(-1079628729/5000000000 : ℝ)|=(1079628729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21571053/40000000 : ℝ)|^8351 ≤ (44123530595897/100000000000000 : ℝ)^6303
        have hw : |(21571053/40000000 : ℝ)|=(21571053/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658246939/1250000000 : ℝ)|^8351 ≤ (42754363593287/100000000000000 : ℝ)^6303
        have hw : |(658246939/1250000000 : ℝ)|=(658246939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672350771/5000000000 : ℝ)*x 0 + (-69486333/312500000 : ℝ)*x 1 + (1053195103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672350771/5000000000 : ℝ)^8351 ≤ (21801636315849/50000000000000 : ℝ)^6303 := by
    have hnat : (2672350771 : ℕ)^8351*50000000000000^6303 ≤ 21801636315849^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672350771 5000000000 21801636315849 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69486333/312500000 : ℝ)^8351 ≤ (1705295465911/12500000000000 : ℝ)^6303 := by
    have hnat : (69486333 : ℕ)^8351*12500000000000^6303 ≤ 1705295465911^6303*312500000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69486333 312500000 1705295465911 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053195103/2000000000 : ℝ)^8351 ≤ (21377181812779/50000000000000 : ℝ)^6303 := by
    have hnat : (1053195103 : ℕ)^8351*50000000000000^6303 ≤ 21377181812779^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053195103 2000000000 21377181812779 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672350771/5000000000 : ℝ), (-69486333/312500000 : ℝ), (1053195103/2000000000 : ℝ)] ![(21801636315849/50000000000000 : ℝ), (1705295465911/12500000000000 : ℝ), (21377181812779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672350771/5000000000 : ℝ)|^8351 ≤ (21801636315849/50000000000000 : ℝ)^6303
        have hw : |(2672350771/5000000000 : ℝ)|=(2672350771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69486333/312500000 : ℝ)|^8351 ≤ (1705295465911/12500000000000 : ℝ)^6303
        have hw : |(-69486333/312500000 : ℝ)|=(69486333/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053195103/2000000000 : ℝ)|^8351 ≤ (21377181812779/50000000000000 : ℝ)^6303
        have hw : |(1053195103/2000000000 : ℝ)|=(1053195103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344701543/10000000000 : ℝ)*x 0 + (1053195103/2000000000 : ℝ)*x 1 + (-1111781327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344701543/10000000000 : ℝ)^8351 ≤ (43603272642507/100000000000000 : ℝ)^6303 := by
    have hnat : (5344701543 : ℕ)^8351*100000000000000^6303 ≤ 43603272642507^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344701543 10000000000 43603272642507 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053195103/2000000000 : ℝ)^8351 ≤ (21377181812779/50000000000000 : ℝ)^6303 := by
    have hnat : (1053195103 : ℕ)^8351*50000000000000^6303 ≤ 21377181812779^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053195103 2000000000 21377181812779 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111781327/5000000000 : ℝ)^8351 ≤ (13642363711031/100000000000000 : ℝ)^6303 := by
    have hnat : (1111781327 : ℕ)^8351*100000000000000^6303 ≤ 13642363711031^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111781327 5000000000 13642363711031 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344701543/10000000000 : ℝ), (1053195103/2000000000 : ℝ), (-1111781327/5000000000 : ℝ)] ![(43603272642507/100000000000000 : ℝ), (21377181812779/50000000000000 : ℝ), (13642363711031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344701543/10000000000 : ℝ)|^8351 ≤ (43603272642507/100000000000000 : ℝ)^6303
        have hw : |(5344701543/10000000000 : ℝ)|=(5344701543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053195103/2000000000 : ℝ)|^8351 ≤ (21377181812779/50000000000000 : ℝ)^6303
        have hw : |(1053195103/2000000000 : ℝ)|=(1053195103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111781327/5000000000 : ℝ)|^8351 ≤ (13642363711031/100000000000000 : ℝ)^6303
        have hw : |(-1111781327/5000000000 : ℝ)|=(1111781327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181211489/5000000000 : ℝ)*x 0 + (4237725357/10000000000 : ℝ)*x 1 + (1122689531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181211489/5000000000 : ℝ)^8351 ≤ (10661453743/32000000000 : ℝ)^6303 := by
    have hnat : (2181211489 : ℕ)^8351*32000000000^6303 ≤ 10661453743^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181211489 5000000000 10661453743 32000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237725357/10000000000 : ℝ)^8351 ≤ (32061148006861/100000000000000 : ℝ)^6303 := by
    have hnat : (4237725357 : ℕ)^8351*100000000000000^6303 ≤ 32061148006861^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237725357 10000000000 32061148006861 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122689531/2500000000 : ℝ)^8351 ≤ (34621809037287/100000000000000 : ℝ)^6303 := by
    have hnat : (1122689531 : ℕ)^8351*100000000000000^6303 ≤ 34621809037287^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122689531 2500000000 34621809037287 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181211489/5000000000 : ℝ), (4237725357/10000000000 : ℝ), (1122689531/2500000000 : ℝ)] ![(10661453743/32000000000 : ℝ), (32061148006861/100000000000000 : ℝ), (34621809037287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181211489/5000000000 : ℝ)|^8351 ≤ (10661453743/32000000000 : ℝ)^6303
        have hw : |(2181211489/5000000000 : ℝ)|=(2181211489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237725357/10000000000 : ℝ)|^8351 ≤ (32061148006861/100000000000000 : ℝ)^6303
        have hw : |(4237725357/10000000000 : ℝ)|=(4237725357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122689531/2500000000 : ℝ)|^8351 ≤ (34621809037287/100000000000000 : ℝ)^6303
        have hw : |(1122689531/2500000000 : ℝ)|=(1122689531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079631423/5000000000 : ℝ)*x 0 + (2633146979/5000000000 : ℝ)*x 1 + (337027703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079631423/5000000000 : ℝ)^8351 ≤ (13122149180433/100000000000000 : ℝ)^6303 := by
    have hnat : (1079631423 : ℕ)^8351*100000000000000^6303 ≤ 13122149180433^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079631423 5000000000 13122149180433 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633146979/5000000000 : ℝ)^8351 ≤ (42757789163333/100000000000000 : ℝ)^6303 := by
    have hnat : (2633146979 : ℕ)^8351*100000000000000^6303 ≤ 42757789163333^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633146979 5000000000 42757789163333 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337027703/625000000 : ℝ)^8351 ≤ (44120061641557/100000000000000 : ℝ)^6303 := by
    have hnat : (337027703 : ℕ)^8351*100000000000000^6303 ≤ 44120061641557^6303*625000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337027703 625000000 44120061641557 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079631423/5000000000 : ℝ), (2633146979/5000000000 : ℝ), (337027703/625000000 : ℝ)] ![(13122149180433/100000000000000 : ℝ), (42757789163333/100000000000000 : ℝ), (44120061641557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079631423/5000000000 : ℝ)|^8351 ≤ (13122149180433/100000000000000 : ℝ)^6303
        have hw : |(-1079631423/5000000000 : ℝ)|=(1079631423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633146979/5000000000 : ℝ)|^8351 ≤ (42757789163333/100000000000000 : ℝ)^6303
        have hw : |(2633146979/5000000000 : ℝ)|=(2633146979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337027703/625000000 : ℝ)|^8351 ≤ (44120061641557/100000000000000 : ℝ)^6303
        have hw : |(337027703/625000000 : ℝ)|=(337027703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656271043/5000000000 : ℝ)*x 0 + (-1048547289/5000000000 : ℝ)*x 1 + (5392442867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656271043/5000000000 : ℝ)^8351 ≤ (8651200062049/20000000000000 : ℝ)^6303 := by
    have hnat : (2656271043 : ℕ)^8351*20000000000000^6303 ≤ 8651200062049^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656271043 5000000000 8651200062049 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048547289/5000000000 : ℝ)^8351 ≤ (6311971087417/50000000000000 : ℝ)^6303 := by
    have hnat : (1048547289 : ℕ)^8351*50000000000000^6303 ≤ 6311971087417^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048547289 5000000000 6311971087417 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392442867/10000000000 : ℝ)^8351 ≤ (44120057511399/100000000000000 : ℝ)^6303 := by
    have hnat : (5392442867 : ℕ)^8351*100000000000000^6303 ≤ 44120057511399^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392442867 10000000000 44120057511399 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656271043/5000000000 : ℝ), (-1048547289/5000000000 : ℝ), (5392442867/10000000000 : ℝ)] ![(8651200062049/20000000000000 : ℝ), (6311971087417/50000000000000 : ℝ), (44120057511399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656271043/5000000000 : ℝ)|^8351 ≤ (8651200062049/20000000000000 : ℝ)^6303
        have hw : |(2656271043/5000000000 : ℝ)|=(2656271043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048547289/5000000000 : ℝ)|^8351 ≤ (6311971087417/50000000000000 : ℝ)^6303
        have hw : |(-1048547289/5000000000 : ℝ)|=(1048547289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392442867/10000000000 : ℝ)|^8351 ≤ (44120057511399/100000000000000 : ℝ)^6303
        have hw : |(5392442867/10000000000 : ℝ)|=(5392442867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656271019/5000000000 : ℝ)*x 0 + (5392442757/10000000000 : ℝ)*x 1 + (-2097094791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656271019/5000000000 : ℝ)^8351 ≤ (10813999948107/25000000000000 : ℝ)^6303 := by
    have hnat : (2656271019 : ℕ)^8351*25000000000000^6303 ≤ 10813999948107^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656271019 5000000000 10813999948107 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392442757/10000000000 : ℝ)^8351 ≤ (8824011263793/20000000000000 : ℝ)^6303 := by
    have hnat : (5392442757 : ℕ)^8351*20000000000000^6303 ≤ 8824011263793^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392442757 10000000000 8824011263793 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097094791/10000000000 : ℝ)^8351 ≤ (2524788774731/20000000000000 : ℝ)^6303 := by
    have hnat : (2097094791 : ℕ)^8351*20000000000000^6303 ≤ 2524788774731^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097094791 10000000000 2524788774731 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656271019/5000000000 : ℝ), (5392442757/10000000000 : ℝ), (-2097094791/10000000000 : ℝ)] ![(10813999948107/25000000000000 : ℝ), (8824011263793/20000000000000 : ℝ), (2524788774731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656271019/5000000000 : ℝ)|^8351 ≤ (10813999948107/25000000000000 : ℝ)^6303
        have hw : |(2656271019/5000000000 : ℝ)|=(2656271019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392442757/10000000000 : ℝ)|^8351 ≤ (8824011263793/20000000000000 : ℝ)^6303
        have hw : |(5392442757/10000000000 : ℝ)|=(5392442757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097094791/10000000000 : ℝ)|^8351 ≤ (2524788774731/20000000000000 : ℝ)^6303
        have hw : |(-2097094791/10000000000 : ℝ)|=(2097094791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174497309/400000000 : ℝ)*x 0 + (4490121839/10000000000 : ℝ)*x 1 + (33906911/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174497309/400000000 : ℝ)^8351 ≤ (6663428315009/20000000000000 : ℝ)^6303 := by
    have hnat : (174497309 : ℕ)^8351*20000000000000^6303 ≤ 6663428315009^6303*400000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174497309 400000000 6663428315009 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490121839/10000000000 : ℝ)^8351 ≤ (3461530979157/10000000000000 : ℝ)^6303 := by
    have hnat : (4490121839 : ℕ)^8351*10000000000000^6303 ≤ 3461530979157^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490121839 10000000000 3461530979157 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33906911/80000000 : ℝ)^8351 ≤ (32067548614621/100000000000000 : ℝ)^6303 := by
    have hnat : (33906911 : ℕ)^8351*100000000000000^6303 ≤ 32067548614621^6303*80000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33906911 80000000 32067548614621 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174497309/400000000 : ℝ), (4490121839/10000000000 : ℝ), (33906911/80000000 : ℝ)] ![(6663428315009/20000000000000 : ℝ), (3461530979157/10000000000000 : ℝ), (32067548614621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174497309/400000000 : ℝ)|^8351 ≤ (6663428315009/20000000000000 : ℝ)^6303
        have hw : |(174497309/400000000 : ℝ)|=(174497309/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490121839/10000000000 : ℝ)|^8351 ≤ (3461530979157/10000000000000 : ℝ)^6303
        have hw : |(4490121839/10000000000 : ℝ)|=(4490121839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33906911/80000000 : ℝ)|^8351 ≤ (32067548614621/100000000000000 : ℝ)^6303
        have hw : |(33906911/80000000 : ℝ)|=(33906911/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s7_8 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-36204387/10000000000 : ℝ)*x 0 + (1454910909/2500000000 : ℝ)*x 1 + (3013724909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36204387/10000000000 : ℝ)^8351 ≤ (29141544557/50000000000000 : ℝ)^6303 := by
    have hnat : (36204387 : ℕ)^8351*50000000000000^6303 ≤ 29141544557^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36204387 10000000000 29141544557 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1454910909/2500000000 : ℝ)^8351 ≤ (9761924223417/20000000000000 : ℝ)^6303 := by
    have hnat : (1454910909 : ℕ)^8351*20000000000000^6303 ≤ 9761924223417^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454910909 2500000000 9761924223417 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3013724909/5000000000 : ℝ)^8351 ≤ (51132095775649/100000000000000 : ℝ)^6303 := by
    have hnat : (3013724909 : ℕ)^8351*100000000000000^6303 ≤ 51132095775649^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013724909 5000000000 51132095775649 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36204387/10000000000 : ℝ), (1454910909/2500000000 : ℝ), (3013724909/5000000000 : ℝ)] ![(29141544557/50000000000000 : ℝ), (9761924223417/20000000000000 : ℝ), (51132095775649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36204387/10000000000 : ℝ)|^8351 ≤ (29141544557/50000000000000 : ℝ)^6303
        have hw : |(-36204387/10000000000 : ℝ)|=(36204387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1454910909/2500000000 : ℝ)|^8351 ≤ (9761924223417/20000000000000 : ℝ)^6303
        have hw : |(1454910909/2500000000 : ℝ)|=(1454910909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3013724909/5000000000 : ℝ)|^8351 ≤ (51132095775649/100000000000000 : ℝ)^6303
        have hw : |(3013724909/5000000000 : ℝ)|=(3013724909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11367/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (141165312419221/1000000000000000000 : ℝ) := by
    have hpowers : (11367/100000 : ℝ)^4175 ≤ (141165312419221/1000000000000000000 : ℝ)^1024 := by
      have hnat : (11367 : ℕ)^4175*1000000000000000000^1024 ≤ 141165312419221^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11367 100000 141165312419221 1000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11367/100000 : ℝ)) (X := (141165312419221/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (4175/1024 : ℝ) ≤ (33638704181575721/100000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^4175 ≤ (33638704181575721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2813 : ℕ)^4175*100000000000000000000^1024 ≤ 33638704181575721^1024*20000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 33638704181575721 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (33638704181575721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500141165312419221/500000000000000000 : ℝ) ≤ (5000346198518557/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (500141165312419221/500000000000000000 : ℝ)^1024 ≤ (5000346198518557/5000000000000000 : ℝ)^4175 := by
      have hnat : (500141165312419221 : ℕ)^1024*5000000000000000^4175 ≤ 5000346198518557^4175*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500141165312419221 500000000000000000 5000346198518557 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346198518557/5000000000000000 : ℝ)) (X := (500141165312419221/500000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047755235423497821/100000000000000000000 : ℝ) ≤ (1250146384883049/1250000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (100047755235423497821/100000000000000000000 : ℝ)^1024 ≤ (1250146384883049/1250000000000000 : ℝ)^4175 := by
      have hnat : (100047755235423497821 : ℕ)^1024*1250000000000000^4175 ≤ 1250146384883049^4175*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047755235423497821 100000000000000000000 1250146384883049 1250000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250146384883049/1250000000000000 : ℝ)) (X := (100047755235423497821/100000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033638704181575721/50000000000000000000 : ℝ) ≤ (1000164976109167/1000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50033638704181575721/50000000000000000000 : ℝ)^1024 ≤ (1000164976109167/1000000000000000 : ℝ)^4175 := by
      have hnat : (50033638704181575721 : ℕ)^1024*1000000000000000^4175 ≤ 1000164976109167^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033638704181575721 50000000000000000000 1000164976109167 1000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000164976109167/1000000000000000 : ℝ)) (X := (50033638704181575721/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(141165312419221/1000000000000000000 : ℝ) ≤ ((10535541300780467/10539062500000000 : ℝ)+2*(239341013639/134900000000000 : ℝ)*(11367/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (10535541300780467/10539062500000000 : ℝ)+2*(239341013639/134900000000000 : ℝ)*(11367/100000 : ℝ)=(5000346198518557/5000000000000000 : ℝ) by norm_num, show 1+2*(141165312419221/1000000000000000000 : ℝ)=(500141165312419221/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33638704181575721/100000000000000000000 : ℝ)+(141165312419221/1000000000000000000 : ℝ) ≤ ((10535541300780467/10539062500000000 : ℝ)+(239341013639/134900000000000 : ℝ)*((2813/20000 : ℝ)+(11367/100000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (10535541300780467/10539062500000000 : ℝ)+(239341013639/134900000000000 : ℝ)*((2813/20000 : ℝ)+(11367/100000 : ℝ))=(1250146384883049/1250000000000000 : ℝ) by norm_num, show 1+(33638704181575721/100000000000000000000 : ℝ)+(141165312419221/1000000000000000000 : ℝ)=(100047755235423497821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33638704181575721/100000000000000000000 : ℝ) ≤ ((10535541300780467/10539062500000000 : ℝ)+2*(239341013639/134900000000000 : ℝ)*(2813/20000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (10535541300780467/10539062500000000 : ℝ)+2*(239341013639/134900000000000 : ℝ)*(2813/20000 : ℝ)=(1000164976109167/1000000000000000 : ℝ) by norm_num, show 1+2*(33638704181575721/100000000000000000000 : ℝ)=(50033638704181575721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10535541300780467/10539062500000000 : ℝ)*(X 1 0+X 2 0)+(239341013639/134900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (10535541300780467/10539062500000000 : ℝ)) (alpha := (239341013639/134900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10535541300780467/10539062500000000 : ℝ)*(X 0 1+X 2 1)+(239341013639/134900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (10535541300780467/10539062500000000 : ℝ)) (alpha := (239341013639/134900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10535541300780467/10539062500000000 : ℝ)*(X 0 2+X 1 2)+(239341013639/134900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (10535541300780467/10539062500000000 : ℝ)) (alpha := (239341013639/134900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079628729/5000000000 : ℝ)*X 0 0+(21571053/40000000 : ℝ)*X 0 1+(658246939/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672350771/5000000000 : ℝ)*X 1 0+(-69486333/312500000 : ℝ)*X 1 1+(1053195103/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344701543/10000000000 : ℝ)*X 2 0+(1053195103/2000000000 : ℝ)*X 2 1+(-1111781327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181211489/5000000000 : ℝ)*X 0 0+(4237725357/10000000000 : ℝ)*X 0 1+(1122689531/2500000000 : ℝ)*X 0 2+(2181211489/5000000000 : ℝ)*X 1 0+(4237725357/10000000000 : ℝ)*X 1 1+(1122689531/2500000000 : ℝ)*X 1 2+(2181211489/5000000000 : ℝ)*X 2 0+(4237725357/10000000000 : ℝ)*X 2 1+(1122689531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079631423/5000000000 : ℝ)*X 0 0+(2633146979/5000000000 : ℝ)*X 0 1+(337027703/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656271043/5000000000 : ℝ)*X 1 0+(-1048547289/5000000000 : ℝ)*X 1 1+(5392442867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656271019/5000000000 : ℝ)*X 2 0+(5392442757/10000000000 : ℝ)*X 2 1+(-2097094791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174497309/400000000 : ℝ)*X 0 0+(4490121839/10000000000 : ℝ)*X 0 1+(33906911/80000000 : ℝ)*X 0 2+(174497309/400000000 : ℝ)*X 1 0+(4490121839/10000000000 : ℝ)*X 1 1+(33906911/80000000 : ℝ)*X 1 2+(174497309/400000000 : ℝ)*X 2 0+(4490121839/10000000000 : ℝ)*X 2 1+(33906911/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-36204387/10000000000 : ℝ)*X 0 0+(1454910909/2500000000 : ℝ)*X 0 1+(3013724909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (370043560549639264629/26980000000000000000000000 : ℝ) := by norm_num
    linear_combination (703436029/100000000000000 : ℝ)*(lower2) + (2578343/781250000000 : ℝ)*(lower3) + (144819569/20000000000000 : ℝ)*(lower4) + (281107/200000000000 : ℝ)*(lower5) + (47357072641141/800000000000 : ℝ)*(major0) + (47357072641141/800000000000 : ℝ)*(major1) + (47357072641141/800000000000 : ℝ)*(major2) + (3943600012183947/50000000000000 : ℝ)*(sp0) + (7887194861132387/100000000000000 : ℝ)*(sp1) + (7887188191105029/100000000000000 : ℝ)*(sp2) + (1976030707967517/50000000000000 : ℝ)*(sp3) + (11426035249/100000000000000 : ℝ)*(sp5) + (18096062607/100000000000000 : ℝ)*(sp6) + (6262799743/100000000000000 : ℝ)*(sp8) + (1976030707967517/50000000000000 : ℝ)*(f.failure) + (1971801571791909/25000000000000 : ℝ)*(f.sum) + (28620176359521/337250000000000000000000000 : ℝ)*base65 + (1110942532808951/67450000000000000000000000000 : ℝ)*base67 + (496322608774449/67450000000000000000000000000 : ℝ)*base70 + (72859145324349/67450000000000000000000000000 : ℝ)*base72 + (3992408975419/1349000000000000000000000000 : ℝ)*base73 + (348332515654851/67450000000000000000000000000 : ℝ)*base75 + (1977761988729599/67450000000000000000000000000 : ℝ)*base78 + (591066842823251/67450000000000000000000000000 : ℝ)*base79 + (890151449519/674500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (297337/19531250000000000000 : ℝ)*base90 + (297337/19531250000000000000 : ℝ)*base92 + (297337/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28277757940699892206830669/4215625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483849391/50000000000000 : ℝ)*(lower2) + (11964461/3125000000000 : ℝ)*(lower3) + (1005749293/100000000000000 : ℝ)*(lower4) + (135325707/20000000000000 : ℝ)*(lower5) + (5949642797251191/100000000000000 : ℝ)*(major0) + (5949642797251191/100000000000000 : ℝ)*(major1) + (5949642797251191/100000000000000 : ℝ)*(major2) + (9721532923/20000000000000 : ℝ)*(sp0) + (10905996699/100000000000000 : ℝ)*(sp3) + (7927129997663239/100000000000000 : ℝ)*(sp4) + (3963594779512453/50000000000000 : ℝ)*(sp5) + (3963594779512453/50000000000000 : ℝ)*(sp6) + (1986042452942967/50000000000000 : ℝ)*(sp7) + (10953697051/100000000000000 : ℝ)*(sp8) + (3972095811882633/100000000000000 : ℝ)*(f.failure) + (3963594779512453/50000000000000 : ℝ)*(f.sum) + (289822333695327/3372500000000000000000000000 : ℝ)*base65 + (159794825342113951/8431250000000000000000000000000 : ℝ)*base67 + (202929214341045201/8431250000000000000000000000000 : ℝ)*base69 + (109501589701620201/8431250000000000000000000000000 : ℝ)*base71 + (284641902451/1686250000000000000000000000 : ℝ)*base73 + (149511422699995201/8431250000000000000000000000000 : ℝ)*base75 + (15351469159820201/8431250000000000000000000000000 : ℝ)*base77 + (17736775952923549/8431250000000000000000000000000 : ℝ)*base80 + (7012446384551/6745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (184251/78125000000000000000 : ℝ)*base90 + (184251/78125000000000000000 : ℝ)*base92 + (184251/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s8_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079630883/5000000000 : ℝ)*x 0 + (67408799/125000000 : ℝ)*x 1 + (2633016039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079630883/5000000000 : ℝ)^8351 ≤ (13122140484537/100000000000000 : ℝ)^6303 := by
    have hnat : (1079630883 : ℕ)^8351*100000000000000^6303 ≤ 13122140484537^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079630883 5000000000 13122140484537 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67408799/125000000 : ℝ)^8351 ≤ (882457748581/2000000000000 : ℝ)^6303 := by
    have hnat : (67408799 : ℕ)^8351*2000000000000^6303 ≤ 882457748581^6303*125000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67408799 125000000 882457748581 2000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633016039/5000000000 : ℝ)^8351 ≤ (42754972077079/100000000000000 : ℝ)^6303 := by
    have hnat : (2633016039 : ℕ)^8351*100000000000000^6303 ≤ 42754972077079^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633016039 5000000000 42754972077079 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079630883/5000000000 : ℝ), (67408799/125000000 : ℝ), (2633016039/5000000000 : ℝ)] ![(13122140484537/100000000000000 : ℝ), (882457748581/2000000000000 : ℝ), (42754972077079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079630883/5000000000 : ℝ)|^8351 ≤ (13122140484537/100000000000000 : ℝ)^6303
        have hw : |(-1079630883/5000000000 : ℝ)|=(1079630883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67408799/125000000 : ℝ)|^8351 ≤ (882457748581/2000000000000 : ℝ)^6303
        have hw : |(67408799/125000000 : ℝ)|=(67408799/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633016039/5000000000 : ℝ)|^8351 ≤ (42754972077079/100000000000000 : ℝ)^6303
        have hw : |(2633016039/5000000000 : ℝ)|=(2633016039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344686799/10000000000 : ℝ)*x 0 + (-8894029/40000000 : ℝ)*x 1 + (5266032199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344686799/10000000000 : ℝ)^8351 ≤ (4360311327421/10000000000000 : ℝ)^6303 := by
    have hnat : (5344686799 : ℕ)^8351*10000000000000^6303 ≤ 4360311327421^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344686799 10000000000 4360311327421 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8894029/40000000 : ℝ)^8351 ≤ (13641913339643/100000000000000 : ℝ)^6303 := by
    have hnat : (8894029 : ℕ)^8351*100000000000000^6303 ≤ 13641913339643^6303*40000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8894029 40000000 13641913339643 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266032199/10000000000 : ℝ)^8351 ≤ (21377486689343/50000000000000 : ℝ)^6303 := by
    have hnat : (5266032199 : ℕ)^8351*50000000000000^6303 ≤ 21377486689343^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266032199 10000000000 21377486689343 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344686799/10000000000 : ℝ), (-8894029/40000000 : ℝ), (5266032199/10000000000 : ℝ)] ![(4360311327421/10000000000000 : ℝ), (13641913339643/100000000000000 : ℝ), (21377486689343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344686799/10000000000 : ℝ)|^8351 ≤ (4360311327421/10000000000000 : ℝ)^6303
        have hw : |(5344686799/10000000000 : ℝ)|=(5344686799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8894029/40000000 : ℝ)|^8351 ≤ (13641913339643/100000000000000 : ℝ)^6303
        have hw : |(-8894029/40000000 : ℝ)|=(8894029/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266032199/10000000000 : ℝ)|^8351 ≤ (21377486689343/50000000000000 : ℝ)^6303
        have hw : |(5266032199/10000000000 : ℝ)|=(5266032199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344686873/10000000000 : ℝ)*x 0 + (42128257/80000000 : ℝ)*x 1 + (-2223507249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344686873/10000000000 : ℝ)^8351 ≤ (43603114074077/100000000000000 : ℝ)^6303 := by
    have hnat : (5344686873 : ℕ)^8351*100000000000000^6303 ≤ 43603114074077^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344686873 10000000000 43603114074077 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42128257/80000000 : ℝ)^8351 ≤ (21377486291331/50000000000000 : ℝ)^6303 := by
    have hnat : (42128257 : ℕ)^8351*50000000000000^6303 ≤ 21377486291331^6303*80000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42128257 80000000 21377486291331 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223507249/10000000000 : ℝ)^8351 ≤ (6820956665757/50000000000000 : ℝ)^6303 := by
    have hnat : (2223507249 : ℕ)^8351*50000000000000^6303 ≤ 6820956665757^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223507249 10000000000 6820956665757 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344686873/10000000000 : ℝ), (42128257/80000000 : ℝ), (-2223507249/10000000000 : ℝ)] ![(43603114074077/100000000000000 : ℝ), (21377486291331/50000000000000 : ℝ), (6820956665757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344686873/10000000000 : ℝ)|^8351 ≤ (43603114074077/100000000000000 : ℝ)^6303
        have hw : |(5344686873/10000000000 : ℝ)|=(5344686873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42128257/80000000 : ℝ)|^8351 ≤ (21377486291331/50000000000000 : ℝ)^6303
        have hw : |(42128257/80000000 : ℝ)|=(42128257/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223507249/10000000000 : ℝ)|^8351 ≤ (6820956665757/50000000000000 : ℝ)^6303
        have hw : |(-2223507249/10000000000 : ℝ)|=(2223507249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362426023/10000000000 : ℝ)*x 0 + (2118920337/5000000000 : ℝ)*x 1 + (2245320971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362426023/10000000000 : ℝ)^8351 ≤ (8329268439671/25000000000000 : ℝ)^6303 := by
    have hnat : (4362426023 : ℕ)^8351*25000000000000^6303 ≤ 8329268439671^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362426023 10000000000 8329268439671 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118920337/5000000000 : ℝ)^8351 ≤ (16031151969973/50000000000000 : ℝ)^6303 := by
    have hnat : (2118920337 : ℕ)^8351*50000000000000^6303 ≤ 16031151969973^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118920337 5000000000 16031151969973 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245320971/5000000000 : ℝ)^8351 ≤ (34620622289879/100000000000000 : ℝ)^6303 := by
    have hnat : (2245320971 : ℕ)^8351*100000000000000^6303 ≤ 34620622289879^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245320971 5000000000 34620622289879 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362426023/10000000000 : ℝ), (2118920337/5000000000 : ℝ), (2245320971/5000000000 : ℝ)] ![(8329268439671/25000000000000 : ℝ), (16031151969973/50000000000000 : ℝ), (34620622289879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362426023/10000000000 : ℝ)|^8351 ≤ (8329268439671/25000000000000 : ℝ)^6303
        have hw : |(4362426023/10000000000 : ℝ)|=(4362426023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118920337/5000000000 : ℝ)|^8351 ≤ (16031151969973/50000000000000 : ℝ)^6303
        have hw : |(2118920337/5000000000 : ℝ)|=(2118920337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245320971/5000000000 : ℝ)|^8351 ≤ (34620622289879/100000000000000 : ℝ)^6303
        have hw : |(2245320971/5000000000 : ℝ)|=(2245320971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159266571/10000000000 : ℝ)*x 0 + (5266350387/10000000000 : ℝ)*x 1 + (1348096121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159266571/10000000000 : ℝ)^8351 ≤ (2624435834647/20000000000000 : ℝ)^6303 := by
    have hnat : (2159266571 : ℕ)^8351*20000000000000^6303 ≤ 2624435834647^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159266571 10000000000 2624435834647 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266350387/10000000000 : ℝ)^8351 ≤ (10689599046333/25000000000000 : ℝ)^6303 := by
    have hnat : (5266350387 : ℕ)^8351*25000000000000^6303 ≤ 10689599046333^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266350387 10000000000 10689599046333 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348096121/2500000000 : ℝ)^8351 ≤ (8823884924541/20000000000000 : ℝ)^6303 := by
    have hnat : (1348096121 : ℕ)^8351*20000000000000^6303 ≤ 8823884924541^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348096121 2500000000 8823884924541 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159266571/10000000000 : ℝ), (5266350387/10000000000 : ℝ), (1348096121/2500000000 : ℝ)] ![(2624435834647/20000000000000 : ℝ), (10689599046333/25000000000000 : ℝ), (8823884924541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159266571/10000000000 : ℝ)|^8351 ≤ (2624435834647/20000000000000 : ℝ)^6303
        have hw : |(-2159266571/10000000000 : ℝ)|=(2159266571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266350387/10000000000 : ℝ)|^8351 ≤ (10689599046333/25000000000000 : ℝ)^6303
        have hw : |(5266350387/10000000000 : ℝ)|=(5266350387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348096121/2500000000 : ℝ)|^8351 ≤ (8823884924541/20000000000000 : ℝ)^6303
        have hw : |(1348096121/2500000000 : ℝ)|=(1348096121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312556133/10000000000 : ℝ)*x 0 + (-2097154929/10000000000 : ℝ)*x 1 + (1348096121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312556133/10000000000 : ℝ)^8351 ≤ (1351754745229/3125000000000 : ℝ)^6303 := by
    have hnat : (5312556133 : ℕ)^8351*3125000000000^6303 ≤ 1351754745229^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312556133 10000000000 1351754745229 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097154929/10000000000 : ℝ)^8351 ≤ (1262442351783/10000000000000 : ℝ)^6303 := by
    have hnat : (2097154929 : ℕ)^8351*10000000000000^6303 ≤ 1262442351783^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097154929 10000000000 1262442351783 10000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348096121/2500000000 : ℝ)^8351 ≤ (8823884924541/20000000000000 : ℝ)^6303 := by
    have hnat : (1348096121 : ℕ)^8351*20000000000000^6303 ≤ 8823884924541^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348096121 2500000000 8823884924541 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312556133/10000000000 : ℝ), (-2097154929/10000000000 : ℝ), (1348096121/2500000000 : ℝ)] ![(1351754745229/3125000000000 : ℝ), (1262442351783/10000000000000 : ℝ), (8823884924541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312556133/10000000000 : ℝ)|^8351 ≤ (1351754745229/3125000000000 : ℝ)^6303
        have hw : |(5312556133/10000000000 : ℝ)|=(5312556133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097154929/10000000000 : ℝ)|^8351 ≤ (1262442351783/10000000000000 : ℝ)^6303
        have hw : |(-2097154929/10000000000 : ℝ)|=(2097154929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348096121/2500000000 : ℝ)|^8351 ≤ (8823884924541/20000000000000 : ℝ)^6303
        have hw : |(1348096121/2500000000 : ℝ)|=(1348096121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312556133/10000000000 : ℝ)*x 0 + (1348096121/2500000000 : ℝ)*x 1 + (-131072183/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312556133/10000000000 : ℝ)^8351 ≤ (1351754745229/3125000000000 : ℝ)^6303 := by
    have hnat : (5312556133 : ℕ)^8351*3125000000000^6303 ≤ 1351754745229^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312556133 10000000000 1351754745229 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348096121/2500000000 : ℝ)^8351 ≤ (8823884924541/20000000000000 : ℝ)^6303 := by
    have hnat : (1348096121 : ℕ)^8351*20000000000000^6303 ≤ 8823884924541^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348096121 2500000000 8823884924541 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131072183/625000000 : ℝ)^8351 ≤ (6312211754927/50000000000000 : ℝ)^6303 := by
    have hnat : (131072183 : ℕ)^8351*50000000000000^6303 ≤ 6312211754927^6303*625000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131072183 625000000 6312211754927 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312556133/10000000000 : ℝ), (1348096121/2500000000 : ℝ), (-131072183/625000000 : ℝ)] ![(1351754745229/3125000000000 : ℝ), (8823884924541/20000000000000 : ℝ), (6312211754927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312556133/10000000000 : ℝ)|^8351 ≤ (1351754745229/3125000000000 : ℝ)^6303
        have hw : |(5312556133/10000000000 : ℝ)|=(5312556133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348096121/2500000000 : ℝ)|^8351 ≤ (8823884924541/20000000000000 : ℝ)^6303
        have hw : |(1348096121/2500000000 : ℝ)|=(1348096121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131072183/625000000 : ℝ)|^8351 ≤ (6312211754927/50000000000000 : ℝ)^6303
        have hw : |(-131072183/625000000 : ℝ)|=(131072183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s8_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362435573/10000000000 : ℝ)*x 0 + (561250859/1250000000 : ℝ)*x 1 + (4238478143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362435573/10000000000 : ℝ)^8351 ≤ (33317170393467/100000000000000 : ℝ)^6303 := by
    have hnat : (4362435573 : ℕ)^8351*100000000000000^6303 ≤ 33317170393467^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362435573 10000000000 33317170393467 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561250859/1250000000 : ℝ)^8351 ≤ (34614135508861/100000000000000 : ℝ)^6303 := by
    have hnat : (561250859 : ℕ)^8351*100000000000000^6303 ≤ 34614135508861^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561250859 1250000000 34614135508861 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238478143/10000000000 : ℝ)^8351 ≤ (16034347044299/50000000000000 : ℝ)^6303 := by
    have hnat : (4238478143 : ℕ)^8351*50000000000000^6303 ≤ 16034347044299^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238478143 10000000000 16034347044299 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362435573/10000000000 : ℝ), (561250859/1250000000 : ℝ), (4238478143/10000000000 : ℝ)] ![(33317170393467/100000000000000 : ℝ), (34614135508861/100000000000000 : ℝ), (16034347044299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362435573/10000000000 : ℝ)|^8351 ≤ (33317170393467/100000000000000 : ℝ)^6303
        have hw : |(4362435573/10000000000 : ℝ)|=(4362435573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561250859/1250000000 : ℝ)|^8351 ≤ (34614135508861/100000000000000 : ℝ)^6303
        have hw : |(561250859/1250000000 : ℝ)|=(561250859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238478143/10000000000 : ℝ)|^8351 ≤ (16034347044299/50000000000000 : ℝ)^6303
        have hw : |(4238478143/10000000000 : ℝ)|=(4238478143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5687/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (1414693607301/10000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^4175 ≤ (1414693607301/10000000000000000 : ℝ)^1024 := by
      have hnat : (11373 : ℕ)^4175*10000000000000000^1024 ≤ 1414693607301^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 1414693607301 10000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (1414693607301/10000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (33580235642850941/100000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^4175 ≤ (33580235642850941/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14059 : ℕ)^4175*100000000000000000000^1024 ≤ 33580235642850941^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 33580235642850941 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (33580235642850941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001414693607301/5000000000000000 : ℝ) ≤ (10000693888194349/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (5001414693607301/5000000000000000 : ℝ)^1024 ≤ (10000693888194349/10000000000000000 : ℝ)^4175 := by
      have hnat : (5001414693607301 : ℕ)^1024*10000000000000000^4175 ≤ 10000693888194349^4175*5000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001414693607301 5000000000000000 10000693888194349 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693888194349/10000000000000000 : ℝ)) (X := (5001414693607301/5000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047727171715860941/100000000000000000000 : ℝ) ≤ (1250146298874407/1250000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (100047727171715860941/100000000000000000000 : ℝ)^1024 ≤ (1250146298874407/1250000000000000 : ℝ)^4175 := by
      have hnat : (100047727171715860941 : ℕ)^1024*1250000000000000^4175 ≤ 1250146298874407^4175*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047727171715860941 100000000000000000000 1250146298874407 1250000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250146298874407/1250000000000000 : ℝ)) (X := (100047727171715860941/100000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033580235642850941/50000000000000000000 : ℝ) ≤ (10001646893796163/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50033580235642850941/50000000000000000000 : ℝ)^1024 ≤ (10001646893796163/10000000000000000 : ℝ)^4175 := by
      have hnat : (50033580235642850941 : ℕ)^1024*10000000000000000^4175 ≤ 10001646893796163^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033580235642850941 50000000000000000000 10001646893796163 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001646893796163/10000000000000000 : ℝ)) (X := (50033580235642850941/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1414693607301/10000000000000000 : ℝ) ≤ ((197434009198386697/197500000000000000 : ℝ)+2*(476502800907/268600000000000 : ℝ)*(11373/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (197434009198386697/197500000000000000 : ℝ)+2*(476502800907/268600000000000 : ℝ)*(11373/100000 : ℝ)=(10000693888194349/10000000000000000 : ℝ) by norm_num, show 1+2*(1414693607301/10000000000000000 : ℝ)=(5001414693607301/5000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33580235642850941/100000000000000000000 : ℝ)+(1414693607301/10000000000000000 : ℝ) ≤ ((197434009198386697/197500000000000000 : ℝ)+(476502800907/268600000000000 : ℝ)*((14059/100000 : ℝ)+(11373/100000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (197434009198386697/197500000000000000 : ℝ)+(476502800907/268600000000000 : ℝ)*((14059/100000 : ℝ)+(11373/100000 : ℝ))=(1250146298874407/1250000000000000 : ℝ) by norm_num, show 1+(33580235642850941/100000000000000000000 : ℝ)+(1414693607301/10000000000000000 : ℝ)=(100047727171715860941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33580235642850941/100000000000000000000 : ℝ) ≤ ((197434009198386697/197500000000000000 : ℝ)+2*(476502800907/268600000000000 : ℝ)*(14059/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (197434009198386697/197500000000000000 : ℝ)+2*(476502800907/268600000000000 : ℝ)*(14059/100000 : ℝ)=(10001646893796163/10000000000000000 : ℝ) by norm_num, show 1+2*(33580235642850941/100000000000000000000 : ℝ)=(50033580235642850941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (197434009198386697/197500000000000000 : ℝ)*(X 1 0+X 2 0)+(476502800907/268600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (197434009198386697/197500000000000000 : ℝ)) (alpha := (476502800907/268600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (197434009198386697/197500000000000000 : ℝ)*(X 0 1+X 2 1)+(476502800907/268600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (197434009198386697/197500000000000000 : ℝ)) (alpha := (476502800907/268600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (197434009198386697/197500000000000000 : ℝ)*(X 0 2+X 1 2)+(476502800907/268600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (197434009198386697/197500000000000000 : ℝ)) (alpha := (476502800907/268600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079630883/5000000000 : ℝ)*X 0 0+(67408799/125000000 : ℝ)*X 0 1+(2633016039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344686799/10000000000 : ℝ)*X 1 0+(-8894029/40000000 : ℝ)*X 1 1+(5266032199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344686873/10000000000 : ℝ)*X 2 0+(42128257/80000000 : ℝ)*X 2 1+(-2223507249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362426023/10000000000 : ℝ)*X 0 0+(2118920337/5000000000 : ℝ)*X 0 1+(2245320971/5000000000 : ℝ)*X 0 2+(4362426023/10000000000 : ℝ)*X 1 0+(2118920337/5000000000 : ℝ)*X 1 1+(2245320971/5000000000 : ℝ)*X 1 2+(4362426023/10000000000 : ℝ)*X 2 0+(2118920337/5000000000 : ℝ)*X 2 1+(2245320971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2159266571/10000000000 : ℝ)*X 0 0+(5266350387/10000000000 : ℝ)*X 0 1+(1348096121/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312556133/10000000000 : ℝ)*X 1 0+(-2097154929/10000000000 : ℝ)*X 1 1+(1348096121/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312556133/10000000000 : ℝ)*X 2 0+(1348096121/2500000000 : ℝ)*X 2 1+(-131072183/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362435573/10000000000 : ℝ)*X 0 0+(561250859/1250000000 : ℝ)*X 0 1+(4238478143/10000000000 : ℝ)*X 0 2+(4362435573/10000000000 : ℝ)*X 1 0+(561250859/1250000000 : ℝ)*X 1 1+(4238478143/10000000000 : ℝ)*X 1 2+(4362435573/10000000000 : ℝ)*X 2 0+(561250859/1250000000 : ℝ)*X 2 1+(4238478143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53586632088192820113970317/4937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140428289/6250000000000 : ℝ)*(base19) + (435886889/20000000000000 : ℝ)*(base23) + (94452563/100000000000000 : ℝ)*(lower2) + (307757897/100000000000000 : ℝ)*(upper3) + (99310033/50000000000000 : ℝ)*(upper5) + (2962572943058513/50000000000000 : ℝ)*(major0) + (2962572943058513/50000000000000 : ℝ)*(major1) + (2962572943058513/50000000000000 : ℝ)*(major2) + (1578896564505251/20000000000000 : ℝ)*(sp0) + (1973636990035273/25000000000000 : ℝ)*(sp1) + (7894548027559271/100000000000000 : ℝ)*(sp2) + (3955706818277379/100000000000000 : ℝ)*(sp3) + (67384467461/100000000000000 : ℝ)*(sp4) + (34385196657/100000000000000 : ℝ)*(sp7) + (988935300868509/25000000000000 : ℝ)*(f.failure) + (1973637551748429/25000000000000 : ℝ)*(f.sum) + (72958146483/839375000000000000000000000 : ℝ)*base66 + (92307438105389037/167875000000000000000000000000000 : ℝ)*base67 + (1670590356890639037/167875000000000000000000000000000 : ℝ)*base69 + (1981308119625485963/167875000000000000000000000000000 : ℝ)*base72 + (18858121676041/6715000000000000000000000000 : ℝ)*base73 + (3361336990785389037/167875000000000000000000000000000 : ℝ)*base75 + (2156255790908889037/167875000000000000000000000000000 : ℝ)*base77 + (874636423735110963/167875000000000000000000000000000 : ℝ)*base80 + (5825675349059/6715000000000000000000000000 : ℝ)*base82 + (98351/9765625000000000000 : ℝ)*base89 + (98351/9765625000000000000 : ℝ)*base91 + (98351/9765625000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (746814944166084901821/85000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1599298739/100000000000000 : ℝ)*(base19) + (870120219/50000000000000 : ℝ)*(base23) + (560243383/100000000000000 : ℝ)*(lower1) + (88325993/50000000000000 : ℝ)*(upper3) + (31990227/50000000000000 : ℝ)*(lower4) + (89677053/50000000000000 : ℝ)*(upper5) + (372186913463537/6250000000000 : ℝ)*(major0) + (372186913463537/6250000000000 : ℝ)*(major1) + (372186913463537/6250000000000 : ℝ)*(major2) + (3391028473/100000000000000 : ℝ)*(sp2) + (7934314819954081/100000000000000 : ℝ)*(sp4) + (3967156610327671/50000000000000 : ℝ)*(sp5) + (793430968868517/10000000000000 : ℝ)*(sp6) + (159026644720419/4000000000000 : ℝ)*(sp7) + (159026644720419/4000000000000 : ℝ)*(f.failure) + (7934314819954081/100000000000000 : ℝ)*(f.sum) + (62514808607/21250000000000000000000000 : ℝ)*base65 + (1410893558630691/33203125000000000000000000000 : ℝ)*base68 + (834878258492861/132812500000000000000000000000 : ℝ)*base69 + (13928117219086611/132812500000000000000000000000 : ℝ)*base71 + (152051008499/42500000000000000000000000 : ℝ)*base73 + (1560614324836611/132812500000000000000000000000 : ℝ)*base75 + (507381044654903/265625000000000000000000000000 : ℝ)*base78 + (1244826632850889/132812500000000000000000000000 : ℝ)*base80 + (28378421253/21250000000000000000000000 : ℝ)*base82 + (24943/3125000000000000000 : ℝ)*base90 + (24943/3125000000000000000 : ℝ)*base92 + (24943/3125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1158_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1158_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1158_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1158_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
