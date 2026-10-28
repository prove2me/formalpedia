-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1295_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:39.031998+00:00
-- url     : https://prove2.me/submissions/d2525c21-797c-46b1-a1c6-a46bb8f7a8fc

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
theorem support_rectangle_w1295_box_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38283987/200000000 : ℝ)*x 0 + (2695943539/5000000000 : ℝ)*x 1 + (5391886859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38283987/200000000 : ℝ)^4255 ≤ (1133515702863/10000000000000 : ℝ)^3231 := by
    have hnat : (38283987 : ℕ)^4255*10000000000000^3231 ≤ 1133515702863^3231*200000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38283987 200000000 1133515702863 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695943539/5000000000 : ℝ)^4255 ≤ (44332422664511/100000000000000 : ℝ)^3231 := by
    have hnat : (2695943539 : ℕ)^4255*100000000000000^3231 ≤ 44332422664511^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695943539 5000000000 44332422664511 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391886859/10000000000 : ℝ)^4255 ≤ (22166210146603/50000000000000 : ℝ)^3231 := by
    have hnat : (5391886859 : ℕ)^4255*50000000000000^3231 ≤ 22166210146603^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391886859 10000000000 22166210146603 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38283987/200000000 : ℝ), (2695943539/5000000000 : ℝ), (5391886859/10000000000 : ℝ)] ![(1133515702863/10000000000000 : ℝ), (44332422664511/100000000000000 : ℝ), (22166210146603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38283987/200000000 : ℝ)|^4255 ≤ (1133515702863/10000000000000 : ℝ)^3231
        have hw : |(-38283987/200000000 : ℝ)|=(38283987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695943539/5000000000 : ℝ)|^4255 ≤ (44332422664511/100000000000000 : ℝ)^3231
        have hw : |(2695943539/5000000000 : ℝ)|=(2695943539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391886859/10000000000 : ℝ)|^4255 ≤ (22166210146603/50000000000000 : ℝ)^3231
        have hw : |(5391886859/10000000000 : ℝ)|=(5391886859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284424527/10000000000 : ℝ)*x 0 + (-2061177201/10000000000 : ℝ)*x 1 + (2695943623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284424527/10000000000 : ℝ)^4255 ≤ (2698282700987/6250000000000 : ℝ)^3231 := by
    have hnat : (5284424527 : ℕ)^4255*6250000000000^3231 ≤ 2698282700987^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284424527 10000000000 2698282700987 6250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061177201/10000000000 : ℝ)^4255 ≤ (156188153563/1250000000000 : ℝ)^3231 := by
    have hnat : (2061177201 : ℕ)^4255*1250000000000^3231 ≤ 156188153563^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061177201 10000000000 156188153563 1250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695943623/5000000000 : ℝ)^4255 ≤ (8866484896719/20000000000000 : ℝ)^3231 := by
    have hnat : (2695943623 : ℕ)^4255*20000000000000^3231 ≤ 8866484896719^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695943623 5000000000 8866484896719 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284424527/10000000000 : ℝ), (-2061177201/10000000000 : ℝ), (2695943623/5000000000 : ℝ)] ![(2698282700987/6250000000000 : ℝ), (156188153563/1250000000000 : ℝ), (8866484896719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284424527/10000000000 : ℝ)|^4255 ≤ (2698282700987/6250000000000 : ℝ)^3231
        have hw : |(5284424527/10000000000 : ℝ)|=(5284424527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061177201/10000000000 : ℝ)|^4255 ≤ (156188153563/1250000000000 : ℝ)^3231
        have hw : |(-2061177201/10000000000 : ℝ)|=(2061177201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695943623/5000000000 : ℝ)|^4255 ≤ (8866484896719/20000000000000 : ℝ)^3231
        have hw : |(2695943623/5000000000 : ℝ)|=(2695943623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165138283/312500000 : ℝ)*x 0 + (5391886897/10000000000 : ℝ)*x 1 + (-1030588481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165138283/312500000 : ℝ)^4255 ≤ (43172528907309/100000000000000 : ℝ)^3231 := by
    have hnat : (165138283 : ℕ)^4255*100000000000000^3231 ≤ 43172528907309^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165138283 312500000 43172528907309 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391886897/10000000000 : ℝ)^4255 ≤ (22166210352333/50000000000000 : ℝ)^3231 := by
    have hnat : (5391886897 : ℕ)^4255*50000000000000^3231 ≤ 22166210352333^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391886897 10000000000 22166210352333 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030588481/5000000000 : ℝ)^4255 ≤ (6247525188509/50000000000000 : ℝ)^3231 := by
    have hnat : (1030588481 : ℕ)^4255*50000000000000^3231 ≤ 6247525188509^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030588481 5000000000 6247525188509 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165138283/312500000 : ℝ), (5391886897/10000000000 : ℝ), (-1030588481/5000000000 : ℝ)] ![(43172528907309/100000000000000 : ℝ), (22166210352333/50000000000000 : ℝ), (6247525188509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165138283/312500000 : ℝ)|^4255 ≤ (43172528907309/100000000000000 : ℝ)^3231
        have hw : |(165138283/312500000 : ℝ)|=(165138283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391886897/10000000000 : ℝ)|^4255 ≤ (22166210352333/50000000000000 : ℝ)^3231
        have hw : |(5391886897/10000000000 : ℝ)|=(5391886897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030588481/5000000000 : ℝ)|^4255 ≤ (6247525188509/50000000000000 : ℝ)^3231
        have hw : |(-1030588481/5000000000 : ℝ)|=(1030588481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (897680977/2000000000 : ℝ)*x 0 + (4268390693/10000000000 : ℝ)*x 1 + (2134195437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897680977/2000000000 : ℝ)^4255 ≤ (6964014028777/20000000000000 : ℝ)^3231 := by
    have hnat : (897680977 : ℕ)^4255*20000000000000^3231 ≤ 6964014028777^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897680977 2000000000 6964014028777 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4268390693/10000000000 : ℝ)^4255 ≤ (32589964008587/100000000000000 : ℝ)^3231 := by
    have hnat : (4268390693 : ℕ)^4255*100000000000000^3231 ≤ 32589964008587^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268390693 10000000000 32589964008587 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134195437/5000000000 : ℝ)^4255 ≤ (32589965828543/100000000000000 : ℝ)^3231 := by
    have hnat : (2134195437 : ℕ)^4255*100000000000000^3231 ≤ 32589965828543^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134195437 5000000000 32589965828543 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897680977/2000000000 : ℝ), (4268390693/10000000000 : ℝ), (2134195437/5000000000 : ℝ)] ![(6964014028777/20000000000000 : ℝ), (32589964008587/100000000000000 : ℝ), (32589965828543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897680977/2000000000 : ℝ)|^4255 ≤ (6964014028777/20000000000000 : ℝ)^3231
        have hw : |(897680977/2000000000 : ℝ)|=(897680977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4268390693/10000000000 : ℝ)|^4255 ≤ (32589964008587/100000000000000 : ℝ)^3231
        have hw : |(4268390693/10000000000 : ℝ)|=(4268390693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2134195437/5000000000 : ℝ)|^4255 ≤ (32589965828543/100000000000000 : ℝ)^3231
        have hw : |(2134195437/5000000000 : ℝ)|=(2134195437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-451826633/2000000000 : ℝ)*x 0 + (2631889261/5000000000 : ℝ)*x 1 + (1052755501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451826633/2000000000 : ℝ)^4255 ≤ (7049475185121/50000000000000 : ℝ)^3231 := by
    have hnat : (451826633 : ℕ)^4255*50000000000000^3231 ≤ 7049475185121^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451826633 2000000000 7049475185121 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631889261/5000000000 : ℝ)^4255 ≤ (42950530274479/100000000000000 : ℝ)^3231 := by
    have hnat : (2631889261 : ℕ)^4255*100000000000000^3231 ≤ 42950530274479^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631889261 5000000000 42950530274479 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052755501/2000000000 : ℝ)^4255 ≤ (10737629836533/25000000000000 : ℝ)^3231 := by
    have hnat : (1052755501 : ℕ)^4255*25000000000000^3231 ≤ 10737629836533^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052755501 2000000000 10737629836533 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451826633/2000000000 : ℝ), (2631889261/5000000000 : ℝ), (1052755501/2000000000 : ℝ)] ![(7049475185121/50000000000000 : ℝ), (42950530274479/100000000000000 : ℝ), (10737629836533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451826633/2000000000 : ℝ)|^4255 ≤ (7049475185121/50000000000000 : ℝ)^3231
        have hw : |(-451826633/2000000000 : ℝ)|=(451826633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631889261/5000000000 : ℝ)|^4255 ≤ (42950530274479/100000000000000 : ℝ)^3231
        have hw : |(2631889261/5000000000 : ℝ)|=(2631889261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052755501/2000000000 : ℝ)|^4255 ≤ (10737629836533/25000000000000 : ℝ)^3231
        have hw : |(1052755501/2000000000 : ℝ)|=(1052755501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343646671/2500000000 : ℝ)*x 0 + (-66007447/312500000 : ℝ)*x 1 + (1052755627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343646671/2500000000 : ℝ)^4255 ≤ (22072595727591/50000000000000 : ℝ)^3231 := by
    have hnat : (1343646671 : ℕ)^4255*50000000000000^3231 ≤ 22072595727591^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343646671 2500000000 22072595727591 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66007447/312500000 : ℝ)^4255 ≤ (12904282415197/100000000000000 : ℝ)^3231 := by
    have hnat : (66007447 : ℕ)^4255*100000000000000^3231 ≤ 12904282415197^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66007447 312500000 12904282415197 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052755627/2000000000 : ℝ)^4255 ≤ (8590105223181/20000000000000 : ℝ)^3231 := by
    have hnat : (1052755627 : ℕ)^4255*20000000000000^3231 ≤ 8590105223181^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052755627 2000000000 8590105223181 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343646671/2500000000 : ℝ), (-66007447/312500000 : ℝ), (1052755627/2000000000 : ℝ)] ![(22072595727591/50000000000000 : ℝ), (12904282415197/100000000000000 : ℝ), (8590105223181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343646671/2500000000 : ℝ)|^4255 ≤ (22072595727591/50000000000000 : ℝ)^3231
        have hw : |(1343646671/2500000000 : ℝ)|=(1343646671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66007447/312500000 : ℝ)|^4255 ≤ (12904282415197/100000000000000 : ℝ)^3231
        have hw : |(-66007447/312500000 : ℝ)|=(66007447/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052755627/2000000000 : ℝ)|^4255 ≤ (8590105223181/20000000000000 : ℝ)^3231
        have hw : |(1052755627/2000000000 : ℝ)|=(1052755627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343646733/2500000000 : ℝ)*x 0 + (5263778443/10000000000 : ℝ)*x 1 + (-1056118779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343646733/2500000000 : ℝ)^4255 ≤ (22072597068881/50000000000000 : ℝ)^3231 := by
    have hnat : (1343646733 : ℕ)^4255*50000000000000^3231 ≤ 22072597068881^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343646733 2500000000 22072597068881 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263778443/10000000000 : ℝ)^4255 ≤ (42950529425571/100000000000000 : ℝ)^3231 := by
    have hnat : (5263778443 : ℕ)^4255*100000000000000^3231 ≤ 42950529425571^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263778443 10000000000 42950529425571 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056118779/5000000000 : ℝ)^4255 ≤ (201629318957/1562500000000 : ℝ)^3231 := by
    have hnat : (1056118779 : ℕ)^4255*1562500000000^3231 ≤ 201629318957^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056118779 5000000000 201629318957 1562500000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343646733/2500000000 : ℝ), (5263778443/10000000000 : ℝ), (-1056118779/5000000000 : ℝ)] ![(22072597068881/50000000000000 : ℝ), (42950529425571/100000000000000 : ℝ), (201629318957/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343646733/2500000000 : ℝ)|^4255 ≤ (22072597068881/50000000000000 : ℝ)^3231
        have hw : |(1343646733/2500000000 : ℝ)|=(1343646733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263778443/10000000000 : ℝ)|^4255 ≤ (42950529425571/100000000000000 : ℝ)^3231
        have hw : |(5263778443/10000000000 : ℝ)|=(5263778443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056118779/5000000000 : ℝ)|^4255 ≤ (201629318957/1562500000000 : ℝ)^3231
        have hw : |(-1056118779/5000000000 : ℝ)|=(1056118779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2094433789/5000000000 : ℝ)*x 0 + (2209052463/5000000000 : ℝ)*x 1 + (4418103453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094433789/5000000000 : ℝ)^4255 ≤ (31792729408363/100000000000000 : ℝ)^3231 := by
    have hnat : (2094433789 : ℕ)^4255*100000000000000^3231 ≤ 31792729408363^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094433789 5000000000 31792729408363 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209052463/5000000000 : ℝ)^4255 ≤ (17051821386459/50000000000000 : ℝ)^3231 := by
    have hnat : (2209052463 : ℕ)^4255*50000000000000^3231 ≤ 17051821386459^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209052463 5000000000 17051821386459 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418103453/10000000000 : ℝ)^4255 ≤ (17051813899593/50000000000000 : ℝ)^3231 := by
    have hnat : (4418103453 : ℕ)^4255*50000000000000^3231 ≤ 17051813899593^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418103453 10000000000 17051813899593 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094433789/5000000000 : ℝ), (2209052463/5000000000 : ℝ), (4418103453/10000000000 : ℝ)] ![(31792729408363/100000000000000 : ℝ), (17051821386459/50000000000000 : ℝ), (17051813899593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094433789/5000000000 : ℝ)|^4255 ≤ (31792729408363/100000000000000 : ℝ)^3231
        have hw : |(2094433789/5000000000 : ℝ)|=(2094433789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209052463/5000000000 : ℝ)|^4255 ≤ (17051821386459/50000000000000 : ℝ)^3231
        have hw : |(2209052463/5000000000 : ℝ)|=(2209052463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418103453/10000000000 : ℝ)|^4255 ≤ (17051813899593/50000000000000 : ℝ)^3231
        have hw : |(4418103453/10000000000 : ℝ)|=(4418103453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_8 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17084609/78125000 : ℝ)*x 0 + (1293953063/2500000000 : ℝ)*x 1 + (2702961821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17084609/78125000 : ℝ)^4255 ≤ (13507741953087/100000000000000 : ℝ)^3231 := by
    have hnat : (17084609 : ℕ)^4255*100000000000000^3231 ≤ 13507741953087^3231*78125000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17084609 78125000 13507741953087 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293953063/2500000000 : ℝ)^4255 ≤ (42007786527159/100000000000000 : ℝ)^3231 := by
    have hnat : (1293953063 : ℕ)^4255*100000000000000^3231 ≤ 42007786527159^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293953063 2500000000 42007786527159 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702961821/5000000000 : ℝ)^4255 ≤ (22242235751869/50000000000000 : ℝ)^3231 := by
    have hnat : (2702961821 : ℕ)^4255*50000000000000^3231 ≤ 22242235751869^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702961821 5000000000 22242235751869 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17084609/78125000 : ℝ), (1293953063/2500000000 : ℝ), (2702961821/5000000000 : ℝ)] ![(13507741953087/100000000000000 : ℝ), (42007786527159/100000000000000 : ℝ), (22242235751869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17084609/78125000 : ℝ)|^4255 ≤ (13507741953087/100000000000000 : ℝ)^3231
        have hw : |(-17084609/78125000 : ℝ)|=(17084609/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293953063/2500000000 : ℝ)|^4255 ≤ (42007786527159/100000000000000 : ℝ)^3231
        have hw : |(1293953063/2500000000 : ℝ)|=(1293953063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702961821/5000000000 : ℝ)|^4255 ≤ (22242235751869/50000000000000 : ℝ)^3231
        have hw : |(2702961821/5000000000 : ℝ)|=(2702961821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_9 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274540577/10000000000 : ℝ)*x 0 + (-256930859/1250000000 : ℝ)*x 1 + (5405922723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274540577/10000000000 : ℝ)^4255 ≤ (68905941159/160000000000 : ℝ)^3231 := by
    have hnat : (5274540577 : ℕ)^4255*160000000000^3231 ≤ 68905941159^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274540577 10000000000 68905941159 160000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256930859/1250000000 : ℝ)^4255 ≤ (12449325210403/100000000000000 : ℝ)^3231 := by
    have hnat : (256930859 : ℕ)^4255*100000000000000^3231 ≤ 12449325210403^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256930859 1250000000 12449325210403 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405922723/10000000000 : ℝ)^4255 ≤ (44484461544717/100000000000000 : ℝ)^3231 := by
    have hnat : (5405922723 : ℕ)^4255*100000000000000^3231 ≤ 44484461544717^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405922723 10000000000 44484461544717 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274540577/10000000000 : ℝ), (-256930859/1250000000 : ℝ), (5405922723/10000000000 : ℝ)] ![(68905941159/160000000000 : ℝ), (12449325210403/100000000000000 : ℝ), (44484461544717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274540577/10000000000 : ℝ)|^4255 ≤ (68905941159/160000000000 : ℝ)^3231
        have hw : |(5274540577/10000000000 : ℝ)|=(5274540577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256930859/1250000000 : ℝ)|^4255 ≤ (12449325210403/100000000000000 : ℝ)^3231
        have hw : |(-256930859/1250000000 : ℝ)|=(256930859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405922723/10000000000 : ℝ)|^4255 ≤ (44484461544717/100000000000000 : ℝ)^3231
        have hw : |(5405922723/10000000000 : ℝ)|=(5405922723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_10 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637270021/5000000000 : ℝ)*x 0 + (216236947/400000000 : ℝ)*x 1 + (-2055446301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637270021/5000000000 : ℝ)^4255 ≤ (43066207471719/100000000000000 : ℝ)^3231 := by
    have hnat : (2637270021 : ℕ)^4255*100000000000000^3231 ≤ 43066207471719^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637270021 5000000000 43066207471719 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216236947/400000000 : ℝ)^4255 ≤ (5560558982669/12500000000000 : ℝ)^3231 := by
    have hnat : (216236947 : ℕ)^4255*12500000000000^3231 ≤ 5560558982669^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216236947 400000000 5560558982669 12500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055446301/10000000000 : ℝ)^4255 ≤ (12449320655929/100000000000000 : ℝ)^3231 := by
    have hnat : (2055446301 : ℕ)^4255*100000000000000^3231 ≤ 12449320655929^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055446301 10000000000 12449320655929 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637270021/5000000000 : ℝ), (216236947/400000000 : ℝ), (-2055446301/10000000000 : ℝ)] ![(43066207471719/100000000000000 : ℝ), (5560558982669/12500000000000 : ℝ), (12449320655929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637270021/5000000000 : ℝ)|^4255 ≤ (43066207471719/100000000000000 : ℝ)^3231
        have hw : |(2637270021/5000000000 : ℝ)|=(2637270021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216236947/400000000 : ℝ)|^4255 ≤ (5560558982669/12500000000000 : ℝ)^3231
        have hw : |(216236947/400000000 : ℝ)|=(216236947/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055446301/10000000000 : ℝ)|^4255 ≤ (12449320655929/100000000000000 : ℝ)^3231
        have hw : |(-2055446301/10000000000 : ℝ)|=(2055446301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_11 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4520664341/10000000000 : ℝ)*x 0 + (531496611/1250000000 : ℝ)*x 1 + (2125986973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4520664341/10000000000 : ℝ)^4255 ≤ (17575011087357/50000000000000 : ℝ)^3231 := by
    have hnat : (4520664341 : ℕ)^4255*50000000000000^3231 ≤ 17575011087357^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520664341 10000000000 17575011087357 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531496611/1250000000 : ℝ)^4255 ≤ (16212491796303/50000000000000 : ℝ)^3231 := by
    have hnat : (531496611 : ℕ)^4255*50000000000000^3231 ≤ 16212491796303^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531496611 1250000000 16212491796303 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125986973/5000000000 : ℝ)^4255 ≤ (16212497108909/50000000000000 : ℝ)^3231 := by
    have hnat : (2125986973 : ℕ)^4255*50000000000000^3231 ≤ 16212497108909^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125986973 5000000000 16212497108909 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4520664341/10000000000 : ℝ), (531496611/1250000000 : ℝ), (2125986973/5000000000 : ℝ)] ![(17575011087357/50000000000000 : ℝ), (16212491796303/50000000000000 : ℝ), (16212497108909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4520664341/10000000000 : ℝ)|^4255 ≤ (17575011087357/50000000000000 : ℝ)^3231
        have hw : |(4520664341/10000000000 : ℝ)|=(4520664341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531496611/1250000000 : ℝ)|^4255 ≤ (16212491796303/50000000000000 : ℝ)^3231
        have hw : |(531496611/1250000000 : ℝ)|=(531496611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125986973/5000000000 : ℝ)|^4255 ≤ (16212497108909/50000000000000 : ℝ)^3231
        have hw : |(2125986973/5000000000 : ℝ)|=(2125986973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_12 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986935199/10000000000 : ℝ)*x 0 + (2738768131/5000000000 : ℝ)*x 1 + (2626376323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986935199/10000000000 : ℝ)^4255 ≤ (11905763323161/100000000000000 : ℝ)^3231 := by
    have hnat : (1986935199 : ℕ)^4255*100000000000000^3231 ≤ 11905763323161^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986935199 10000000000 11905763323161 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738768131/5000000000 : ℝ)^4255 ≤ (22631073738869/50000000000000 : ℝ)^3231 := by
    have hnat : (2738768131 : ℕ)^4255*50000000000000^3231 ≤ 22631073738869^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738768131 5000000000 22631073738869 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626376323/5000000000 : ℝ)^4255 ≤ (42832089187621/100000000000000 : ℝ)^3231 := by
    have hnat : (2626376323 : ℕ)^4255*100000000000000^3231 ≤ 42832089187621^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626376323 5000000000 42832089187621 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986935199/10000000000 : ℝ), (2738768131/5000000000 : ℝ), (2626376323/5000000000 : ℝ)] ![(11905763323161/100000000000000 : ℝ), (22631073738869/50000000000000 : ℝ), (42832089187621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986935199/10000000000 : ℝ)|^4255 ≤ (11905763323161/100000000000000 : ℝ)^3231
        have hw : |(-1986935199/10000000000 : ℝ)|=(1986935199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738768131/5000000000 : ℝ)|^4255 ≤ (22631073738869/50000000000000 : ℝ)^3231
        have hw : |(2738768131/5000000000 : ℝ)|=(2738768131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626376323/5000000000 : ℝ)|^4255 ≤ (42832089187621/100000000000000 : ℝ)^3231
        have hw : |(2626376323/5000000000 : ℝ)|=(2626376323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_13 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269117197/500000000 : ℝ)*x 0 + (-2116526781/10000000000 : ℝ)*x 1 + (262637607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269117197/500000000 : ℝ)^4255 ≤ (22114559870139/50000000000000 : ℝ)^3231 := by
    have hnat : (269117197 : ℕ)^4255*50000000000000^3231 ≤ 22114559870139^3231*500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269117197 500000000 22114559870139 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116526781/10000000000 : ℝ)^4255 ≤ (1293879649317/10000000000000 : ℝ)^3231 := by
    have hnat : (2116526781 : ℕ)^4255*10000000000000^3231 ≤ 1293879649317^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116526781 10000000000 1293879649317 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262637607/500000000 : ℝ)^4255 ≤ (10708020938481/25000000000000 : ℝ)^3231 := by
    have hnat : (262637607 : ℕ)^4255*25000000000000^3231 ≤ 10708020938481^3231*500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262637607 500000000 10708020938481 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269117197/500000000 : ℝ), (-2116526781/10000000000 : ℝ), (262637607/500000000 : ℝ)] ![(22114559870139/50000000000000 : ℝ), (1293879649317/10000000000000 : ℝ), (10708020938481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269117197/500000000 : ℝ)|^4255 ≤ (22114559870139/50000000000000 : ℝ)^3231
        have hw : |(269117197/500000000 : ℝ)|=(269117197/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116526781/10000000000 : ℝ)|^4255 ≤ (1293879649317/10000000000000 : ℝ)^3231
        have hw : |(-2116526781/10000000000 : ℝ)|=(2116526781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262637607/500000000 : ℝ)|^4255 ≤ (10708020938481/25000000000000 : ℝ)^3231
        have hw : |(262637607/500000000 : ℝ)|=(262637607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_14 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382343969/10000000000 : ℝ)*x 0 + (328297043/625000000 : ℝ)*x 1 + (-211652601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382343969/10000000000 : ℝ)^4255 ≤ (4422912005411/10000000000000 : ℝ)^3231 := by
    have hnat : (5382343969 : ℕ)^4255*10000000000000^3231 ≤ 4422912005411^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382343969 10000000000 4422912005411 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328297043/625000000 : ℝ)^4255 ≤ (42832089638639/100000000000000 : ℝ)^3231 := by
    have hnat : (328297043 : ℕ)^4255*100000000000000^3231 ≤ 42832089638639^3231*625000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328297043 625000000 42832089638639 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211652601/1000000000 : ℝ)^4255 ≤ (12938790286093/100000000000000 : ℝ)^3231 := by
    have hnat : (211652601 : ℕ)^4255*100000000000000^3231 ≤ 12938790286093^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211652601 1000000000 12938790286093 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382343969/10000000000 : ℝ), (328297043/625000000 : ℝ), (-211652601/1000000000 : ℝ)] ![(4422912005411/10000000000000 : ℝ), (42832089638639/100000000000000 : ℝ), (12938790286093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382343969/10000000000 : ℝ)|^4255 ≤ (4422912005411/10000000000000 : ℝ)^3231
        have hw : |(5382343969/10000000000 : ℝ)|=(5382343969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328297043/625000000 : ℝ)|^4255 ≤ (42832089638639/100000000000000 : ℝ)^3231
        have hw : |(328297043/625000000 : ℝ)|=(328297043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211652601/1000000000 : ℝ)|^4255 ≤ (12938790286093/100000000000000 : ℝ)^3231
        have hw : |(-211652601/1000000000 : ℝ)|=(211652601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_box_15 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208132019/500000000 : ℝ)*x 0 + (443097947/1000000000 : ℝ)*x 1 + (886195889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208132019/500000000 : ℝ)^4255 ≤ (7882710599599/25000000000000 : ℝ)^3231 := by
    have hnat : (208132019 : ℕ)^4255*25000000000000^3231 ≤ 7882710599599^3231*500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208132019 500000000 7882710599599 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443097947/1000000000 : ℝ)^4255 ≤ (34234578924893/100000000000000 : ℝ)^3231 := by
    have hnat : (443097947 : ℕ)^4255*100000000000000^3231 ≤ 34234578924893^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443097947 1000000000 34234578924893 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886195889/2000000000 : ℝ)^4255 ≤ (17117289335261/50000000000000 : ℝ)^3231 := by
    have hnat : (886195889 : ℕ)^4255*50000000000000^3231 ≤ 17117289335261^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886195889 2000000000 17117289335261 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208132019/500000000 : ℝ), (443097947/1000000000 : ℝ), (886195889/2000000000 : ℝ)] ![(7882710599599/25000000000000 : ℝ), (34234578924893/100000000000000 : ℝ), (17117289335261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208132019/500000000 : ℝ)|^4255 ≤ (7882710599599/25000000000000 : ℝ)^3231
        have hw : |(208132019/500000000 : ℝ)|=(208132019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443097947/1000000000 : ℝ)|^4255 ≤ (34234578924893/100000000000000 : ℝ)^3231
        have hw : |(443097947/1000000000 : ℝ)|=(443097947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886195889/2000000000 : ℝ)|^4255 ≤ (17117289335261/50000000000000 : ℝ)^3231
        have hw : |(886195889/2000000000 : ℝ)|=(886195889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1571/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58851/100000 : ℝ) ∧ (3187/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84167/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2759/25000 : ℝ) ^ (2127/512 : ℝ) ≤ (5278683299789761/50000000000000000000 : ℝ) := by
    have hpowers : (2759/25000 : ℝ)^2127 ≤ (5278683299789761/50000000000000000000 : ℝ)^512 := by
      have hnat : (2759 : ℕ)^2127*50000000000000000000^512 ≤ 5278683299789761^512*25000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2759 25000 5278683299789761 50000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2759/25000 : ℝ)) (X := (5278683299789761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7337/50000 : ℝ) ^ (2127/512 : ℝ) ≤ (8620552636847443/25000000000000000000 : ℝ) := by
    have hpowers : (7337/50000 : ℝ)^2127 ≤ (8620552636847443/25000000000000000000 : ℝ)^512 := by
      have hnat : (7337 : ℕ)^2127*25000000000000000000^512 ≤ 8620552636847443^512*50000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7337 50000 8620552636847443 25000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7337/50000 : ℝ)) (X := (8620552636847443/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005278683299789761/25000000000000000000 : ℝ) ≤ (10000508221763527/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (25005278683299789761/25000000000000000000 : ℝ)^512 ≤ (10000508221763527/10000000000000000 : ℝ)^2127 := by
      have hnat : (25005278683299789761 : ℕ)^512*10000000000000000^2127 ≤ 10000508221763527^2127*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005278683299789761 25000000000000000000 10000508221763527 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000508221763527/10000000000000000 : ℝ)) (X := (25005278683299789761/25000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022519788573484647/50000000000000000000 : ℝ) ≤ (10001083983144257/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (50022519788573484647/50000000000000000000 : ℝ)^512 ≤ (10001083983144257/10000000000000000 : ℝ)^2127 := by
      have hnat : (50022519788573484647 : ℕ)^512*10000000000000000^2127 ≤ 10001083983144257^2127*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022519788573484647 50000000000000000000 10001083983144257 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001083983144257/10000000000000000 : ℝ)) (X := (50022519788573484647/50000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508620552636847443/12500000000000000000 : ℝ) ≤ (10001659744524987/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (12508620552636847443/12500000000000000000 : ℝ)^512 ≤ (10001659744524987/10000000000000000 : ℝ)^2127 := by
      have hnat : (12508620552636847443 : ℕ)^512*10000000000000000^2127 ≤ 10001659744524987^2127*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508620552636847443 12500000000000000000 10001659744524987 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001659744524987/10000000000000000 : ℝ)) (X := (12508620552636847443/12500000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5278683299789761/50000000000000000000 : ℝ) ≤ ((18184570352790119333/18190000000000000000 : ℝ)+2*(57576138073/36380000000000 : ℝ)*(2759/25000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (18184570352790119333/18190000000000000000 : ℝ)+2*(57576138073/36380000000000 : ℝ)*(2759/25000 : ℝ)=(10000508221763527/10000000000000000 : ℝ) by norm_num, show 1+2*(5278683299789761/50000000000000000000 : ℝ)=(25005278683299789761/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8620552636847443/25000000000000000000 : ℝ)+(5278683299789761/50000000000000000000 : ℝ) ≤ ((18184570352790119333/18190000000000000000 : ℝ)+(57576138073/36380000000000 : ℝ)*((7337/50000 : ℝ)+(2759/25000 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (18184570352790119333/18190000000000000000 : ℝ)+(57576138073/36380000000000 : ℝ)*((7337/50000 : ℝ)+(2759/25000 : ℝ))=(10001083983144257/10000000000000000 : ℝ) by norm_num, show 1+(8620552636847443/25000000000000000000 : ℝ)+(5278683299789761/50000000000000000000 : ℝ)=(50022519788573484647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8620552636847443/25000000000000000000 : ℝ) ≤ ((18184570352790119333/18190000000000000000 : ℝ)+2*(57576138073/36380000000000 : ℝ)*(7337/50000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (18184570352790119333/18190000000000000000 : ℝ)+2*(57576138073/36380000000000 : ℝ)*(7337/50000 : ℝ)=(10001659744524987/10000000000000000 : ℝ) by norm_num, show 1+2*(8620552636847443/25000000000000000000 : ℝ)=(12508620552636847443/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18184570352790119333/18190000000000000000 : ℝ)*(X 1 0+X 2 0)+(57576138073/36380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (18184570352790119333/18190000000000000000 : ℝ)) (alpha := (57576138073/36380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18184570352790119333/18190000000000000000 : ℝ)*(X 0 1+X 2 1)+(57576138073/36380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (18184570352790119333/18190000000000000000 : ℝ)) (alpha := (57576138073/36380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18184570352790119333/18190000000000000000 : ℝ)*(X 0 2+X 1 2)+(57576138073/36380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (18184570352790119333/18190000000000000000 : ℝ)) (alpha := (57576138073/36380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-38283987/200000000 : ℝ)*X 0 0+(2695943539/5000000000 : ℝ)*X 0 1+(5391886859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284424527/10000000000 : ℝ)*X 1 0+(-2061177201/10000000000 : ℝ)*X 1 1+(2695943623/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((165138283/312500000 : ℝ)*X 2 0+(5391886897/10000000000 : ℝ)*X 2 1+(-1030588481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((897680977/2000000000 : ℝ)*X 0 0+(4268390693/10000000000 : ℝ)*X 0 1+(2134195437/5000000000 : ℝ)*X 0 2+(897680977/2000000000 : ℝ)*X 1 0+(4268390693/10000000000 : ℝ)*X 1 1+(2134195437/5000000000 : ℝ)*X 1 2+(897680977/2000000000 : ℝ)*X 2 0+(4268390693/10000000000 : ℝ)*X 2 1+(2134195437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-451826633/2000000000 : ℝ)*X 0 0+(2631889261/5000000000 : ℝ)*X 0 1+(1052755501/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343646671/2500000000 : ℝ)*X 1 0+(-66007447/312500000 : ℝ)*X 1 1+(1052755627/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343646733/2500000000 : ℝ)*X 2 0+(5263778443/10000000000 : ℝ)*X 2 1+(-1056118779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2094433789/5000000000 : ℝ)*X 0 0+(2209052463/5000000000 : ℝ)*X 0 1+(4418103453/10000000000 : ℝ)*X 0 2+(2094433789/5000000000 : ℝ)*X 1 0+(2209052463/5000000000 : ℝ)*X 1 1+(4418103453/10000000000 : ℝ)*X 1 2+(2094433789/5000000000 : ℝ)*X 2 0+(2209052463/5000000000 : ℝ)*X 2 1+(4418103453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-17084609/78125000 : ℝ)*X 0 0+(1293953063/2500000000 : ℝ)*X 0 1+(2702961821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274540577/10000000000 : ℝ)*X 1 0+(-256930859/1250000000 : ℝ)*X 1 1+(5405922723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637270021/5000000000 : ℝ)*X 2 0+(216236947/400000000 : ℝ)*X 2 1+(-2055446301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4520664341/10000000000 : ℝ)*X 0 0+(531496611/1250000000 : ℝ)*X 0 1+(2125986973/5000000000 : ℝ)*X 0 2+(4520664341/10000000000 : ℝ)*X 1 0+(531496611/1250000000 : ℝ)*X 1 1+(2125986973/5000000000 : ℝ)*X 1 2+(4520664341/10000000000 : ℝ)*X 2 0+(531496611/1250000000 : ℝ)*X 2 1+(2125986973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1986935199/10000000000 : ℝ)*X 0 0+(2738768131/5000000000 : ℝ)*X 0 1+(2626376323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((269117197/500000000 : ℝ)*X 1 0+(-2116526781/10000000000 : ℝ)*X 1 1+(262637607/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382343969/10000000000 : ℝ)*X 2 0+(328297043/625000000 : ℝ)*X 2 1+(-211652601/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((208132019/500000000 : ℝ)*X 0 0+(443097947/1000000000 : ℝ)*X 0 1+(886195889/2000000000 : ℝ)*X 0 2+(208132019/500000000 : ℝ)*X 1 0+(443097947/1000000000 : ℝ)*X 1 1+(886195889/2000000000 : ℝ)*X 1 2+(208132019/500000000 : ℝ)*X 2 0+(443097947/1000000000 : ℝ)*X 2 1+(886195889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1571/2500 : ℝ) ≤ (-5715063030190023469983914670777/9095000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112626669/100000000000000 : ℝ)*(upper1) + (62071947/25000000000000 : ℝ)*(lower2) + (74128959/100000000000000 : ℝ)*(upper4) + (57352068021777/2000000000000 : ℝ)*(major0) + (57352068021777/2000000000000 : ℝ)*(major1) + (57352068021777/2000000000000 : ℝ)*(major2) + (252923083/4000000000000 : ℝ)*(sp1) + (2225703229/100000000000000 : ℝ)*(sp3) + (388039599531269/10000000000000 : ℝ)*(sp4) + (388042049248479/10000000000000 : ℝ)*(sp5) + (1940104363609363/50000000000000 : ℝ)*(sp6) + (234465445801353/12500000000000 : ℝ)*(sp7) + (1232809967/4000000000000 : ℝ)*(sp8) + (218088343139/100000000000000 : ℝ)*(sp14) + (1875725792114053/100000000000000 : ℝ)*(f.failure) + (485053351945233/12500000000000 : ℝ)*(f.sum) + (11108204895803/1819000000000000000000000000 : ℝ)*base66 + (4445688809225573/2140000000000000000000000000000 : ℝ)*base67 + (1606954975154427/2140000000000000000000000000000 : ℝ)*base70 + (10865133407714427/2140000000000000000000000000000 : ℝ)*base72 + (112486130627/227375000000000000000000000 : ℝ)*base73 + (12441814137154427/2140000000000000000000000000000 : ℝ)*base76 + (628470025034427/2140000000000000000000000000000 : ℝ)*base78 + (175416426574427/2140000000000000000000000000000 : ℝ)*base80 + (423632563743/181900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2500251/1000000000000000000000 : ℝ)*base89 + (2500251/1000000000000000000000 : ℝ)*base91 + (2500251/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58851/100000 : ℝ) ≤ (33454440135843771099983295208977/56843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3882069/10000000000000 : ℝ)*(upper0) + (93772327/100000000000000 : ℝ)*(lower1) + (200994417/100000000000000 : ℝ)*(upper4) + (366840714587523/12500000000000 : ℝ)*(major0) + (366840714587523/12500000000000 : ℝ)*(major1) + (366840714587523/12500000000000 : ℝ)*(major2) + (1965099513728279/50000000000000 : ℝ)*(sp0) + (1965099185795627/50000000000000 : ℝ)*(sp1) + (1965099569171627/50000000000000 : ℝ)*(sp2) + (1919624736538357/100000000000000 : ℝ)*(sp3) + (1042012787/25000000000000 : ℝ)*(sp5) + (850324787/25000000000000 : ℝ)*(sp6) + (702437169/20000000000000 : ℝ)*(sp8) + (3190169751/50000000000000 : ℝ)*(sp11) + (959815558438929/50000000000000 : ℝ)*(f.failure) + (1965101269821201/50000000000000 : ℝ)*(f.sum) + (7788409206479/1819000000000000000000000000 : ℝ)*base65 + (125502201808234873/13375000000000000000000000000000 : ℝ)*base68 + (124500736391609873/13375000000000000000000000000000 : ℝ)*base70 + (8854929012234873/13375000000000000000000000000000 : ℝ)*base72 + (11716099772857/1819000000000000000000000000 : ℝ)*base74 + (13061450887890127/13375000000000000000000000000000 : ℝ)*base75 + (55690247698484873/13375000000000000000000000000000 : ℝ)*base78 + (190091132603984873/13375000000000000000000000000000 : ℝ)*base80 + (56961974389/36380000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1932657/500000000000000000000 : ℝ)*base90 + (1932657/500000000000000000000 : ℝ)*base92 + (1932657/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (3187/4000 : ℝ) ≤ (724664613089669178229259479142001/909500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156525607/100000000000000 : ℝ)*(upper0) + (166331791/100000000000000 : ℝ)*(lower3) + (26415557/100000000000000 : ℝ)*(upper4) + (649727230882589/20000000000000 : ℝ)*(major0) + (649727230882589/20000000000000 : ℝ)*(major1) + (1624318077206473/50000000000000 : ℝ)*(major2) + (56545657/10000000000000 : ℝ)*(sp0) + (261924971441/100000000000000 : ℝ)*(sp2) + (64929710211/100000000000000 : ℝ)*(sp3) + (434573467146569/10000000000000 : ℝ)*(sp8) + (1086437599911527/25000000000000 : ℝ)*(sp9) + (1086372118668667/25000000000000 : ℝ)*(sp10) + (2124897895244177/100000000000000 : ℝ)*(sp11) + (1895340481/12500000000000 : ℝ)*(sp12) + (531240706238597/25000000000000 : ℝ)*(f.failure) + (1086437599911527/25000000000000 : ℝ)*(f.sum) + (6097737095563/3638000000000000000000000000 : ℝ)*base65 + (1198422378850793137/363800000000000000000000000000000 : ℝ)*base67 + (5687589648993292509/909500000000000000000000000000000 : ℝ)*base69 + (8710378391502606863/363800000000000000000000000000000 : ℝ)*base72 + (10333996633231/3638000000000000000000000000 : ℝ)*base74 + (7720000489766292509/909500000000000000000000000000000 : ℝ)*base75 + (108419891795688639/21400000000000000000000000000000 : ℝ)*base78 + (172220953680488639/21400000000000000000000000000000 : ℝ)*base80 + (10335036777189/1819000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2562299/250000000000000000000 : ℝ)*base89 + (2562299/250000000000000000000 : ℝ)*base91 + (62299/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84167/100000 : ℝ) ≤ (-382736983568556303011228059676103/454750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67304913/50000000000000 : ℝ)*(lower1) + (77751037/25000000000000 : ℝ)*(lower2) + (19097879/50000000000000 : ℝ)*(upper5) + (1642283907050103/50000000000000 : ℝ)*(major0) + (1642283907050103/50000000000000 : ℝ)*(major1) + (1642283907050103/50000000000000 : ℝ)*(major2) + (5232332641/100000000000000 : ℝ)*(sp0) + (196134192343/50000000000000 : ℝ)*(sp5) + (159591367/2000000000000 : ℝ)*(sp6) + (127770914183/100000000000000 : ℝ)*(sp7) + (1112179773894169/25000000000000 : ℝ)*(sp12) + (444833205952463/10000000000000 : ℝ)*(sp13) + (2224358174170483/50000000000000 : ℝ)*(sp14) + (537084570883141/25000000000000 : ℝ)*(sp15) + (1074233027223373/50000000000000 : ℝ)*(f.failure) + (1112181081977329/25000000000000 : ℝ)*(f.sum) + (726837843071/909500000000000000000000000 : ℝ)*base66 + (276369011424503453/53500000000000000000000000000000 : ℝ)*base68 + (416309258135503453/53500000000000000000000000000000 : ℝ)*base70 + (4299676469503453/53500000000000000000000000000000 : ℝ)*base72 + (4991580426739/909500000000000000000000000 : ℝ)*base74 + (179076218881996547/53500000000000000000000000000000 : ℝ)*base75 + (33676077125496547/53500000000000000000000000000000 : ℝ)*base77 + (130589940242503453/53500000000000000000000000000000 : ℝ)*base80 + (16294741523623/1819000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1947309/500000000000000000000 : ℝ)*base90 + (1947309/500000000000000000000 : ℝ)*base92 + (1947309/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1295_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58851/100000 : ℝ) else (3187/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84167/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1295_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1295_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58851/100000 : ℝ) else (3187/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84167/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1295_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58851/100000 : ℝ) else (3187/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84167/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1295_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
