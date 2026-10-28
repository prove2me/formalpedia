-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1149_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:35:09.771729+00:00
-- url     : https://prove2.me/submissions/c468fba4-16e7-4b29-8d17-2526c520428e

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
theorem support_rectangle_w1149_s3_0 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079909839/5000000000 : ℝ)*x 0 + (5428451333/10000000000 : ℝ)*x 1 + (5232745689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079909839/5000000000 : ℝ)^4171 ≤ (65586446167/500000000000 : ℝ)^3147 := by
    have hnat : (1079909839 : ℕ)^4171*500000000000^3147 ≤ 65586446167^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079909839 5000000000 65586446167 500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428451333/10000000000 : ℝ)^4171 ≤ (44498190612001/100000000000000 : ℝ)^3147 := by
    have hnat : (5428451333 : ℕ)^4171*100000000000000^3147 ≤ 44498190612001^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428451333 10000000000 44498190612001 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232745689/10000000000 : ℝ)^4171 ≤ (42384520144921/100000000000000 : ℝ)^3147 := by
    have hnat : (5232745689 : ℕ)^4171*100000000000000^3147 ≤ 42384520144921^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232745689 10000000000 42384520144921 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079909839/5000000000 : ℝ), (5428451333/10000000000 : ℝ), (5232745689/10000000000 : ℝ)] ![(65586446167/500000000000 : ℝ), (44498190612001/100000000000000 : ℝ), (42384520144921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079909839/5000000000 : ℝ)|^4171 ≤ (65586446167/500000000000 : ℝ)^3147
        have hw : |(-1079909839/5000000000 : ℝ)|=(1079909839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428451333/10000000000 : ℝ)|^4171 ≤ (44498190612001/100000000000000 : ℝ)^3147
        have hw : |(5428451333/10000000000 : ℝ)|=(5428451333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232745689/10000000000 : ℝ)|^4171 ≤ (42384520144921/100000000000000 : ℝ)^3147
        have hw : |(5232745689/10000000000 : ℝ)|=(5232745689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_1 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353623657/10000000000 : ℝ)*x 0 + (-2259842299/10000000000 : ℝ)*x 1 + (654093189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353623657/10000000000 : ℝ)^4171 ≤ (4368705400051/10000000000000 : ℝ)^3147 := by
    have hnat : (5353623657 : ℕ)^4171*10000000000000^3147 ≤ 4368705400051^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353623657 10000000000 4368705400051 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259842299/10000000000 : ℝ)^4171 ≤ (6964213869697/50000000000000 : ℝ)^3147 := by
    have hnat : (2259842299 : ℕ)^4171*50000000000000^3147 ≤ 6964213869697^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259842299 10000000000 6964213869697 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654093189/1250000000 : ℝ)^4171 ≤ (42384518244743/100000000000000 : ℝ)^3147 := by
    have hnat : (654093189 : ℕ)^4171*100000000000000^3147 ≤ 42384518244743^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654093189 1250000000 42384518244743 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353623657/10000000000 : ℝ), (-2259842299/10000000000 : ℝ), (654093189/1250000000 : ℝ)] ![(4368705400051/10000000000000 : ℝ), (6964213869697/50000000000000 : ℝ), (42384518244743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353623657/10000000000 : ℝ)|^4171 ≤ (4368705400051/10000000000000 : ℝ)^3147
        have hw : |(5353623657/10000000000 : ℝ)|=(5353623657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2259842299/10000000000 : ℝ)|^4171 ≤ (6964213869697/50000000000000 : ℝ)^3147
        have hw : |(-2259842299/10000000000 : ℝ)|=(2259842299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654093189/1250000000 : ℝ)|^4171 ≤ (42384518244743/100000000000000 : ℝ)^3147
        have hw : |(654093189/1250000000 : ℝ)|=(654093189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_2 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353623737/10000000000 : ℝ)*x 0 + (2616372787/5000000000 : ℝ)*x 1 + (-2259842113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353623737/10000000000 : ℝ)^4171 ≤ (21843527432877/50000000000000 : ℝ)^3147 := by
    have hnat : (5353623737 : ℕ)^4171*50000000000000^3147 ≤ 21843527432877^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353623737 10000000000 21843527432877 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616372787/5000000000 : ℝ)^4171 ≤ (21192259455171/50000000000000 : ℝ)^3147 := by
    have hnat : (2616372787 : ℕ)^4171*50000000000000^3147 ≤ 21192259455171^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616372787 5000000000 21192259455171 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259842113/10000000000 : ℝ)^4171 ≤ (6964213109983/50000000000000 : ℝ)^3147 := by
    have hnat : (2259842113 : ℕ)^4171*50000000000000^3147 ≤ 6964213109983^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259842113 10000000000 6964213109983 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353623737/10000000000 : ℝ), (2616372787/5000000000 : ℝ), (-2259842113/10000000000 : ℝ)] ![(21843527432877/50000000000000 : ℝ), (21192259455171/50000000000000 : ℝ), (6964213109983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353623737/10000000000 : ℝ)|^4171 ≤ (21843527432877/50000000000000 : ℝ)^3147
        have hw : |(5353623737/10000000000 : ℝ)|=(5353623737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616372787/5000000000 : ℝ)|^4171 ≤ (21192259455171/50000000000000 : ℝ)^3147
        have hw : |(2616372787/5000000000 : ℝ)|=(2616372787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2259842113/10000000000 : ℝ)|^4171 ≤ (6964213109983/50000000000000 : ℝ)^3147
        have hw : |(-2259842113/10000000000 : ℝ)|=(2259842113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_3 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361475433/10000000000 : ℝ)*x 0 + (130339213/312500000 : ℝ)*x 1 + (4560740627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361475433/10000000000 : ℝ)^4171 ≤ (8323654171903/25000000000000 : ℝ)^3147 := by
    have hnat : (4361475433 : ℕ)^4171*25000000000000^3147 ≤ 8323654171903^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361475433 10000000000 8323654171903 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130339213/312500000 : ℝ)^4171 ≤ (3922476977837/12500000000000 : ℝ)^3147 := by
    have hnat : (130339213 : ℕ)^4171*12500000000000^3147 ≤ 3922476977837^3147*312500000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130339213 312500000 3922476977837 12500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4560740627/10000000000 : ℝ)^4171 ≤ (706511349497/2000000000000 : ℝ)^3147 := by
    have hnat : (4560740627 : ℕ)^4171*2000000000000^3147 ≤ 706511349497^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560740627 10000000000 706511349497 2000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361475433/10000000000 : ℝ), (130339213/312500000 : ℝ), (4560740627/10000000000 : ℝ)] ![(8323654171903/25000000000000 : ℝ), (3922476977837/12500000000000 : ℝ), (706511349497/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361475433/10000000000 : ℝ)|^4171 ≤ (8323654171903/25000000000000 : ℝ)^3147
        have hw : |(4361475433/10000000000 : ℝ)|=(4361475433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130339213/312500000 : ℝ)|^4171 ≤ (3922476977837/12500000000000 : ℝ)^3147
        have hw : |(130339213/312500000 : ℝ)|=(130339213/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4560740627/10000000000 : ℝ)|^4171 ≤ (706511349497/2000000000000 : ℝ)^3147
        have hw : |(4560740627/10000000000 : ℝ)|=(4560740627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_4 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159837419/10000000000 : ℝ)*x 0 + (2616750713/5000000000 : ℝ)*x 1 + (42403839/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159837419/10000000000 : ℝ)^4171 ≤ (13117432040147/100000000000000 : ℝ)^3147 := by
    have hnat : (2159837419 : ℕ)^4171*100000000000000^3147 ≤ 13117432040147^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159837419 10000000000 13117432040147 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616750713/5000000000 : ℝ)^4171 ≤ (331192449437/781250000000 : ℝ)^3147 := by
    have hnat : (2616750713 : ℕ)^4171*781250000000^3147 ≤ 331192449437^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616750713 5000000000 331192449437 781250000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42403839/78125000 : ℝ)^4171 ≤ (11122483604761/25000000000000 : ℝ)^3147 := by
    have hnat : (42403839 : ℕ)^4171*25000000000000^3147 ≤ 11122483604761^3147*78125000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42403839 78125000 11122483604761 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159837419/10000000000 : ℝ), (2616750713/5000000000 : ℝ), (42403839/78125000 : ℝ)] ![(13117432040147/100000000000000 : ℝ), (331192449437/781250000000 : ℝ), (11122483604761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159837419/10000000000 : ℝ)|^4171 ≤ (13117432040147/100000000000000 : ℝ)^3147
        have hw : |(-2159837419/10000000000 : ℝ)|=(2159837419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616750713/5000000000 : ℝ)|^4171 ≤ (331192449437/781250000000 : ℝ)^3147
        have hw : |(2616750713/5000000000 : ℝ)|=(2616750713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42403839/78125000 : ℝ)|^4171 ≤ (11122483604761/25000000000000 : ℝ)^3147
        have hw : |(42403839/78125000 : ℝ)|=(42403839/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_5 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304017243/10000000000 : ℝ)*x 0 + (-2064896357/10000000000 : ℝ)*x 1 + (5427691479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304017243/10000000000 : ℝ)^4171 ≤ (43151344155069/100000000000000 : ℝ)^3147 := by
    have hnat : (5304017243 : ℕ)^4171*100000000000000^3147 ≤ 43151344155069^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304017243 10000000000 43151344155069 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064896357/10000000000 : ℝ)^4171 ≤ (617936023561/5000000000000 : ℝ)^3147 := by
    have hnat : (2064896357 : ℕ)^4171*5000000000000^3147 ≤ 617936023561^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064896357 10000000000 617936023561 5000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427691479/10000000000 : ℝ)^4171 ≤ (11122483841053/25000000000000 : ℝ)^3147 := by
    have hnat : (5427691479 : ℕ)^4171*25000000000000^3147 ≤ 11122483841053^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427691479 10000000000 11122483841053 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304017243/10000000000 : ℝ), (-2064896357/10000000000 : ℝ), (5427691479/10000000000 : ℝ)] ![(43151344155069/100000000000000 : ℝ), (617936023561/5000000000000 : ℝ), (11122483841053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304017243/10000000000 : ℝ)|^4171 ≤ (43151344155069/100000000000000 : ℝ)^3147
        have hw : |(5304017243/10000000000 : ℝ)|=(5304017243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064896357/10000000000 : ℝ)|^4171 ≤ (617936023561/5000000000000 : ℝ)^3147
        have hw : |(-2064896357/10000000000 : ℝ)|=(2064896357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427691479/10000000000 : ℝ)|^4171 ≤ (11122483841053/25000000000000 : ℝ)^3147
        have hw : |(5427691479/10000000000 : ℝ)|=(5427691479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_6 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33150107/62500000 : ℝ)*x 0 + (5427691681/10000000000 : ℝ)*x 1 + (-1032448123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33150107/62500000 : ℝ)^4171 ≤ (43151342828781/100000000000000 : ℝ)^3147 := by
    have hnat : (33150107 : ℕ)^4171*100000000000000^3147 ≤ 43151342828781^3147*62500000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33150107 62500000 43151342828781 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427691681/10000000000 : ℝ)^4171 ≤ (22244968779371/50000000000000 : ℝ)^3147 := by
    have hnat : (5427691681 : ℕ)^4171*50000000000000^3147 ≤ 22244968779371^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427691681 10000000000 22244968779371 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032448123/5000000000 : ℝ)^4171 ≤ (2471743918139/20000000000000 : ℝ)^3147 := by
    have hnat : (1032448123 : ℕ)^4171*20000000000000^3147 ≤ 2471743918139^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032448123 5000000000 2471743918139 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33150107/62500000 : ℝ), (5427691681/10000000000 : ℝ), (-1032448123/5000000000 : ℝ)] ![(43151342828781/100000000000000 : ℝ), (22244968779371/50000000000000 : ℝ), (2471743918139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33150107/62500000 : ℝ)|^4171 ≤ (43151342828781/100000000000000 : ℝ)^3147
        have hw : |(33150107/62500000 : ℝ)|=(33150107/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427691681/10000000000 : ℝ)|^4171 ≤ (22244968779371/50000000000000 : ℝ)^3147
        have hw : |(5427691681/10000000000 : ℝ)|=(5427691681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1032448123/5000000000 : ℝ)|^4171 ≤ (2471743918139/20000000000000 : ℝ)^3147
        have hw : |(-1032448123/5000000000 : ℝ)|=(1032448123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s3_7 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361510789/10000000000 : ℝ)*x 0 + (284952201/625000000 : ℝ)*x 1 + (2086184299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361510789/10000000000 : ℝ)^4171 ≤ (520233975177/1562500000000 : ℝ)^3147 := by
    have hnat : (4361510789 : ℕ)^4171*1562500000000^3147 ≤ 520233975177^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361510789 10000000000 520233975177 1562500000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284952201/625000000 : ℝ)^4171 ≤ (35310113899291/100000000000000 : ℝ)^3147 := by
    have hnat : (284952201 : ℕ)^4171*100000000000000^3147 ≤ 35310113899291^3147*625000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284952201 625000000 35310113899291 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086184299/5000000000 : ℝ)^4171 ≤ (627898233573/2000000000000 : ℝ)^3147 := by
    have hnat : (2086184299 : ℕ)^4171*2000000000000^3147 ≤ 627898233573^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086184299 5000000000 627898233573 2000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361510789/10000000000 : ℝ), (284952201/625000000 : ℝ), (2086184299/5000000000 : ℝ)] ![(520233975177/1562500000000 : ℝ), (35310113899291/100000000000000 : ℝ), (627898233573/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361510789/10000000000 : ℝ)|^4171 ≤ (520233975177/1562500000000 : ℝ)^3147
        have hw : |(4361510789/10000000000 : ℝ)|=(4361510789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284952201/625000000 : ℝ)|^4171 ≤ (35310113899291/100000000000000 : ℝ)^3147
        have hw : |(284952201/625000000 : ℝ)|=(284952201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086184299/5000000000 : ℝ)|^4171 ≤ (627898233573/2000000000000 : ℝ)^3147
        have hw : |(2086184299/5000000000 : ℝ)|=(2086184299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1149_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (333/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14797/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4551/50000 : ℝ) ^ (8341/2048 : ℝ) ≤ (5765280782320787/100000000000000000000 : ℝ) := by
    have hpowers : (4551/50000 : ℝ)^8341 ≤ (5765280782320787/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4551 : ℕ)^8341*100000000000000000000^2048 ≤ 5765280782320787^2048*50000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4551 50000 5765280782320787 100000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4551/50000 : ℝ)) (X := (5765280782320787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16481/100000 : ℝ) ^ (8341/2048 : ℝ) ≤ (64709304618416493/100000000000000000000 : ℝ) := by
    have hpowers : (16481/100000 : ℝ)^8341 ≤ (64709304618416493/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16481 : ℕ)^8341*100000000000000000000^2048 ≤ 64709304618416493^2048*100000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16481 100000 64709304618416493 100000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16481/100000 : ℝ)) (X := (64709304618416493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005765280782320787/50000000000000000000 : ℝ) ≤ (10000283102301739/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (50005765280782320787/50000000000000000000 : ℝ)^2048 ≤ (10000283102301739/10000000000000000 : ℝ)^8341 := by
      have hnat : (50005765280782320787 : ℕ)^2048*10000000000000000^8341 ≤ 10000283102301739^8341*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005765280782320787 50000000000000000000 10000283102301739 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283102301739/10000000000000000 : ℝ)) (X := (50005765280782320787/50000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (39090029134922163/39062500000000000 : ℝ) ≤ (10001729931609813/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (39090029134922163/39062500000000000 : ℝ)^2048 ≤ (10001729931609813/10000000000000000 : ℝ)^8341 := by
      have hnat : (39090029134922163 : ℕ)^2048*10000000000000000^8341 ≤ 10001729931609813^8341*39062500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39090029134922163 39062500000000000 10001729931609813 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001729931609813/10000000000000000 : ℝ)) (X := (39090029134922163/39062500000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50064709304618416493/50000000000000000000 : ℝ) ≤ (10003176760917887/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (50064709304618416493/50000000000000000000 : ℝ)^2048 ≤ (10003176760917887/10000000000000000 : ℝ)^8341 := by
      have hnat : (50064709304618416493 : ℕ)^2048*10000000000000000^8341 ≤ 10003176760917887^8341*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064709304618416493 50000000000000000000 10003176760917887 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003176760917887/10000000000000000 : ℝ)) (X := (50064709304618416493/50000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5765280782320787/100000000000000000000 : ℝ) ≤ ((14753150186232070597/14758000000000000000 : ℝ)+2*(723414654037/368950000000000 : ℝ)*(4551/50000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (14753150186232070597/14758000000000000000 : ℝ)+2*(723414654037/368950000000000 : ℝ)*(4551/50000 : ℝ)=(10000283102301739/10000000000000000 : ℝ) by norm_num, show 1+2*(5765280782320787/100000000000000000000 : ℝ)=(50005765280782320787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64709304618416493/100000000000000000000 : ℝ)+(5765280782320787/100000000000000000000 : ℝ) ≤ ((14753150186232070597/14758000000000000000 : ℝ)+(723414654037/368950000000000 : ℝ)*((16481/100000 : ℝ)+(4551/50000 : ℝ)))^(8341/2048 : ℝ) := by
    rw [show (14753150186232070597/14758000000000000000 : ℝ)+(723414654037/368950000000000 : ℝ)*((16481/100000 : ℝ)+(4551/50000 : ℝ))=(10001729931609813/10000000000000000 : ℝ) by norm_num, show 1+(64709304618416493/100000000000000000000 : ℝ)+(5765280782320787/100000000000000000000 : ℝ)=(39090029134922163/39062500000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64709304618416493/100000000000000000000 : ℝ) ≤ ((14753150186232070597/14758000000000000000 : ℝ)+2*(723414654037/368950000000000 : ℝ)*(16481/100000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (14753150186232070597/14758000000000000000 : ℝ)+2*(723414654037/368950000000000 : ℝ)*(16481/100000 : ℝ)=(10003176760917887/10000000000000000 : ℝ) by norm_num, show 1+2*(64709304618416493/100000000000000000000 : ℝ)=(50064709304618416493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14753150186232070597/14758000000000000000 : ℝ)*(X 1 0+X 2 0)+(723414654037/368950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (4551/50000 : ℝ)) (hi := (16481/100000 : ℝ)) (c := (14753150186232070597/14758000000000000000 : ℝ)) (alpha := (723414654037/368950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14753150186232070597/14758000000000000000 : ℝ)*(X 0 1+X 2 1)+(723414654037/368950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (4551/50000 : ℝ)) (hi := (16481/100000 : ℝ)) (c := (14753150186232070597/14758000000000000000 : ℝ)) (alpha := (723414654037/368950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14753150186232070597/14758000000000000000 : ℝ)*(X 0 2+X 1 2)+(723414654037/368950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (4551/50000 : ℝ)) (hi := (16481/100000 : ℝ)) (c := (14753150186232070597/14758000000000000000 : ℝ)) (alpha := (723414654037/368950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079909839/5000000000 : ℝ)*X 0 0+(5428451333/10000000000 : ℝ)*X 0 1+(5232745689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353623657/10000000000 : ℝ)*X 1 0+(-2259842299/10000000000 : ℝ)*X 1 1+(654093189/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353623737/10000000000 : ℝ)*X 2 0+(2616372787/5000000000 : ℝ)*X 2 1+(-2259842113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361475433/10000000000 : ℝ)*X 0 0+(130339213/312500000 : ℝ)*X 0 1+(4560740627/10000000000 : ℝ)*X 0 2+(4361475433/10000000000 : ℝ)*X 1 0+(130339213/312500000 : ℝ)*X 1 1+(4560740627/10000000000 : ℝ)*X 1 2+(4361475433/10000000000 : ℝ)*X 2 0+(130339213/312500000 : ℝ)*X 2 1+(4560740627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2159837419/10000000000 : ℝ)*X 0 0+(2616750713/5000000000 : ℝ)*X 0 1+(42403839/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304017243/10000000000 : ℝ)*X 1 0+(-2064896357/10000000000 : ℝ)*X 1 1+(5427691479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33150107/62500000 : ℝ)*X 2 0+(5427691681/10000000000 : ℝ)*X 2 1+(-1032448123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361510789/10000000000 : ℝ)*X 0 0+(284952201/625000000 : ℝ)*X 0 1+(2086184299/5000000000 : ℝ)*X 0 2+(4361510789/10000000000 : ℝ)*X 1 0+(284952201/625000000 : ℝ)*X 1 1+(2086184299/5000000000 : ℝ)*X 1 2+(4361510789/10000000000 : ℝ)*X 2 0+(284952201/625000000 : ℝ)*X 2 1+(2086184299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1386519708778520391153959049/368950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217702853/20000000000000 : ℝ)*(base19) + (1045539317/100000000000000 : ℝ)*(base23) + (63885157/100000000000000 : ℝ)*(lower2) + (30566081/100000000000000 : ℝ)*(upper3) + (153098297/100000000000000 : ℝ)*(upper5) + (3837309912951239/100000000000000 : ℝ)*(major0) + (3837309912951239/100000000000000 : ℝ)*(major1) + (3837309912951239/100000000000000 : ℝ)*(major2) + (2554864616786499/50000000000000 : ℝ)*(sp0) + (2554874278289121/50000000000000 : ℝ)*(sp1) + (510974859955319/10000000000000 : ℝ)*(sp2) + (1282431120677471/50000000000000 : ℝ)*(sp3) + (20411519509/100000000000000 : ℝ)*(sp4) + (7814187849/100000000000000 : ℝ)*(sp7) + (2564870055542791/100000000000000 : ℝ)*(f.failure) + (5109749645092507/100000000000000 : ℝ)*(f.sum) + (101639981396477/18447500000000000000000000000 : ℝ)*base66 + (11300664993038860317/1475800000000000000000000000000000 : ℝ)*base68 + (8521215973898460317/1475800000000000000000000000000000 : ℝ)*base70 + (8436574792827460317/1475800000000000000000000000000000 : ℝ)*base72 + (1731021311633/288242187500000000000000000 : ℝ)*base74 + (5439270003251660317/1475800000000000000000000000000000 : ℝ)*base76 + (32396778165956260317/1475800000000000000000000000000000 : ℝ)*base78 + (8141738357347539683/1475800000000000000000000000000000 : ℝ)*base79 + (4583986629137/1152968750000000000000000000 : ℝ)*base82 + (412251/2000000000000000000000 : ℝ)*base89 + (412251/2000000000000000000000 : ℝ)*base91 + (412251/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36548921573966926798107/7379000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198390559/20000000000000 : ℝ)*(base19) + (1073186739/100000000000000 : ℝ)*(base23) + (850667/625000000000 : ℝ)*(upper3) + (75957219/100000000000000 : ℝ)*(lower4) + (24660103/25000000000000 : ℝ)*(upper5) + (386723189764789/10000000000000 : ℝ)*(major0) + (386723189764789/10000000000000 : ℝ)*(major1) + (386723189764789/10000000000000 : ℝ)*(major2) + (18581875329/100000000000000 : ℝ)*(sp1) + (24724002769/100000000000000 : ℝ)*(sp2) + (1029918725130213/20000000000000 : ℝ)*(sp4) + (5149574051822941/100000000000000 : ℝ)*(sp5) + (5149567828461557/100000000000000 : ℝ)*(sp6) + (161554375283837/6250000000000 : ℝ)*(sp7) + (161554375283837/6250000000000 : ℝ)*(f.failure) + (1029918725130213/20000000000000 : ℝ)*(f.sum) + (3697146912263/1475800000000000000000000000 : ℝ)*base66 + (948656969243430967/147580000000000000000000000000000 : ℝ)*base68 + (966228723568849033/147580000000000000000000000000000 : ℝ)*base69 + (578629451012209033/147580000000000000000000000000000 : ℝ)*base71 + (10848696052523/922375000000000000000000000 : ℝ)*base74 + (178189345570210967/147580000000000000000000000000000 : ℝ)*base76 + (289969792602549033/147580000000000000000000000000000 : ℝ)*base77 + (970761949253570967/147580000000000000000000000000000 : ℝ)*base80 + (13111649032591/7379000000000000000000000000 : ℝ)*base82 + (528057/125000000000000000000 : ℝ)*base89 + (528057/125000000000000000000 : ℝ)*base91 + (528057/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1149_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14797/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1149_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1149_s4_0 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-540690919/2500000000 : ℝ)*x 0 + (5401554181/10000000000 : ℝ)*x 1 + (657214609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540690919/2500000000 : ℝ)^4171 ≤ (2628198452283/20000000000000 : ℝ)^3147 := by
    have hnat : (540690919 : ℕ)^4171*20000000000000^3147 ≤ 2628198452283^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540690919 2500000000 2628198452283 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401554181/10000000000 : ℝ)^4171 ≤ (4420620226561/10000000000000 : ℝ)^3147 := by
    have hnat : (5401554181 : ℕ)^4171*10000000000000^3147 ≤ 4420620226561^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401554181 10000000000 4420620226561 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657214609/1250000000 : ℝ)^4171 ≤ (10663201364551/25000000000000 : ℝ)^3147 := by
    have hnat : (657214609 : ℕ)^4171*25000000000000^3147 ≤ 10663201364551^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657214609 1250000000 10663201364551 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540690919/2500000000 : ℝ), (5401554181/10000000000 : ℝ), (657214609/1250000000 : ℝ)] ![(2628198452283/20000000000000 : ℝ), (4420620226561/10000000000000 : ℝ), (10663201364551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540690919/2500000000 : ℝ)|^4171 ≤ (2628198452283/20000000000000 : ℝ)^3147
        have hw : |(-540690919/2500000000 : ℝ)|=(540690919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401554181/10000000000 : ℝ)|^4171 ≤ (4420620226561/10000000000000 : ℝ)^3147
        have hw : |(5401554181/10000000000 : ℝ)|=(5401554181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657214609/1250000000 : ℝ)|^4171 ≤ (10663201364551/25000000000000 : ℝ)^3147
        have hw : |(657214609/1250000000 : ℝ)|=(657214609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_1 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346902769/10000000000 : ℝ)*x 0 + (-89434207/400000000 : ℝ)*x 1 + (5257716773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346902769/10000000000 : ℝ)^4171 ≤ (8722875758301/20000000000000 : ℝ)^3147 := by
    have hnat : (5346902769 : ℕ)^4171*20000000000000^3147 ≤ 8722875758301^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346902769 10000000000 8722875758301 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89434207/400000000 : ℝ)^4171 ≤ (3433204199187/25000000000000 : ℝ)^3147 := by
    have hnat : (89434207 : ℕ)^4171*25000000000000^3147 ≤ 3433204199187^3147*400000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89434207 400000000 3433204199187 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257716773/10000000000 : ℝ)^4171 ≤ (8530560878749/20000000000000 : ℝ)^3147 := by
    have hnat : (5257716773 : ℕ)^4171*20000000000000^3147 ≤ 8530560878749^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257716773 10000000000 8530560878749 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346902769/10000000000 : ℝ), (-89434207/400000000 : ℝ), (5257716773/10000000000 : ℝ)] ![(8722875758301/20000000000000 : ℝ), (3433204199187/25000000000000 : ℝ), (8530560878749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346902769/10000000000 : ℝ)|^4171 ≤ (8722875758301/20000000000000 : ℝ)^3147
        have hw : |(5346902769/10000000000 : ℝ)|=(5346902769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89434207/400000000 : ℝ)|^4171 ≤ (3433204199187/25000000000000 : ℝ)^3147
        have hw : |(-89434207/400000000 : ℝ)|=(89434207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257716773/10000000000 : ℝ)|^4171 ≤ (8530560878749/20000000000000 : ℝ)^3147
        have hw : |(5257716773/10000000000 : ℝ)|=(5257716773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_2 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336725713/2500000000 : ℝ)*x 0 + (5257716847/10000000000 : ℝ)*x 1 + (-1117927483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336725713/2500000000 : ℝ)^4171 ≤ (10903594922207/25000000000000 : ℝ)^3147 := by
    have hnat : (1336725713 : ℕ)^4171*25000000000000^3147 ≤ 10903594922207^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336725713 2500000000 10903594922207 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257716847/10000000000 : ℝ)^4171 ≤ (21326402594701/50000000000000 : ℝ)^3147 := by
    have hnat : (5257716847 : ℕ)^4171*50000000000000^3147 ≤ 21326402594701^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257716847 10000000000 21326402594701 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117927483/5000000000 : ℝ)^4171 ≤ (274656301907/2000000000000 : ℝ)^3147 := by
    have hnat : (1117927483 : ℕ)^4171*2000000000000^3147 ≤ 274656301907^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117927483 5000000000 274656301907 2000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336725713/2500000000 : ℝ), (5257716847/10000000000 : ℝ), (-1117927483/5000000000 : ℝ)] ![(10903594922207/25000000000000 : ℝ), (21326402594701/50000000000000 : ℝ), (274656301907/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336725713/2500000000 : ℝ)|^4171 ≤ (10903594922207/25000000000000 : ℝ)^3147
        have hw : |(1336725713/2500000000 : ℝ)|=(1336725713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257716847/10000000000 : ℝ)|^4171 ≤ (21326402594701/50000000000000 : ℝ)^3147
        have hw : |(5257716847/10000000000 : ℝ)|=(5257716847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117927483/5000000000 : ℝ)|^4171 ≤ (274656301907/2000000000000 : ℝ)^3147
        have hw : |(-1117927483/5000000000 : ℝ)|=(1117927483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_3 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363233839/10000000000 : ℝ)*x 0 + (4222293519/10000000000 : ℝ)*x 1 + (4508846693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363233839/10000000000 : ℝ)^4171 ≤ (16656204485269/50000000000000 : ℝ)^3147 := by
    have hnat : (4363233839 : ℕ)^4171*50000000000000^3147 ≤ 16656204485269^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363233839 10000000000 16656204485269 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222293519/10000000000 : ℝ)^4171 ≤ (31893772971707/100000000000000 : ℝ)^3147 := by
    have hnat : (4222293519 : ℕ)^4171*100000000000000^3147 ≤ 31893772971707^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222293519 10000000000 31893772971707 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508846693/10000000000 : ℝ)^4171 ≤ (8698454511799/25000000000000 : ℝ)^3147 := by
    have hnat : (4508846693 : ℕ)^4171*25000000000000^3147 ≤ 8698454511799^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508846693 10000000000 8698454511799 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363233839/10000000000 : ℝ), (4222293519/10000000000 : ℝ), (4508846693/10000000000 : ℝ)] ![(16656204485269/50000000000000 : ℝ), (31893772971707/100000000000000 : ℝ), (8698454511799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363233839/10000000000 : ℝ)|^4171 ≤ (16656204485269/50000000000000 : ℝ)^3147
        have hw : |(4363233839/10000000000 : ℝ)|=(4363233839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222293519/10000000000 : ℝ)|^4171 ≤ (31893772971707/100000000000000 : ℝ)^3147
        have hw : |(4222293519/10000000000 : ℝ)|=(4222293519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508846693/10000000000 : ℝ)|^4171 ≤ (8698454511799/25000000000000 : ℝ)^3147
        have hw : |(4508846693/10000000000 : ℝ)|=(4508846693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_4 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-135173159/625000000 : ℝ)*x 0 + (2629063071/5000000000 : ℝ)*x 1 + (270057169/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135173159/625000000 : ℝ)^4171 ≤ (821315473129/6250000000000 : ℝ)^3147 := by
    have hnat : (135173159 : ℕ)^4171*6250000000000^3147 ≤ 821315473129^3147*625000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135173159 625000000 821315473129 6250000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629063071/5000000000 : ℝ)^4171 ≤ (42657206031557/100000000000000 : ℝ)^3147 := by
    have hnat : (2629063071 : ℕ)^4171*100000000000000^3147 ≤ 42657206031557^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629063071 5000000000 42657206031557 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270057169/500000000 : ℝ)^4171 ≤ (22100873189991/50000000000000 : ℝ)^3147 := by
    have hnat : (270057169 : ℕ)^4171*50000000000000^3147 ≤ 22100873189991^3147*500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270057169 500000000 22100873189991 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135173159/625000000 : ℝ), (2629063071/5000000000 : ℝ), (270057169/500000000 : ℝ)] ![(821315473129/6250000000000 : ℝ), (42657206031557/100000000000000 : ℝ), (22100873189991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135173159/625000000 : ℝ)|^4171 ≤ (821315473129/6250000000000 : ℝ)^3147
        have hw : |(-135173159/625000000 : ℝ)|=(135173159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629063071/5000000000 : ℝ)|^4171 ≤ (42657206031557/100000000000000 : ℝ)^3147
        have hw : |(2629063071/5000000000 : ℝ)|=(2629063071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270057169/500000000 : ℝ)|^4171 ≤ (22100873189991/50000000000000 : ℝ)^3147
        have hw : |(270057169/500000000 : ℝ)|=(270057169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_5 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663805471/1250000000 : ℝ)*x 0 + (-2092429003/10000000000 : ℝ)*x 1 + (2700571679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663805471/1250000000 : ℝ)^4171 ≤ (43220653952341/100000000000000 : ℝ)^3147 := by
    have hnat : (663805471 : ℕ)^4171*100000000000000^3147 ≤ 43220653952341^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663805471 1250000000 43220653952341 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092429003/10000000000 : ℝ)^4171 ≤ (12577599900647/100000000000000 : ℝ)^3147 := by
    have hnat : (2092429003 : ℕ)^4171*100000000000000^3147 ≤ 12577599900647^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092429003 10000000000 12577599900647 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700571679/5000000000 : ℝ)^4171 ≤ (22100873070677/50000000000000 : ℝ)^3147 := by
    have hnat : (2700571679 : ℕ)^4171*50000000000000^3147 ≤ 22100873070677^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700571679 5000000000 22100873070677 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663805471/1250000000 : ℝ), (-2092429003/10000000000 : ℝ), (2700571679/5000000000 : ℝ)] ![(43220653952341/100000000000000 : ℝ), (12577599900647/100000000000000 : ℝ), (22100873070677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663805471/1250000000 : ℝ)|^4171 ≤ (43220653952341/100000000000000 : ℝ)^3147
        have hw : |(663805471/1250000000 : ℝ)|=(663805471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092429003/10000000000 : ℝ)|^4171 ≤ (12577599900647/100000000000000 : ℝ)^3147
        have hw : |(-2092429003/10000000000 : ℝ)|=(2092429003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700571679/5000000000 : ℝ)|^4171 ≤ (22100873070677/50000000000000 : ℝ)^3147
        have hw : |(2700571679/5000000000 : ℝ)|=(2700571679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_6 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310443673/10000000000 : ℝ)*x 0 + (1080228753/2000000000 : ℝ)*x 1 + (-65388393/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310443673/10000000000 : ℝ)^4171 ≤ (43220652927569/100000000000000 : ℝ)^3147 := by
    have hnat : (5310443673 : ℕ)^4171*100000000000000^3147 ≤ 43220652927569^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310443673 10000000000 43220652927569 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080228753/2000000000 : ℝ)^4171 ≤ (44201750555957/100000000000000 : ℝ)^3147 := by
    have hnat : (1080228753 : ℕ)^4171*100000000000000^3147 ≤ 44201750555957^3147*2000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080228753 2000000000 44201750555957 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65388393/312500000 : ℝ)^4171 ≤ (3144399124693/25000000000000 : ℝ)^3147 := by
    have hnat : (65388393 : ℕ)^4171*25000000000000^3147 ≤ 3144399124693^3147*312500000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65388393 312500000 3144399124693 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310443673/10000000000 : ℝ), (1080228753/2000000000 : ℝ), (-65388393/312500000 : ℝ)] ![(43220652927569/100000000000000 : ℝ), (44201750555957/100000000000000 : ℝ), (3144399124693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310443673/10000000000 : ℝ)|^4171 ≤ (43220652927569/100000000000000 : ℝ)^3147
        have hw : |(5310443673/10000000000 : ℝ)|=(5310443673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080228753/2000000000 : ℝ)|^4171 ≤ (44201750555957/100000000000000 : ℝ)^3147
        have hw : |(1080228753/2000000000 : ℝ)|=(1080228753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65388393/312500000 : ℝ)|^4171 ≤ (3144399124693/25000000000000 : ℝ)^3147
        have hw : |(-65388393/312500000 : ℝ)|=(65388393/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s4_7 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (87264959/200000000 : ℝ)*x 0 + (450803243/1000000000 : ℝ)*x 1 + (2111555527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87264959/200000000 : ℝ)^4171 ≤ (1665627588047/5000000000000 : ℝ)^3147 := by
    have hnat : (87264959 : ℕ)^4171*5000000000000^3147 ≤ 1665627588047^3147*200000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87264959 200000000 1665627588047 5000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450803243/1000000000 : ℝ)^4171 ≤ (1391419608569/4000000000000 : ℝ)^3147 := by
    have hnat : (450803243 : ℕ)^4171*4000000000000^3147 ≤ 1391419608569^3147*1000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450803243 1000000000 1391419608569 4000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111555527/5000000000 : ℝ)^4171 ≤ (31901958014597/100000000000000 : ℝ)^3147 := by
    have hnat : (2111555527 : ℕ)^4171*100000000000000^3147 ≤ 31901958014597^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111555527 5000000000 31901958014597 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87264959/200000000 : ℝ), (450803243/1000000000 : ℝ), (2111555527/5000000000 : ℝ)] ![(1665627588047/5000000000000 : ℝ), (1391419608569/4000000000000 : ℝ), (31901958014597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87264959/200000000 : ℝ)|^4171 ≤ (1665627588047/5000000000000 : ℝ)^3147
        have hw : |(87264959/200000000 : ℝ)|=(87264959/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450803243/1000000000 : ℝ)|^4171 ≤ (1391419608569/4000000000000 : ℝ)^3147
        have hw : |(450803243/1000000000 : ℝ)|=(450803243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111555527/5000000000 : ℝ)|^4171 ≤ (31901958014597/100000000000000 : ℝ)^3147
        have hw : |(2111555527/5000000000 : ℝ)|=(2111555527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1149_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14797/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11189/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14797/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (333/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14797/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (333/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14797/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (333/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14797/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (333/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14797/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (333/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14797/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (333/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (333/3125 : ℝ) ^ (8341/2048 : ℝ) ≤ (2738864433892397/25000000000000000000 : ℝ) := by
    have hpowers : (333/3125 : ℝ)^8341 ≤ (2738864433892397/25000000000000000000 : ℝ)^2048 := by
      have hnat : (333 : ℕ)^8341*25000000000000000000^2048 ≤ 2738864433892397^2048*3125^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        333 3125 2738864433892397 25000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (333/3125 : ℝ)) (X := (2738864433892397/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14797/100000 : ℝ) ^ (8341/2048 : ℝ) ≤ (2085890916254829/5000000000000000000 : ℝ) := by
    have hpowers : (14797/100000 : ℝ)^8341 ≤ (2085890916254829/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14797 : ℕ)^8341*5000000000000000000^2048 ≤ 2085890916254829^2048*100000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14797 100000 2085890916254829 5000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14797/100000 : ℝ)) (X := (2085890916254829/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502738864433892397/12500000000000000000 : ℝ) ≤ (5000268971624073/5000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (12502738864433892397/12500000000000000000 : ℝ)^2048 ≤ (5000268971624073/5000000000000000 : ℝ)^8341 := by
      have hnat : (12502738864433892397 : ℕ)^2048*5000000000000000^8341 ≤ 5000268971624073^8341*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502738864433892397 12500000000000000000 5000268971624073 5000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268971624073/5000000000000000 : ℝ)) (X := (12502738864433892397/12500000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506584159507583271/12500000000000000000 : ℝ) ≤ (10001293051686053/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (12506584159507583271/12500000000000000000 : ℝ)^2048 ≤ (10001293051686053/10000000000000000 : ℝ)^8341 := by
      have hnat : (12506584159507583271 : ℕ)^2048*10000000000000000^8341 ≤ 10001293051686053^8341*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506584159507583271 12500000000000000000 10001293051686053 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001293051686053/10000000000000000 : ℝ)) (X := (12506584159507583271/12500000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502085890916254829/2500000000000000000 : ℝ) ≤ (250051204003099/250000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (2502085890916254829/2500000000000000000 : ℝ)^2048 ≤ (250051204003099/250000000000000 : ℝ)^8341 := by
      have hnat : (2502085890916254829 : ℕ)^2048*250000000000000^8341 ≤ 250051204003099^8341*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502085890916254829 2500000000000000000 250051204003099 250000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250051204003099/250000000000000 : ℝ)) (X := (2502085890916254829/2500000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2738864433892397/25000000000000000000 : ℝ) ≤ ((20698067375980949301/20705000000000000000 : ℝ)+2*(755108437907/414100000000000 : ℝ)*(333/3125 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (20698067375980949301/20705000000000000000 : ℝ)+2*(755108437907/414100000000000 : ℝ)*(333/3125 : ℝ)=(5000268971624073/5000000000000000 : ℝ) by norm_num, show 1+2*(2738864433892397/25000000000000000000 : ℝ)=(12502738864433892397/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2085890916254829/5000000000000000000 : ℝ)+(2738864433892397/25000000000000000000 : ℝ) ≤ ((20698067375980949301/20705000000000000000 : ℝ)+(755108437907/414100000000000 : ℝ)*((14797/100000 : ℝ)+(333/3125 : ℝ)))^(8341/2048 : ℝ) := by
    rw [show (20698067375980949301/20705000000000000000 : ℝ)+(755108437907/414100000000000 : ℝ)*((14797/100000 : ℝ)+(333/3125 : ℝ))=(10001293051686053/10000000000000000 : ℝ) by norm_num, show 1+(2085890916254829/5000000000000000000 : ℝ)+(2738864433892397/25000000000000000000 : ℝ)=(12506584159507583271/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2085890916254829/5000000000000000000 : ℝ) ≤ ((20698067375980949301/20705000000000000000 : ℝ)+2*(755108437907/414100000000000 : ℝ)*(14797/100000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (20698067375980949301/20705000000000000000 : ℝ)+2*(755108437907/414100000000000 : ℝ)*(14797/100000 : ℝ)=(250051204003099/250000000000000 : ℝ) by norm_num, show 1+2*(2085890916254829/5000000000000000000 : ℝ)=(2502085890916254829/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20698067375980949301/20705000000000000000 : ℝ)*(X 1 0+X 2 0)+(755108437907/414100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (333/3125 : ℝ)) (hi := (14797/100000 : ℝ)) (c := (20698067375980949301/20705000000000000000 : ℝ)) (alpha := (755108437907/414100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20698067375980949301/20705000000000000000 : ℝ)*(X 0 1+X 2 1)+(755108437907/414100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (333/3125 : ℝ)) (hi := (14797/100000 : ℝ)) (c := (20698067375980949301/20705000000000000000 : ℝ)) (alpha := (755108437907/414100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20698067375980949301/20705000000000000000 : ℝ)*(X 0 2+X 1 2)+(755108437907/414100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (333/3125 : ℝ)) (hi := (14797/100000 : ℝ)) (c := (20698067375980949301/20705000000000000000 : ℝ)) (alpha := (755108437907/414100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540690919/2500000000 : ℝ)*X 0 0+(5401554181/10000000000 : ℝ)*X 0 1+(657214609/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346902769/10000000000 : ℝ)*X 1 0+(-89434207/400000000 : ℝ)*X 1 1+(5257716773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336725713/2500000000 : ℝ)*X 2 0+(5257716847/10000000000 : ℝ)*X 2 1+(-1117927483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363233839/10000000000 : ℝ)*X 0 0+(4222293519/10000000000 : ℝ)*X 0 1+(4508846693/10000000000 : ℝ)*X 0 2+(4363233839/10000000000 : ℝ)*X 1 0+(4222293519/10000000000 : ℝ)*X 1 1+(4508846693/10000000000 : ℝ)*X 1 2+(4363233839/10000000000 : ℝ)*X 2 0+(4222293519/10000000000 : ℝ)*X 2 1+(4508846693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-135173159/625000000 : ℝ)*X 0 0+(2629063071/5000000000 : ℝ)*X 0 1+(270057169/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663805471/1250000000 : ℝ)*X 1 0+(-2092429003/10000000000 : ℝ)*X 1 1+(2700571679/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310443673/10000000000 : ℝ)*X 2 0+(1080228753/2000000000 : ℝ)*X 2 1+(-65388393/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((87264959/200000000 : ℝ)*X 0 0+(450803243/1000000000 : ℝ)*X 0 1+(2111555527/5000000000 : ℝ)*X 0 2+(87264959/200000000 : ℝ)*X 1 0+(450803243/1000000000 : ℝ)*X 1 1+(2111555527/5000000000 : ℝ)*X 1 2+(87264959/200000000 : ℝ)*X 2 0+(450803243/1000000000 : ℝ)*X 2 1+(2111555527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1789605089734429347614793447/517625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195443533/25000000000000 : ℝ)*(base19) + (750103659/100000000000000 : ℝ)*(base23) + (88783113/100000000000000 : ℝ)*(lower2) + (85470269/100000000000000 : ℝ)*(upper5) + (5221056002529551/100000000000000 : ℝ)*(major0) + (5221056002529551/100000000000000 : ℝ)*(major1) + (5221056002529551/100000000000000 : ℝ)*(major2) + (347615832582703/5000000000000 : ℝ)*(sp0) + (1390467383954829/20000000000000 : ℝ)*(sp1) + (6952340831088303/100000000000000 : ℝ)*(sp2) + (1744881016287737/50000000000000 : ℝ)*(sp3) + (24929537901/100000000000000 : ℝ)*(sp4) + (1939821843/50000000000000 : ℝ)*(sp5) + (8276047017/100000000000000 : ℝ)*(sp7) + (872442577155623/25000000000000 : ℝ)*(f.failure) + (3476170790595981/50000000000000 : ℝ)*(f.sum) + (118751932628303/20705000000000000000000000000 : ℝ)*base66 + (38300778788954143851/2070500000000000000000000000000000 : ℝ)*base67 + (33909596170223143851/2070500000000000000000000000000000 : ℝ)*base69 + (66764275492448643851/2070500000000000000000000000000000 : ℝ)*base71 + (61118626508621/10352500000000000000000000000 : ℝ)*base73 + (18203286206873356149/2070500000000000000000000000000000 : ℝ)*base76 + (12019874928337143851/2070500000000000000000000000000000 : ℝ)*base77 + (41528257958304643851/2070500000000000000000000000000000 : ℝ)*base79 + (82493346704847/20705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (2899003/500000000000000000000 : ℝ)*base89 + (2899003/500000000000000000000 : ℝ)*base91 + (2899003/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13115874742498571069732067909/1035250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1244023/156250000000 : ℝ)*(base19) + (536128273/50000000000000 : ℝ)*(base23) + (113723827/100000000000000 : ℝ)*(lower2) + (350766617/100000000000000 : ℝ)*(upper3) + (96120427/50000000000000 : ℝ)*(lower4) + (5250949843926199/100000000000000 : ℝ)*(major0) + (5250949843926199/100000000000000 : ℝ)*(major1) + (5250949843926199/100000000000000 : ℝ)*(major2) + (36896077189/100000000000000 : ℝ)*(sp2) + (12532893/500000000000 : ℝ)*(sp3) + (1748036954748103/25000000000000 : ℝ)*(sp4) + (6992147022817691/100000000000000 : ℝ)*(sp5) + (1748027462664669/25000000000000 : ℝ)*(sp6) + (877437234992989/25000000000000 : ℝ)*(sp7) + (877437861637639/25000000000000 : ℝ)*(f.failure) + (1748036954748103/25000000000000 : ℝ)*(f.sum) + (115217603037733/20705000000000000000000000000 : ℝ)*base65 + (4263804072907286899/2070500000000000000000000000000000 : ℝ)*base67 + (7454769641407286899/2070500000000000000000000000000000 : ℝ)*base69 + (29973048726475286899/2070500000000000000000000000000000 : ℝ)*base71 + (17460658064279/10352500000000000000000000000 : ℝ)*base73 + (65748633281238286899/2070500000000000000000000000000000 : ℝ)*base75 + (31314939180171286899/2070500000000000000000000000000000 : ℝ)*base77 + (28692756262717786899/2070500000000000000000000000000000 : ℝ)*base79 + (96917447336323/20705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (946021/500000000000000000000 : ℝ)*base90 + (946021/500000000000000000000 : ℝ)*base92 + (946021/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1149_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14797/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1149_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1149_s5_0 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-540845809/2500000000 : ℝ)*x 0 + (67434133/125000000 : ℝ)*x 1 + (1052826771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540845809/2500000000 : ℝ)^4171 ≤ (13145981866227/100000000000000 : ℝ)^3147 := by
    have hnat : (540845809 : ℕ)^4171*100000000000000^3147 ≤ 13145981866227^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540845809 2500000000 13145981866227 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67434133/125000000 : ℝ)^4171 ≤ (1765288113051/4000000000000 : ℝ)^3147 := by
    have hnat : (67434133 : ℕ)^4171*4000000000000^3147 ≤ 1765288113051^3147*125000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67434133 125000000 1765288113051 4000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052826771/2000000000 : ℝ)^4171 ≤ (13350567277/31250000000 : ℝ)^3147 := by
    have hnat : (1052826771 : ℕ)^4171*31250000000^3147 ≤ 13350567277^3147*2000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052826771 2000000000 13350567277 31250000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540845809/2500000000 : ℝ), (67434133/125000000 : ℝ), (1052826771/2000000000 : ℝ)] ![(13145981866227/100000000000000 : ℝ), (1765288113051/4000000000000 : ℝ), (13350567277/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540845809/2500000000 : ℝ)|^4171 ≤ (13145981866227/100000000000000 : ℝ)^3147
        have hw : |(-540845809/2500000000 : ℝ)|=(540845809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67434133/125000000 : ℝ)|^4171 ≤ (1765288113051/4000000000000 : ℝ)^3147
        have hw : |(67434133/125000000 : ℝ)|=(67434133/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052826771/2000000000 : ℝ)|^4171 ≤ (13350567277/31250000000 : ℝ)^3147
        have hw : |(1052826771/2000000000 : ℝ)|=(1052826771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_1 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133629767/250000000 : ℝ)*x 0 + (-557412177/2500000000 : ℝ)*x 1 + (2632066911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133629767/250000000 : ℝ)^4171 ≤ (1089896753731/2500000000000 : ℝ)^3147 := by
    have hnat : (133629767 : ℕ)^4171*2500000000000^3147 ≤ 1089896753731^3147*250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133629767 250000000 1089896753731 2500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557412177/2500000000 : ℝ)^4171 ≤ (2736462983217/20000000000000 : ℝ)^3147 := by
    have hnat : (557412177 : ℕ)^4171*20000000000000^3147 ≤ 2736462983217^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557412177 2500000000 2736462983217 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632066911/5000000000 : ℝ)^4171 ≤ (42721814931439/100000000000000 : ℝ)^3147 := by
    have hnat : (2632066911 : ℕ)^4171*100000000000000^3147 ≤ 42721814931439^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632066911 5000000000 42721814931439 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133629767/250000000 : ℝ), (-557412177/2500000000 : ℝ), (2632066911/5000000000 : ℝ)] ![(1089896753731/2500000000000 : ℝ), (2736462983217/20000000000000 : ℝ), (42721814931439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133629767/250000000 : ℝ)|^4171 ≤ (1089896753731/2500000000000 : ℝ)^3147
        have hw : |(133629767/250000000 : ℝ)|=(133629767/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557412177/2500000000 : ℝ)|^4171 ≤ (2736462983217/20000000000000 : ℝ)^3147
        have hw : |(-557412177/2500000000 : ℝ)|=(557412177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632066911/5000000000 : ℝ)|^4171 ≤ (42721814931439/100000000000000 : ℝ)^3147
        have hw : |(2632066911/5000000000 : ℝ)|=(2632066911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_2 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345190727/10000000000 : ℝ)*x 0 + (5264133791/10000000000 : ℝ)*x 1 + (-445929737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345190727/10000000000 : ℝ)^4171 ≤ (4359587065731/10000000000000 : ℝ)^3147 := by
    have hnat : (5345190727 : ℕ)^4171*10000000000000^3147 ≤ 4359587065731^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345190727 10000000000 4359587065731 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264133791/10000000000 : ℝ)^4171 ≤ (42721814597991/100000000000000 : ℝ)^3147 := by
    have hnat : (5264133791 : ℕ)^4171*100000000000000^3147 ≤ 42721814597991^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264133791 10000000000 42721814597991 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445929737/2000000000 : ℝ)^4171 ≤ (684115736451/5000000000000 : ℝ)^3147 := by
    have hnat : (445929737 : ℕ)^4171*5000000000000^3147 ≤ 684115736451^3147*2000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445929737 2000000000 684115736451 5000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345190727/10000000000 : ℝ), (5264133791/10000000000 : ℝ), (-445929737/2000000000 : ℝ)] ![(4359587065731/10000000000000 : ℝ), (42721814597991/100000000000000 : ℝ), (684115736451/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345190727/10000000000 : ℝ)|^4171 ≤ (4359587065731/10000000000000 : ℝ)^3147
        have hw : |(5345190727/10000000000 : ℝ)|=(5345190727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264133791/10000000000 : ℝ)|^4171 ≤ (42721814597991/100000000000000 : ℝ)^3147
        have hw : |(5264133791/10000000000 : ℝ)|=(5264133791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445929737/2000000000 : ℝ)|^4171 ≤ (684115736451/5000000000000 : ℝ)^3147
        have hw : |(-445929737/2000000000 : ℝ)|=(445929737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_3 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545449589/1250000000 : ℝ)*x 0 + (2117717567/5000000000 : ℝ)*x 1 + (179824441/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545449589/1250000000 : ℝ)^4171 ≤ (3331608096087/10000000000000 : ℝ)^3147 := by
    have hnat : (545449589 : ℕ)^4171*10000000000000^3147 ≤ 3331608096087^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545449589 1250000000 3331608096087 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117717567/5000000000 : ℝ)^4171 ≤ (4003175920463/12500000000000 : ℝ)^3147 := by
    have hnat : (2117717567 : ℕ)^4171*12500000000000^3147 ≤ 4003175920463^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117717567 5000000000 4003175920463 12500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179824441/400000000 : ℝ)^4171 ≤ (34658511649989/100000000000000 : ℝ)^3147 := by
    have hnat : (179824441 : ℕ)^4171*100000000000000^3147 ≤ 34658511649989^3147*400000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179824441 400000000 34658511649989 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545449589/1250000000 : ℝ), (2117717567/5000000000 : ℝ), (179824441/400000000 : ℝ)] ![(3331608096087/10000000000000 : ℝ), (4003175920463/12500000000000 : ℝ), (34658511649989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545449589/1250000000 : ℝ)|^4171 ≤ (3331608096087/10000000000000 : ℝ)^3147
        have hw : |(545449589/1250000000 : ℝ)|=(545449589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117717567/5000000000 : ℝ)|^4171 ≤ (4003175920463/12500000000000 : ℝ)^3147
        have hw : |(2117717567/5000000000 : ℝ)|=(2117717567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179824441/400000000 : ℝ)|^4171 ≤ (34658511649989/100000000000000 : ℝ)^3147
        have hw : |(179824441/400000000 : ℝ)|=(179824441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_4 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163388549/10000000000 : ℝ)*x 0 + (5264471087/10000000000 : ℝ)*x 1 + (5394392133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163388549/10000000000 : ℝ)^4171 ≤ (6573012328149/50000000000000 : ℝ)^3147 := by
    have hnat : (2163388549 : ℕ)^4171*50000000000000^3147 ≤ 6573012328149^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163388549 10000000000 6573012328149 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264471087/10000000000 : ℝ)^4171 ≤ (10681360680113/25000000000000 : ℝ)^3147 := by
    have hnat : (5264471087 : ℕ)^4171*25000000000000^3147 ≤ 10681360680113^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264471087 10000000000 10681360680113 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394392133/10000000000 : ℝ)^4171 ≤ (4412853260281/10000000000000 : ℝ)^3147 := by
    have hnat : (5394392133 : ℕ)^4171*10000000000000^3147 ≤ 4412853260281^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394392133 10000000000 4412853260281 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163388549/10000000000 : ℝ), (5264471087/10000000000 : ℝ), (5394392133/10000000000 : ℝ)] ![(6573012328149/50000000000000 : ℝ), (10681360680113/25000000000000 : ℝ), (4412853260281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163388549/10000000000 : ℝ)|^4171 ≤ (6573012328149/50000000000000 : ℝ)^3147
        have hw : |(-2163388549/10000000000 : ℝ)|=(2163388549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264471087/10000000000 : ℝ)|^4171 ≤ (10681360680113/25000000000000 : ℝ)^3147
        have hw : |(5264471087/10000000000 : ℝ)|=(5264471087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394392133/10000000000 : ℝ)|^4171 ≤ (4412853260281/10000000000000 : ℝ)^3147
        have hw : |(5394392133/10000000000 : ℝ)|=(5394392133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_5 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312086723/10000000000 : ℝ)*x 0 + (-2099390287/10000000000 : ℝ)*x 1 + (5394392129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312086723/10000000000 : ℝ)^4171 ≤ (8647675506817/20000000000000 : ℝ)^3147 := by
    have hnat : (5312086723 : ℕ)^4171*20000000000000^3147 ≤ 8647675506817^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312086723 10000000000 8647675506817 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099390287/10000000000 : ℝ)^4171 ≤ (2526617978823/20000000000000 : ℝ)^3147 := by
    have hnat : (2099390287 : ℕ)^4171*20000000000000^3147 ≤ 2526617978823^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099390287 10000000000 2526617978823 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394392129/10000000000 : ℝ)^4171 ≤ (44128532559441/100000000000000 : ℝ)^3147 := by
    have hnat : (5394392129 : ℕ)^4171*100000000000000^3147 ≤ 44128532559441^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394392129 10000000000 44128532559441 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312086723/10000000000 : ℝ), (-2099390287/10000000000 : ℝ), (5394392129/10000000000 : ℝ)] ![(8647675506817/20000000000000 : ℝ), (2526617978823/20000000000000 : ℝ), (44128532559441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312086723/10000000000 : ℝ)|^4171 ≤ (8647675506817/20000000000000 : ℝ)^3147
        have hw : |(5312086723/10000000000 : ℝ)|=(5312086723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099390287/10000000000 : ℝ)|^4171 ≤ (2526617978823/20000000000000 : ℝ)^3147
        have hw : |(-2099390287/10000000000 : ℝ)|=(2099390287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394392129/10000000000 : ℝ)|^4171 ≤ (44128532559441/100000000000000 : ℝ)^3147
        have hw : |(5394392129/10000000000 : ℝ)|=(5394392129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_6 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656043363/5000000000 : ℝ)*x 0 + (5394392127/10000000000 : ℝ)*x 1 + (-524847571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656043363/5000000000 : ℝ)^4171 ≤ (43238377566449/100000000000000 : ℝ)^3147 := by
    have hnat : (2656043363 : ℕ)^4171*100000000000000^3147 ≤ 43238377566449^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656043363 5000000000 43238377566449 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394392127/10000000000 : ℝ)^4171 ≤ (11032133134439/25000000000000 : ℝ)^3147 := by
    have hnat : (5394392127 : ℕ)^4171*25000000000000^3147 ≤ 11032133134439^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394392127 10000000000 11032133134439 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524847571/2500000000 : ℝ)^4171 ≤ (3158272467547/25000000000000 : ℝ)^3147 := by
    have hnat : (524847571 : ℕ)^4171*25000000000000^3147 ≤ 3158272467547^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524847571 2500000000 3158272467547 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656043363/5000000000 : ℝ), (5394392127/10000000000 : ℝ), (-524847571/2500000000 : ℝ)] ![(43238377566449/100000000000000 : ℝ), (11032133134439/25000000000000 : ℝ), (3158272467547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656043363/5000000000 : ℝ)|^4171 ≤ (43238377566449/100000000000000 : ℝ)^3147
        have hw : |(2656043363/5000000000 : ℝ)|=(2656043363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394392127/10000000000 : ℝ)|^4171 ≤ (11032133134439/25000000000000 : ℝ)^3147
        have hw : |(5394392127/10000000000 : ℝ)|=(5394392127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524847571/2500000000 : ℝ)|^4171 ≤ (3158272467547/25000000000000 : ℝ)^3147
        have hw : |(-524847571/2500000000 : ℝ)|=(524847571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s5_7 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1090901821/2500000000 : ℝ)*x 0 + (4494939057/10000000000 : ℝ)*x 1 + (4236109557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090901821/2500000000 : ℝ)^4171 ≤ (33316187942713/100000000000000 : ℝ)^3147 := by
    have hnat : (1090901821 : ℕ)^4171*100000000000000^3147 ≤ 33316187942713^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090901821 2500000000 33316187942713 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494939057/10000000000 : ℝ)^4171 ≤ (34651645668027/100000000000000 : ℝ)^3147 := by
    have hnat : (4494939057 : ℕ)^4171*100000000000000^3147 ≤ 34651645668027^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494939057 10000000000 34651645668027 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236109557/10000000000 : ℝ)^4171 ≤ (32032166383181/100000000000000 : ℝ)^3147 := by
    have hnat : (4236109557 : ℕ)^4171*100000000000000^3147 ≤ 32032166383181^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236109557 10000000000 32032166383181 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090901821/2500000000 : ℝ), (4494939057/10000000000 : ℝ), (4236109557/10000000000 : ℝ)] ![(33316187942713/100000000000000 : ℝ), (34651645668027/100000000000000 : ℝ), (32032166383181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090901821/2500000000 : ℝ)|^4171 ≤ (33316187942713/100000000000000 : ℝ)^3147
        have hw : |(1090901821/2500000000 : ℝ)|=(1090901821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494939057/10000000000 : ℝ)|^4171 ≤ (34651645668027/100000000000000 : ℝ)^3147
        have hw : |(4494939057/10000000000 : ℝ)|=(4494939057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236109557/10000000000 : ℝ)|^4171 ≤ (32032166383181/100000000000000 : ℝ)^3147
        have hw : |(4236109557/10000000000 : ℝ)|=(4236109557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1149_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (453/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11189/100000 : ℝ) ^ (8341/2048 : ℝ) ≤ (417648539069913/3125000000000000000 : ℝ) := by
    have hpowers : (11189/100000 : ℝ)^8341 ≤ (417648539069913/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11189 : ℕ)^8341*3125000000000000000^2048 ≤ 417648539069913^2048*100000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11189 100000 417648539069913 3125000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11189/100000 : ℝ)) (X := (417648539069913/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8341/2048 : ℝ) ≤ (7126287353685599/20000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8341 ≤ (7126287353685599/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8341*20000000000000000000^2048 ≤ 7126287353685599^2048*20000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 7126287353685599 20000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (7126287353685599/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562917648539069913/1562500000000000000 : ℝ) ≤ (10000656234389159/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (1562917648539069913/1562500000000000000 : ℝ)^2048 ≤ (10000656234389159/10000000000000000 : ℝ)^8341 := by
      have hnat : (1562917648539069913 : ℕ)^2048*10000000000000000^8341 ≤ 10000656234389159^8341*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562917648539069913 1562500000000000000 10000656234389159 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656234389159/10000000000000000 : ℝ)) (X := (1562917648539069913/1562500000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048996190018665211/100000000000000000000 : ℝ) ≤ (250030070032333/250000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (100048996190018665211/100000000000000000000 : ℝ)^2048 ≤ (250030070032333/250000000000000 : ℝ)^8341 := by
      have hnat : (100048996190018665211 : ℕ)^2048*250000000000000^8341 ≤ 250030070032333^8341*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048996190018665211 100000000000000000000 250030070032333 250000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250030070032333/250000000000000 : ℝ)) (X := (100048996190018665211/100000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007126287353685599/10000000000000000000 : ℝ) ≤ (10001749368197481/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (10007126287353685599/10000000000000000000 : ℝ)^2048 ≤ (10001749368197481/10000000000000000 : ℝ)^8341 := by
      have hnat : (10007126287353685599 : ℕ)^2048*10000000000000000^8341 ≤ 10001749368197481^8341*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007126287353685599 10000000000000000000 10001749368197481 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001749368197481/10000000000000000 : ℝ)) (X := (10007126287353685599/10000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(417648539069913/3125000000000000000 : ℝ) ≤ ((951555244242751983/951875000000000000 : ℝ)+2*(546566904161/304600000000000 : ℝ)*(11189/100000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (951555244242751983/951875000000000000 : ℝ)+2*(546566904161/304600000000000 : ℝ)*(11189/100000 : ℝ)=(10000656234389159/10000000000000000 : ℝ) by norm_num, show 1+2*(417648539069913/3125000000000000000 : ℝ)=(1562917648539069913/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7126287353685599/20000000000000000000 : ℝ)+(417648539069913/3125000000000000000 : ℝ) ≤ ((951555244242751983/951875000000000000 : ℝ)+(546566904161/304600000000000 : ℝ)*((2847/20000 : ℝ)+(11189/100000 : ℝ)))^(8341/2048 : ℝ) := by
    rw [show (951555244242751983/951875000000000000 : ℝ)+(546566904161/304600000000000 : ℝ)*((2847/20000 : ℝ)+(11189/100000 : ℝ))=(250030070032333/250000000000000 : ℝ) by norm_num, show 1+(7126287353685599/20000000000000000000 : ℝ)+(417648539069913/3125000000000000000 : ℝ)=(100048996190018665211/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7126287353685599/20000000000000000000 : ℝ) ≤ ((951555244242751983/951875000000000000 : ℝ)+2*(546566904161/304600000000000 : ℝ)*(2847/20000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (951555244242751983/951875000000000000 : ℝ)+2*(546566904161/304600000000000 : ℝ)*(2847/20000 : ℝ)=(10001749368197481/10000000000000000 : ℝ) by norm_num, show 1+2*(7126287353685599/20000000000000000000 : ℝ)=(10007126287353685599/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (951555244242751983/951875000000000000 : ℝ)*(X 1 0+X 2 0)+(546566904161/304600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (951555244242751983/951875000000000000 : ℝ)) (alpha := (546566904161/304600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (951555244242751983/951875000000000000 : ℝ)*(X 0 1+X 2 1)+(546566904161/304600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (951555244242751983/951875000000000000 : ℝ)) (alpha := (546566904161/304600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (951555244242751983/951875000000000000 : ℝ)*(X 0 2+X 1 2)+(546566904161/304600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (951555244242751983/951875000000000000 : ℝ)) (alpha := (546566904161/304600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540845809/2500000000 : ℝ)*X 0 0+(67434133/125000000 : ℝ)*X 0 1+(1052826771/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133629767/250000000 : ℝ)*X 1 0+(-557412177/2500000000 : ℝ)*X 1 1+(2632066911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345190727/10000000000 : ℝ)*X 2 0+(5264133791/10000000000 : ℝ)*X 2 1+(-445929737/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545449589/1250000000 : ℝ)*X 0 0+(2117717567/5000000000 : ℝ)*X 0 1+(179824441/400000000 : ℝ)*X 0 2+(545449589/1250000000 : ℝ)*X 1 0+(2117717567/5000000000 : ℝ)*X 1 1+(179824441/400000000 : ℝ)*X 1 2+(545449589/1250000000 : ℝ)*X 2 0+(2117717567/5000000000 : ℝ)*X 2 1+(179824441/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163388549/10000000000 : ℝ)*X 0 0+(5264471087/10000000000 : ℝ)*X 0 1+(5394392133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312086723/10000000000 : ℝ)*X 1 0+(-2099390287/10000000000 : ℝ)*X 1 1+(5394392129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656043363/5000000000 : ℝ)*X 2 0+(5394392127/10000000000 : ℝ)*X 2 1+(-524847571/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090901821/2500000000 : ℝ)*X 0 0+(4494939057/10000000000 : ℝ)*X 0 1+(4236109557/10000000000 : ℝ)*X 0 2+(1090901821/2500000000 : ℝ)*X 1 0+(4494939057/10000000000 : ℝ)*X 1 1+(4236109557/10000000000 : ℝ)*X 1 2+(1090901821/2500000000 : ℝ)*X 2 0+(4494939057/10000000000 : ℝ)*X 2 1+(4236109557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (549741036355315930966316121/47593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190838209/10000000000000 : ℝ)*(base19) + (113428749/6250000000000 : ℝ)*(base23) + (85978427/100000000000000 : ℝ)*(lower2) + (50418353/20000000000000 : ℝ)*(upper3) + (180210883/100000000000000 : ℝ)*(upper5) + (5750428881180893/100000000000000 : ℝ)*(major0) + (5750428881180893/100000000000000 : ℝ)*(major1) + (5750428881180893/100000000000000 : ℝ)*(major2) + (7657204475158301/100000000000000 : ℝ)*(sp0) + (7657250657656219/100000000000000 : ℝ)*(sp1) + (3828625375589163/50000000000000 : ℝ)*(sp2) + (120111807825993/3125000000000 : ℝ)*(sp3) + (48090880009/100000000000000 : ℝ)*(sp4) + (13480434209/50000000000000 : ℝ)*(sp7) + (3843604811300193/100000000000000 : ℝ)*(f.failure) + (7657252566038309/100000000000000 : ℝ)*(f.sum) + (107624172506037/15230000000000000000000000000 : ℝ)*base66 + (182536684441804507/11898437500000000000000000000000 : ℝ)*base68 + (383363374415405889/23796875000000000000000000000000 : ℝ)*base70 + (373784308046937139/23796875000000000000000000000000 : ℝ)*base72 + (64887064068567/15230000000000000000000000000 : ℝ)*base74 + (81418854989124639/23796875000000000000000000000000 : ℝ)*base76 + (612127717998280889/23796875000000000000000000000000 : ℝ)*base78 + (554057951816249639/23796875000000000000000000000000 : ℝ)*base80 + (96777087324907/15230000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4257773/2000000000000000000000 : ℝ)*base89 + (4257773/2000000000000000000000 : ℝ)*base91 + (4257773/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (455887117056975263016567717/47593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1773018543/100000000000000 : ℝ)*(base19) + (962773219/50000000000000 : ℝ)*(base23) + (194096657/100000000000000 : ℝ)*(upper3) + (66904459/100000000000000 : ℝ)*(lower4) + (4928501/2500000000000 : ℝ)*(upper5) + (5780263929829883/100000000000000 : ℝ)*(major0) + (5780263929829883/100000000000000 : ℝ)*(major1) + (5780263929829883/100000000000000 : ℝ)*(major2) + (47552235443/100000000000000 : ℝ)*(sp1) + (6389986773/12500000000000 : ℝ)*(sp2) + (7696980888398969/100000000000000 : ℝ)*(sp4) + (7696931563144983/100000000000000 : ℝ)*(sp5) + (7696927842958347/100000000000000 : ℝ)*(sp6) + (772709330394037/20000000000000 : ℝ)*(sp7) + (772709330394037/20000000000000 : ℝ)*(f.failure) + (7696980888398969/100000000000000 : ℝ)*(f.sum) + (35288442499593/15230000000000000000000000000 : ℝ)*base65 + (39063928720801909/23796875000000000000000000000000 : ℝ)*base68 + (34160441606770659/23796875000000000000000000000000 : ℝ)*base70 + (2868106051146799/1487304687500000000000000000000 : ℝ)*base72 + (311015746237/15230000000000000000000000000 : ℝ)*base74 + (426414246225291841/23796875000000000000000000000000 : ℝ)*base75 + (149244636751291841/23796875000000000000000000000000 : ℝ)*base77 + (33433500285333159/23796875000000000000000000000000 : ℝ)*base80 + (10684561813053/15230000000000000000000000000 : ℝ)*base81 + (2849743/400000000000000000000 : ℝ)*base90 + (2849743/400000000000000000000 : ℝ)*base92 + (2849743/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1149_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1149_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1149_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1149_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1149_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1149_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1149_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
