-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1153_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:52.345248+00:00
-- url     : https://prove2.me/submissions/e7fb9f28-c17e-4327-86f0-06838cd6b250

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
theorem support_rectangle_w1153_s0_0 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888334223/10000000000 : ℝ)*x 0 + (1210358239/2000000000 : ℝ)*x 1 + (1195465489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888334223/10000000000 : ℝ)^4173 ≤ (2745442278319/25000000000000 : ℝ)^3149 := by
    have hnat : (1888334223 : ℕ)^4173*25000000000000^3149 ≤ 2745442278319^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888334223 10000000000 2745442278319 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210358239/2000000000 : ℝ)^4173 ≤ (51399203206011/100000000000000 : ℝ)^3149 := by
    have hnat : (1210358239 : ℕ)^4173*100000000000000^3149 ≤ 51399203206011^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210358239 2000000000 51399203206011 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195465489/2500000000 : ℝ)^4173 ≤ (4702378456721/12500000000000 : ℝ)^3149 := by
    have hnat : (1195465489 : ℕ)^4173*12500000000000^3149 ≤ 4702378456721^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195465489 2500000000 4702378456721 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888334223/10000000000 : ℝ), (1210358239/2000000000 : ℝ), (1195465489/2500000000 : ℝ)] ![(2745442278319/25000000000000 : ℝ), (51399203206011/100000000000000 : ℝ), (4702378456721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888334223/10000000000 : ℝ)|^4173 ≤ (2745442278319/25000000000000 : ℝ)^3149
        have hw : |(-1888334223/10000000000 : ℝ)|=(1888334223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1210358239/2000000000 : ℝ)|^4173 ≤ (51399203206011/100000000000000 : ℝ)^3149
        have hw : |(1210358239/2000000000 : ℝ)|=(1210358239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195465489/2500000000 : ℝ)|^4173 ≤ (4702378456721/12500000000000 : ℝ)^3149
        have hw : |(1195465489/2500000000 : ℝ)|=(1195465489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_1 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1379043469/2500000000 : ℝ)*x 0 + (-2616812213/10000000000 : ℝ)*x 1 + (956372383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379043469/2500000000 : ℝ)^4173 ≤ (9091867530061/20000000000000 : ℝ)^3149 := by
    have hnat : (1379043469 : ℕ)^4173*20000000000000^3149 ≤ 9091867530061^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379043469 2500000000 9091867530061 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616812213/10000000000 : ℝ)^4173 ≤ (8460817557513/50000000000000 : ℝ)^3149 := by
    have hnat : (2616812213 : ℕ)^4173*50000000000000^3149 ≤ 8460817557513^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616812213 10000000000 8460817557513 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956372383/2000000000 : ℝ)^4173 ≤ (37619027226333/100000000000000 : ℝ)^3149 := by
    have hnat : (956372383 : ℕ)^4173*100000000000000^3149 ≤ 37619027226333^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956372383 2000000000 37619027226333 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379043469/2500000000 : ℝ), (-2616812213/10000000000 : ℝ), (956372383/2000000000 : ℝ)] ![(9091867530061/20000000000000 : ℝ), (8460817557513/50000000000000 : ℝ), (37619027226333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379043469/2500000000 : ℝ)|^4173 ≤ (9091867530061/20000000000000 : ℝ)^3149
        have hw : |(1379043469/2500000000 : ℝ)|=(1379043469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2616812213/10000000000 : ℝ)|^4173 ≤ (8460817557513/50000000000000 : ℝ)^3149
        have hw : |(-2616812213/10000000000 : ℝ)|=(2616812213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(956372383/2000000000 : ℝ)|^4173 ≤ (37619027226333/100000000000000 : ℝ)^3149
        have hw : |(956372383/2000000000 : ℝ)|=(956372383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_2 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5516174149/10000000000 : ℝ)*x 0 + (2390930941/5000000000 : ℝ)*x 1 + (-523362381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516174149/10000000000 : ℝ)^4173 ≤ (2841208789483/6250000000000 : ℝ)^3149 := by
    have hnat : (5516174149 : ℕ)^4173*6250000000000^3149 ≤ 2841208789483^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516174149 10000000000 2841208789483 6250000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2390930941/5000000000 : ℝ)^4173 ≤ (376190268823/1000000000000 : ℝ)^3149 := by
    have hnat : (2390930941 : ℕ)^4173*1000000000000^3149 ≤ 376190268823^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390930941 5000000000 376190268823 1000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523362381/2000000000 : ℝ)^4173 ≤ (16921632475681/100000000000000 : ℝ)^3149 := by
    have hnat : (523362381 : ℕ)^4173*100000000000000^3149 ≤ 16921632475681^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523362381 2000000000 16921632475681 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516174149/10000000000 : ℝ), (2390930941/5000000000 : ℝ), (-523362381/2000000000 : ℝ)] ![(2841208789483/6250000000000 : ℝ), (376190268823/1000000000000 : ℝ), (16921632475681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516174149/10000000000 : ℝ)|^4173 ≤ (2841208789483/6250000000000 : ℝ)^3149
        have hw : |(5516174149/10000000000 : ℝ)|=(5516174149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2390930941/5000000000 : ℝ)|^4173 ≤ (376190268823/1000000000000 : ℝ)^3149
        have hw : |(2390930941/5000000000 : ℝ)|=(2390930941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523362381/2000000000 : ℝ)|^4173 ≤ (16921632475681/100000000000000 : ℝ)^3149
        have hw : |(-523362381/2000000000 : ℝ)|=(523362381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_3 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840020531/2000000000 : ℝ)*x 0 + (3120574281/10000000000 : ℝ)*x 1 + (5652518281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840020531/2000000000 : ℝ)^4173 ≤ (31677476869061/100000000000000 : ℝ)^3149 := by
    have hnat : (840020531 : ℕ)^4173*100000000000000^3149 ≤ 31677476869061^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840020531 2000000000 31677476869061 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120574281/10000000000 : ℝ)^4173 ≤ (21368222333201/100000000000000 : ℝ)^3149 := by
    have hnat : (3120574281 : ℕ)^4173*100000000000000^3149 ≤ 21368222333201^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120574281 10000000000 21368222333201 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5652518281/10000000000 : ℝ)^4173 ≤ (9390860155651/20000000000000 : ℝ)^3149 := by
    have hnat : (5652518281 : ℕ)^4173*20000000000000^3149 ≤ 9390860155651^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5652518281 10000000000 9390860155651 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840020531/2000000000 : ℝ), (3120574281/10000000000 : ℝ), (5652518281/10000000000 : ℝ)] ![(31677476869061/100000000000000 : ℝ), (21368222333201/100000000000000 : ℝ), (9390860155651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840020531/2000000000 : ℝ)|^4173 ≤ (31677476869061/100000000000000 : ℝ)^3149
        have hw : |(840020531/2000000000 : ℝ)|=(840020531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120574281/10000000000 : ℝ)|^4173 ≤ (21368222333201/100000000000000 : ℝ)^3149
        have hw : |(3120574281/10000000000 : ℝ)|=(3120574281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5652518281/10000000000 : ℝ)|^4173 ≤ (9390860155651/20000000000000 : ℝ)^3149
        have hw : |(5652518281/10000000000 : ℝ)|=(5652518281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_4 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893447437/10000000000 : ℝ)*x 0 + (1203654243/2500000000 : ℝ)*x 1 + (6017883783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893447437/10000000000 : ℝ)^4173 ≤ (11021192522987/100000000000000 : ℝ)^3149 := by
    have hnat : (1893447437 : ℕ)^4173*100000000000000^3149 ≤ 11021192522987^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893447437 10000000000 11021192522987 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203654243/2500000000 : ℝ)^4173 ≤ (37960886438723/100000000000000 : ℝ)^3149 := by
    have hnat : (1203654243 : ℕ)^4173*100000000000000^3149 ≤ 37960886438723^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203654243 2500000000 37960886438723 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6017883783/10000000000 : ℝ)^4173 ≤ (25508960514183/50000000000000 : ℝ)^3149 := by
    have hnat : (6017883783 : ℕ)^4173*50000000000000^3149 ≤ 25508960514183^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017883783 10000000000 25508960514183 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893447437/10000000000 : ℝ), (1203654243/2500000000 : ℝ), (6017883783/10000000000 : ℝ)] ![(11021192522987/100000000000000 : ℝ), (37960886438723/100000000000000 : ℝ), (25508960514183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893447437/10000000000 : ℝ)|^4173 ≤ (11021192522987/100000000000000 : ℝ)^3149
        have hw : |(-1893447437/10000000000 : ℝ)|=(1893447437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203654243/2500000000 : ℝ)|^4173 ≤ (37960886438723/100000000000000 : ℝ)^3149
        have hw : |(1203654243/2500000000 : ℝ)|=(1203654243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6017883783/10000000000 : ℝ)|^4173 ≤ (25508960514183/50000000000000 : ℝ)^3149
        have hw : |(6017883783/10000000000 : ℝ)|=(6017883783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_5 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1292763029/2500000000 : ℝ)*x 0 + (-1380790359/10000000000 : ℝ)*x 1 + (6017883609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292763029/2500000000 : ℝ)^4173 ≤ (41729171506097/100000000000000 : ℝ)^3149 := by
    have hnat : (1292763029 : ℕ)^4173*100000000000000^3149 ≤ 41729171506097^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292763029 2500000000 41729171506097 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380790359/10000000000 : ℝ)^4173 ≤ (7252909405949/100000000000000 : ℝ)^3149 := by
    have hnat : (1380790359 : ℕ)^4173*100000000000000^3149 ≤ 7252909405949^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380790359 10000000000 7252909405949 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6017883609/10000000000 : ℝ)^4173 ≤ (51017919073559/100000000000000 : ℝ)^3149 := by
    have hnat : (6017883609 : ℕ)^4173*100000000000000^3149 ≤ 51017919073559^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017883609 10000000000 51017919073559 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292763029/2500000000 : ℝ), (-1380790359/10000000000 : ℝ), (6017883609/10000000000 : ℝ)] ![(41729171506097/100000000000000 : ℝ), (7252909405949/100000000000000 : ℝ), (51017919073559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292763029/2500000000 : ℝ)|^4173 ≤ (41729171506097/100000000000000 : ℝ)^3149
        have hw : |(1292763029/2500000000 : ℝ)|=(1292763029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1380790359/10000000000 : ℝ)|^4173 ≤ (7252909405949/100000000000000 : ℝ)^3149
        have hw : |(-1380790359/10000000000 : ℝ)|=(1380790359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6017883609/10000000000 : ℝ)|^4173 ≤ (51017919073559/100000000000000 : ℝ)^3149
        have hw : |(6017883609/10000000000 : ℝ)|=(6017883609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_6 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5171052101/10000000000 : ℝ)*x 0 + (6017883663/10000000000 : ℝ)*x 1 + (-276158059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171052101/10000000000 : ℝ)^4173 ≤ (5216146418211/12500000000000 : ℝ)^3149 := by
    have hnat : (5171052101 : ℕ)^4173*12500000000000^3149 ≤ 5216146418211^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171052101 10000000000 5216146418211 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6017883663/10000000000 : ℝ)^4173 ≤ (51017919680223/100000000000000 : ℝ)^3149 := by
    have hnat : (6017883663 : ℕ)^4173*100000000000000^3149 ≤ 51017919680223^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017883663 10000000000 51017919680223 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276158059/2000000000 : ℝ)^4173 ≤ (7252908960457/100000000000000 : ℝ)^3149 := by
    have hnat : (276158059 : ℕ)^4173*100000000000000^3149 ≤ 7252908960457^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276158059 2000000000 7252908960457 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171052101/10000000000 : ℝ), (6017883663/10000000000 : ℝ), (-276158059/2000000000 : ℝ)] ![(5216146418211/12500000000000 : ℝ), (51017919680223/100000000000000 : ℝ), (7252908960457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171052101/10000000000 : ℝ)|^4173 ≤ (5216146418211/12500000000000 : ℝ)^3149
        have hw : |(5171052101/10000000000 : ℝ)|=(5171052101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6017883663/10000000000 : ℝ)|^4173 ≤ (51017919680223/100000000000000 : ℝ)^3149
        have hw : |(6017883663/10000000000 : ℝ)|=(6017883663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276158059/2000000000 : ℝ)|^4173 ≤ (7252908960457/100000000000000 : ℝ)^3149
        have hw : |(-276158059/2000000000 : ℝ)|=(276158059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s0_7 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168411901/400000000 : ℝ)*x 0 + (2793606037/5000000000 : ℝ)*x 1 + (3188178227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168411901/400000000 : ℝ)^4173 ≤ (31779410938703/100000000000000 : ℝ)^3149 := by
    have hnat : (168411901 : ℕ)^4173*100000000000000^3149 ≤ 31779410938703^3149*400000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168411901 400000000 31779410938703 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793606037/5000000000 : ℝ)^4173 ≤ (46236762844903/100000000000000 : ℝ)^3149 := by
    have hnat : (2793606037 : ℕ)^4173*100000000000000^3149 ≤ 46236762844903^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793606037 5000000000 46236762844903 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188178227/10000000000 : ℝ)^4173 ≤ (21983826193981/100000000000000 : ℝ)^3149 := by
    have hnat : (3188178227 : ℕ)^4173*100000000000000^3149 ≤ 21983826193981^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188178227 10000000000 21983826193981 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168411901/400000000 : ℝ), (2793606037/5000000000 : ℝ), (3188178227/10000000000 : ℝ)] ![(31779410938703/100000000000000 : ℝ), (46236762844903/100000000000000 : ℝ), (21983826193981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168411901/400000000 : ℝ)|^4173 ≤ (31779410938703/100000000000000 : ℝ)^3149
        have hw : |(168411901/400000000 : ℝ)|=(168411901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2793606037/5000000000 : ℝ)|^4173 ≤ (46236762844903/100000000000000 : ℝ)^3149
        have hw : |(2793606037/5000000000 : ℝ)|=(2793606037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188178227/10000000000 : ℝ)|^4173 ≤ (21983826193981/100000000000000 : ℝ)^3149
        have hw : |(3188178227/10000000000 : ℝ)|=(3188178227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1153_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (459/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8345/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8345 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8345*1^2048 ≤ 0^2048*1^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8345/2048 : ℝ) ≤ (2390622753096844083/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8345 ≤ (2390622753096844083/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8345*100000000000000000000^2048 ≤ 2390622753096844083^2048*5^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2390622753096844083 100000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2390622753096844083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8345 := by
      have hnat : (1 : ℕ)^2048*1^8345 ≤ 1^8345*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102390622753096844083/100000000000000000000 : ℝ) ≤ (5029073953359717/5000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (102390622753096844083/100000000000000000000 : ℝ)^2048 ≤ (5029073953359717/5000000000000000 : ℝ)^8345 := by
      have hnat : (102390622753096844083 : ℕ)^2048*5000000000000000^8345 ≤ 5029073953359717^8345*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102390622753096844083 100000000000000000000 5029073953359717 5000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029073953359717/5000000000000000 : ℝ)) (X := (102390622753096844083/100000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52390622753096844083/50000000000000000000 : ℝ) ≤ (2529073953359717/2500000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (52390622753096844083/50000000000000000000 : ℝ)^2048 ≤ (2529073953359717/2500000000000000 : ℝ)^8345 := by
      have hnat : (52390622753096844083 : ℕ)^2048*2500000000000000^8345 ≤ 2529073953359717^8345*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52390622753096844083 50000000000000000000 2529073953359717 2500000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529073953359717/2500000000000000 : ℝ)) (X := (52390622753096844083/50000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29073953359717/2000000000000000 : ℝ)*(0 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29073953359717/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2390622753096844083/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29073953359717/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8345/2048 : ℝ) := by
    rw [show (1 : ℝ)+(29073953359717/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029073953359717/5000000000000000 : ℝ) by norm_num, show 1+(2390622753096844083/100000000000000000000 : ℝ)+(0 : ℝ)=(102390622753096844083/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2390622753096844083/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29073953359717/2000000000000000 : ℝ)*(2/5 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29073953359717/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529073953359717/2500000000000000 : ℝ) by norm_num, show 1+2*(2390622753096844083/100000000000000000000 : ℝ)=(52390622753096844083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29073953359717/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29073953359717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29073953359717/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29073953359717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29073953359717/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29073953359717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1888334223/10000000000 : ℝ)*X 0 0+(1210358239/2000000000 : ℝ)*X 0 1+(1195465489/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1379043469/2500000000 : ℝ)*X 1 0+(-2616812213/10000000000 : ℝ)*X 1 1+(956372383/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516174149/10000000000 : ℝ)*X 2 0+(2390930941/5000000000 : ℝ)*X 2 1+(-523362381/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840020531/2000000000 : ℝ)*X 0 0+(3120574281/10000000000 : ℝ)*X 0 1+(5652518281/10000000000 : ℝ)*X 0 2+(840020531/2000000000 : ℝ)*X 1 0+(3120574281/10000000000 : ℝ)*X 1 1+(5652518281/10000000000 : ℝ)*X 1 2+(840020531/2000000000 : ℝ)*X 2 0+(3120574281/10000000000 : ℝ)*X 2 1+(5652518281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1893447437/10000000000 : ℝ)*X 0 0+(1203654243/2500000000 : ℝ)*X 0 1+(6017883783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292763029/2500000000 : ℝ)*X 1 0+(-1380790359/10000000000 : ℝ)*X 1 1+(6017883609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171052101/10000000000 : ℝ)*X 2 0+(6017883663/10000000000 : ℝ)*X 2 1+(-276158059/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168411901/400000000 : ℝ)*X 0 0+(2793606037/5000000000 : ℝ)*X 0 1+(3188178227/10000000000 : ℝ)*X 0 2+(168411901/400000000 : ℝ)*X 1 0+(2793606037/5000000000 : ℝ)*X 1 1+(3188178227/10000000000 : ℝ)*X 1 2+(168411901/400000000 : ℝ)*X 2 0+(2793606037/5000000000 : ℝ)*X 2 1+(3188178227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30871611902151252140637/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (474897/2500000000000 : ℝ)*(base1) + (632685407/100000000000000 : ℝ)*(base19) + (600311647/100000000000000 : ℝ)*(base23) + (71345219/100000000000000 : ℝ)*(base24) + (150836117/100000000000000 : ℝ)*(upper3) + (295601033829587/50000000000000 : ℝ)*(major0) + (295601033829587/50000000000000 : ℝ)*(major1) + (295601033829587/50000000000000 : ℝ)*(major2) + (1230386710823/156250000000 : ℝ)*(sp0) + (393724097159967/50000000000000 : ℝ)*(sp1) + (31497926213939/4000000000000 : ℝ)*(sp2) + (197477035045447/50000000000000 : ℝ)*(sp3) + (1351074501/100000000000000 : ℝ)*(sp4) + (1136901931/100000000000000 : ℝ)*(sp7) + (78991045197741/20000000000000 : ℝ)*(f.failure) + (787448827005341/100000000000000 : ℝ)*(f.sum) + (3971603853121/50000000000000000000000000000 : ℝ)*base66 + (180773859453121/100000000000000000000000000000 : ℝ)*base68 + (548833626853121/100000000000000000000000000000 : ℝ)*base70 + (235925364353121/100000000000000000000000000000 : ℝ)*base72 + (16270580246879/50000000000000000000000000000 : ℝ)*base73 + (263966827553121/100000000000000000000000000000 : ℝ)*base76 + (472398223453121/100000000000000000000000000000 : ℝ)*base78 + (461980717253121/100000000000000000000000000000 : ℝ)*base80 + (336041245253121/50000000000000000000000000000 : ℝ)*base82 + (14356357/2000000000000000000000 : ℝ)*base89 + (14356357/2000000000000000000000 : ℝ)*base91 + (14356357/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3451952083382408864709/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70583253/100000000000000 : ℝ)*(base1) + (341613619/25000000000000 : ℝ)*(base19) + (10909433/800000000000 : ℝ)*(base23) + (146236029/100000000000000 : ℝ)*(upper3) + (162351601/100000000000000 : ℝ)*(upper5) + (15598819792641/2500000000000 : ℝ)*(major0) + (15598819792641/2500000000000 : ℝ)*(major1) + (15598819792641/2500000000000 : ℝ)*(major2) + (1379284987/50000000000000 : ℝ)*(sp1) + (2753104559/100000000000000 : ℝ)*(sp2) + (831070973979193/100000000000000 : ℝ)*(sp4) + (831066778371491/100000000000000 : ℝ)*(sp5) + (25970837081633/3125000000000 : ℝ)*(sp6) + (416834425327969/100000000000000 : ℝ)*(sp7) + (208417247955611/50000000000000 : ℝ)*(f.failure) + (41553545169797/5000000000000 : ℝ)*(f.sum) + (3547226482597/2500000000000000000000000000 : ℝ)*base65 + (40842415932597/5000000000000000000000000000 : ℝ)*base67 + (1668932032597/5000000000000000000000000000 : ℝ)*base69 + (12537217917597/5000000000000000000000000000 : ℝ)*base71 + (7501347505097/2500000000000000000000000000 : ℝ)*base73 + (4664911482597/5000000000000000000000000000 : ℝ)*base75 + (34314363082597/5000000000000000000000000000 : ℝ)*base77 + (54103265082597/5000000000000000000000000000 : ℝ)*base79 + (8626028927403/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (21366653/5000000000000000000000 : ℝ)*base90 + (21366653/5000000000000000000000 : ℝ)*base92 + (21366653/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1153_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1153_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1153_s1_0 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092201851/10000000000 : ℝ)*x 0 + (5698576591/10000000000 : ℝ)*x 1 + (5004564993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092201851/10000000000 : ℝ)^4173 ≤ (6289928291369/50000000000000 : ℝ)^3149 := by
    have hnat : (2092201851 : ℕ)^4173*50000000000000^3149 ≤ 6289928291369^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092201851 10000000000 6289928291369 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5698576591/10000000000 : ℝ)^4173 ≤ (47461981958947/100000000000000 : ℝ)^3149 := by
    have hnat : (5698576591 : ℕ)^4173*100000000000000^3149 ≤ 47461981958947^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5698576591 10000000000 47461981958947 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5004564993/10000000000 : ℝ)^4173 ≤ (7991632286933/20000000000000 : ℝ)^3149 := by
    have hnat : (5004564993 : ℕ)^4173*20000000000000^3149 ≤ 7991632286933^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004564993 10000000000 7991632286933 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092201851/10000000000 : ℝ), (5698576591/10000000000 : ℝ), (5004564993/10000000000 : ℝ)] ![(6289928291369/50000000000000 : ℝ), (47461981958947/100000000000000 : ℝ), (7991632286933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092201851/10000000000 : ℝ)|^4173 ≤ (6289928291369/50000000000000 : ℝ)^3149
        have hw : |(-2092201851/10000000000 : ℝ)|=(2092201851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5698576591/10000000000 : ℝ)|^4173 ≤ (47461981958947/100000000000000 : ℝ)^3149
        have hw : |(5698576591/10000000000 : ℝ)|=(5698576591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5004564993/10000000000 : ℝ)|^4173 ≤ (7991632286933/20000000000000 : ℝ)^3149
        have hw : |(5004564993/10000000000 : ℝ)|=(5004564993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_1 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354629691/2500000000 : ℝ)*x 0 + (-2466519321/10000000000 : ℝ)*x 1 + (5004564119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354629691/2500000000 : ℝ)^4173 ≤ (22197966018801/50000000000000 : ℝ)^3149 := by
    have hnat : (1354629691 : ℕ)^4173*50000000000000^3149 ≤ 22197966018801^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354629691 2500000000 22197966018801 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2466519321/10000000000 : ℝ)^4173 ≤ (15645915752901/100000000000000 : ℝ)^3149 := by
    have hnat : (2466519321 : ℕ)^4173*100000000000000^3149 ≤ 15645915752901^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466519321 10000000000 15645915752901 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5004564119/10000000000 : ℝ)^4173 ≤ (39958152187123/100000000000000 : ℝ)^3149 := by
    have hnat : (5004564119 : ℕ)^4173*100000000000000^3149 ≤ 39958152187123^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004564119 10000000000 39958152187123 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354629691/2500000000 : ℝ), (-2466519321/10000000000 : ℝ), (5004564119/10000000000 : ℝ)] ![(22197966018801/50000000000000 : ℝ), (15645915752901/100000000000000 : ℝ), (39958152187123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354629691/2500000000 : ℝ)|^4173 ≤ (22197966018801/50000000000000 : ℝ)^3149
        have hw : |(1354629691/2500000000 : ℝ)|=(1354629691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2466519321/10000000000 : ℝ)|^4173 ≤ (15645915752901/100000000000000 : ℝ)^3149
        have hw : |(-2466519321/10000000000 : ℝ)|=(2466519321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5004564119/10000000000 : ℝ)|^4173 ≤ (39958152187123/100000000000000 : ℝ)^3149
        have hw : |(5004564119/10000000000 : ℝ)|=(5004564119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_2 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541852083/1000000000 : ℝ)*x 0 + (5004562271/10000000000 : ℝ)*x 1 + (-2466518979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541852083/1000000000 : ℝ)^4173 ≤ (11098988617409/25000000000000 : ℝ)^3149 := by
    have hnat : (541852083 : ℕ)^4173*25000000000000^3149 ≤ 11098988617409^3149*1000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541852083 1000000000 11098988617409 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5004562271/10000000000 : ℝ)^4173 ≤ (3995813263397/10000000000000 : ℝ)^3149 := by
    have hnat : (5004562271 : ℕ)^4173*10000000000000^3149 ≤ 3995813263397^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004562271 10000000000 3995813263397 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2466518979/10000000000 : ℝ)^4173 ≤ (1564591287803/10000000000000 : ℝ)^3149 := by
    have hnat : (2466518979 : ℕ)^4173*10000000000000^3149 ≤ 1564591287803^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466518979 10000000000 1564591287803 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541852083/1000000000 : ℝ), (5004562271/10000000000 : ℝ), (-2466518979/10000000000 : ℝ)] ![(11098988617409/25000000000000 : ℝ), (3995813263397/10000000000000 : ℝ), (1564591287803/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541852083/1000000000 : ℝ)|^4173 ≤ (11098988617409/25000000000000 : ℝ)^3149
        have hw : |(541852083/1000000000 : ℝ)|=(541852083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5004562271/10000000000 : ℝ)|^4173 ≤ (3995813263397/10000000000000 : ℝ)^3149
        have hw : |(5004562271/10000000000 : ℝ)|=(5004562271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2466518979/10000000000 : ℝ)|^4173 ≤ (1564591287803/10000000000000 : ℝ)^3149
        have hw : |(-2466518979/10000000000 : ℝ)|=(2466518979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_3 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158253307/5000000000 : ℝ)*x 0 + (1839552491/5000000000 : ℝ)*x 1 + (2531399589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158253307/5000000000 : ℝ)^4173 ≤ (32846100714861/100000000000000 : ℝ)^3149 := by
    have hnat : (2158253307 : ℕ)^4173*100000000000000^3149 ≤ 32846100714861^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158253307 5000000000 32846100714861 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839552491/5000000000 : ℝ)^4173 ≤ (26578416000759/100000000000000 : ℝ)^3149 := by
    have hnat : (1839552491 : ℕ)^4173*100000000000000^3149 ≤ 26578416000759^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839552491 5000000000 26578416000759 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2531399589/5000000000 : ℝ)^4173 ≤ (20287741635201/50000000000000 : ℝ)^3149 := by
    have hnat : (2531399589 : ℕ)^4173*50000000000000^3149 ≤ 20287741635201^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531399589 5000000000 20287741635201 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158253307/5000000000 : ℝ), (1839552491/5000000000 : ℝ), (2531399589/5000000000 : ℝ)] ![(32846100714861/100000000000000 : ℝ), (26578416000759/100000000000000 : ℝ), (20287741635201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158253307/5000000000 : ℝ)|^4173 ≤ (32846100714861/100000000000000 : ℝ)^3149
        have hw : |(2158253307/5000000000 : ℝ)|=(2158253307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1839552491/5000000000 : ℝ)|^4173 ≤ (26578416000759/100000000000000 : ℝ)^3149
        have hw : |(1839552491/5000000000 : ℝ)|=(1839552491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2531399589/5000000000 : ℝ)|^4173 ≤ (20287741635201/50000000000000 : ℝ)^3149
        have hw : |(2531399589/5000000000 : ℝ)|=(2531399589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_4 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104649867/500000000 : ℝ)*x 0 + (5014001411/10000000000 : ℝ)*x 1 + (2844475321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104649867/500000000 : ℝ)^4173 ≤ (6293097704551/50000000000000 : ℝ)^3149 := by
    have hnat : (104649867 : ℕ)^4173*50000000000000^3149 ≤ 6293097704551^3149*500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104649867 500000000 6293097704551 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014001411/10000000000 : ℝ)^4173 ≤ (8011607210261/20000000000000 : ℝ)^3149 := by
    have hnat : (5014001411 : ℕ)^4173*20000000000000^3149 ≤ 8011607210261^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014001411 10000000000 8011607210261 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2844475321/5000000000 : ℝ)^4173 ≤ (9471153706407/20000000000000 : ℝ)^3149 := by
    have hnat : (2844475321 : ℕ)^4173*20000000000000^3149 ≤ 9471153706407^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844475321 5000000000 9471153706407 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104649867/500000000 : ℝ), (5014001411/10000000000 : ℝ), (2844475321/5000000000 : ℝ)] ![(6293097704551/50000000000000 : ℝ), (8011607210261/20000000000000 : ℝ), (9471153706407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104649867/500000000 : ℝ)|^4173 ≤ (6293097704551/50000000000000 : ℝ)^3149
        have hw : |(-104649867/500000000 : ℝ)|=(104649867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014001411/10000000000 : ℝ)|^4173 ≤ (8011607210261/20000000000000 : ℝ)^3149
        have hw : |(5014001411/10000000000 : ℝ)|=(5014001411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2844475321/5000000000 : ℝ)|^4173 ≤ (9471153706407/20000000000000 : ℝ)^3149
        have hw : |(2844475321/5000000000 : ℝ)|=(2844475321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_5 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5240488609/10000000000 : ℝ)*x 0 + (-445532201/2500000000 : ℝ)*x 1 + (5688954239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240488609/10000000000 : ℝ)^4173 ≤ (42473335500911/100000000000000 : ℝ)^3149 := by
    have hnat : (5240488609 : ℕ)^4173*100000000000000^3149 ≤ 42473335500911^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240488609 10000000000 42473335500911 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445532201/2500000000 : ℝ)^4173 ≤ (5085428133727/50000000000000 : ℝ)^3149 := by
    have hnat : (445532201 : ℕ)^4173*50000000000000^3149 ≤ 5085428133727^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445532201 2500000000 5085428133727 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5688954239/10000000000 : ℝ)^4173 ≤ (47355808210689/100000000000000 : ℝ)^3149 := by
    have hnat : (5688954239 : ℕ)^4173*100000000000000^3149 ≤ 47355808210689^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688954239 10000000000 47355808210689 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240488609/10000000000 : ℝ), (-445532201/2500000000 : ℝ), (5688954239/10000000000 : ℝ)] ![(42473335500911/100000000000000 : ℝ), (5085428133727/50000000000000 : ℝ), (47355808210689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240488609/10000000000 : ℝ)|^4173 ≤ (42473335500911/100000000000000 : ℝ)^3149
        have hw : |(5240488609/10000000000 : ℝ)|=(5240488609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445532201/2500000000 : ℝ)|^4173 ≤ (5085428133727/50000000000000 : ℝ)^3149
        have hw : |(-445532201/2500000000 : ℝ)|=(445532201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5688954239/10000000000 : ℝ)|^4173 ≤ (47355808210689/100000000000000 : ℝ)^3149
        have hw : |(5688954239/10000000000 : ℝ)|=(5688954239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_6 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5240487399/10000000000 : ℝ)*x 0 + (568895593/1000000000 : ℝ)*x 1 + (-891064029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240487399/10000000000 : ℝ)^4173 ≤ (5309165313129/12500000000000 : ℝ)^3149 := by
    have hnat : (5240487399 : ℕ)^4173*12500000000000^3149 ≤ 5309165313129^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240487399 10000000000 5309165313129 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568895593/1000000000 : ℝ)^4173 ≤ (47355826864181/100000000000000 : ℝ)^3149 := by
    have hnat : (568895593 : ℕ)^4173*100000000000000^3149 ≤ 47355826864181^3149*1000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568895593 1000000000 47355826864181 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891064029/5000000000 : ℝ)^4173 ≤ (635678164091/6250000000000 : ℝ)^3149 := by
    have hnat : (891064029 : ℕ)^4173*6250000000000^3149 ≤ 635678164091^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891064029 5000000000 635678164091 6250000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240487399/10000000000 : ℝ), (568895593/1000000000 : ℝ), (-891064029/5000000000 : ℝ)] ![(5309165313129/12500000000000 : ℝ), (47355826864181/100000000000000 : ℝ), (635678164091/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240487399/10000000000 : ℝ)|^4173 ≤ (5309165313129/12500000000000 : ℝ)^3149
        have hw : |(5240487399/10000000000 : ℝ)|=(5240487399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568895593/1000000000 : ℝ)|^4173 ≤ (47355826864181/100000000000000 : ℝ)^3149
        have hw : |(568895593/1000000000 : ℝ)|=(568895593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891064029/5000000000 : ℝ)|^4173 ≤ (635678164091/6250000000000 : ℝ)^3149
        have hw : |(-891064029/5000000000 : ℝ)|=(891064029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_7 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159040699/5000000000 : ℝ)*x 0 + (1008797247/2000000000 : ℝ)*x 1 + (462286029/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159040699/5000000000 : ℝ)^4173 ≤ (32861981570057/100000000000000 : ℝ)^3149 := by
    have hnat : (2159040699 : ℕ)^4173*100000000000000^3149 ≤ 32861981570057^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159040699 5000000000 32861981570057 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008797247/2000000000 : ℝ)^4173 ≤ (40375799497111/100000000000000 : ℝ)^3149 := by
    have hnat : (1008797247 : ℕ)^4173*100000000000000^3149 ≤ 40375799497111^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008797247 2000000000 40375799497111 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462286029/1250000000 : ℝ)^4173 ≤ (26762218926287/100000000000000 : ℝ)^3149 := by
    have hnat : (462286029 : ℕ)^4173*100000000000000^3149 ≤ 26762218926287^3149*1250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462286029 1250000000 26762218926287 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159040699/5000000000 : ℝ), (1008797247/2000000000 : ℝ), (462286029/1250000000 : ℝ)] ![(32861981570057/100000000000000 : ℝ), (40375799497111/100000000000000 : ℝ), (26762218926287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159040699/5000000000 : ℝ)|^4173 ≤ (32861981570057/100000000000000 : ℝ)^3149
        have hw : |(2159040699/5000000000 : ℝ)|=(2159040699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008797247/2000000000 : ℝ)|^4173 ≤ (40375799497111/100000000000000 : ℝ)^3149
        have hw : |(1008797247/2000000000 : ℝ)|=(1008797247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(462286029/1250000000 : ℝ)|^4173 ≤ (26762218926287/100000000000000 : ℝ)^3149
        have hw : |(462286029/1250000000 : ℝ)|=(462286029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_8 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5775987/10000000000 : ℝ)*x 0 + (219616371/400000000 : ℝ)*x 1 + (6353021707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5775987/10000000000 : ℝ)^4173 ≤ (5111677017/100000000000000 : ℝ)^3149 := by
    have hnat : (5775987 : ℕ)^4173*100000000000000^3149 ≤ 5111677017^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5775987 10000000000 5111677017 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219616371/400000000 : ℝ)^4173 ≤ (9035635467661/20000000000000 : ℝ)^3149 := by
    have hnat : (219616371 : ℕ)^4173*20000000000000^3149 ≤ 9035635467661^3149*400000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219616371 400000000 9035635467661 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6353021707/10000000000 : ℝ)^4173 ≤ (13704177744377/25000000000000 : ℝ)^3149 := by
    have hnat : (6353021707 : ℕ)^4173*25000000000000^3149 ≤ 13704177744377^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6353021707 10000000000 13704177744377 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5775987/10000000000 : ℝ), (219616371/400000000 : ℝ), (6353021707/10000000000 : ℝ)] ![(5111677017/100000000000000 : ℝ), (9035635467661/20000000000000 : ℝ), (13704177744377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5775987/10000000000 : ℝ)|^4173 ≤ (5111677017/100000000000000 : ℝ)^3149
        have hw : |(5775987/10000000000 : ℝ)|=(5775987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219616371/400000000 : ℝ)|^4173 ≤ (9035635467661/20000000000000 : ℝ)^3149
        have hw : |(219616371/400000000 : ℝ)|=(219616371/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6353021707/10000000000 : ℝ)|^4173 ≤ (13704177744377/25000000000000 : ℝ)^3149
        have hw : |(6353021707/10000000000 : ℝ)|=(6353021707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_9 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (491063591/5000000000 : ℝ)*x 0 + (-2201189873/5000000000 : ℝ)*x 1 + (6943412437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491063591/5000000000 : ℝ)^4173 ≤ (230891646191/5000000000000 : ℝ)^3149 := by
    have hnat : (491063591 : ℕ)^4173*5000000000000^3149 ≤ 230891646191^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491063591 5000000000 230891646191 5000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201189873/5000000000 : ℝ)^4173 ≤ (16857411266619/50000000000000 : ℝ)^3149 := by
    have hnat : (2201189873 : ℕ)^4173*50000000000000^3149 ≤ 16857411266619^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201189873 5000000000 16857411266619 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6943412437/10000000000 : ℝ)^4173 ≤ (61667344529363/100000000000000 : ℝ)^3149 := by
    have hnat : (6943412437 : ℕ)^4173*100000000000000^3149 ≤ 61667344529363^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6943412437 10000000000 61667344529363 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(491063591/5000000000 : ℝ), (-2201189873/5000000000 : ℝ), (6943412437/10000000000 : ℝ)] ![(230891646191/5000000000000 : ℝ), (16857411266619/50000000000000 : ℝ), (61667344529363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(491063591/5000000000 : ℝ)|^4173 ≤ (230891646191/5000000000000 : ℝ)^3149
        have hw : |(491063591/5000000000 : ℝ)|=(491063591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2201189873/5000000000 : ℝ)|^4173 ≤ (16857411266619/50000000000000 : ℝ)^3149
        have hw : |(-2201189873/5000000000 : ℝ)|=(2201189873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6943412437/10000000000 : ℝ)|^4173 ≤ (61667344529363/100000000000000 : ℝ)^3149
        have hw : |(6943412437/10000000000 : ℝ)|=(6943412437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_10 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (196423923/2000000000 : ℝ)*x 0 + (8679243/12500000 : ℝ)*x 1 + (-4402405309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196423923/2000000000 : ℝ)^4173 ≤ (923557155031/20000000000000 : ℝ)^3149 := by
    have hnat : (196423923 : ℕ)^4173*20000000000000^3149 ≤ 923557155031^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196423923 2000000000 923557155031 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8679243/12500000 : ℝ)^4173 ≤ (7708391530373/12500000000000 : ℝ)^3149 := by
    have hnat : (8679243 : ℕ)^4173*12500000000000^3149 ≤ 7708391530373^3149*12500000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8679243 12500000 7708391530373 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402405309/10000000000 : ℝ)^4173 ≤ (6743016392783/20000000000000 : ℝ)^3149 := by
    have hnat : (4402405309 : ℕ)^4173*20000000000000^3149 ≤ 6743016392783^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402405309 10000000000 6743016392783 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(196423923/2000000000 : ℝ), (8679243/12500000 : ℝ), (-4402405309/10000000000 : ℝ)] ![(923557155031/20000000000000 : ℝ), (7708391530373/12500000000000 : ℝ), (6743016392783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(196423923/2000000000 : ℝ)|^4173 ≤ (923557155031/20000000000000 : ℝ)^3149
        have hw : |(196423923/2000000000 : ℝ)|=(196423923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8679243/12500000 : ℝ)|^4173 ≤ (7708391530373/12500000000000 : ℝ)^3149
        have hw : |(8679243/12500000 : ℝ)|=(8679243/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4402405309/10000000000 : ℝ)|^4173 ≤ (6743016392783/20000000000000 : ℝ)^3149
        have hw : |(-4402405309/10000000000 : ℝ)|=(4402405309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s1_11 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (59832307/312500000 : ℝ)*x 0 + (5809302711/10000000000 : ℝ)*x 1 + (5020529787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59832307/312500000 : ℝ)^4173 ≤ (11184910124223/100000000000000 : ℝ)^3149 := by
    have hnat : (59832307 : ℕ)^4173*100000000000000^3149 ≤ 11184910124223^3149*312500000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59832307 312500000 11184910124223 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5809302711/10000000000 : ℝ)^4173 ≤ (12171980499319/25000000000000 : ℝ)^3149 := by
    have hnat : (5809302711 : ℕ)^4173*25000000000000^3149 ≤ 12171980499319^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5809302711 10000000000 12171980499319 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020529787/10000000000 : ℝ)^4173 ≤ (40127167870867/100000000000000 : ℝ)^3149 := by
    have hnat : (5020529787 : ℕ)^4173*100000000000000^3149 ≤ 40127167870867^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020529787 10000000000 40127167870867 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(59832307/312500000 : ℝ), (5809302711/10000000000 : ℝ), (5020529787/10000000000 : ℝ)] ![(11184910124223/100000000000000 : ℝ), (12171980499319/25000000000000 : ℝ), (40127167870867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(59832307/312500000 : ℝ)|^4173 ≤ (11184910124223/100000000000000 : ℝ)^3149
        have hw : |(59832307/312500000 : ℝ)|=(59832307/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5809302711/10000000000 : ℝ)|^4173 ≤ (12171980499319/25000000000000 : ℝ)^3149
        have hw : |(5809302711/10000000000 : ℝ)|=(5809302711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020529787/10000000000 : ℝ)|^4173 ≤ (40127167870867/100000000000000 : ℝ)^3149
        have hw : |(5020529787/10000000000 : ℝ)|=(5020529787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1153_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20387/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (459/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (14843684459/50000000000000000000 : ℝ) := by
    have hpowers : (459/100000 : ℝ)^8345 ≤ (14843684459/50000000000000000000 : ℝ)^2048 := by
      have hnat : (459 : ℕ)^8345*50000000000000000000^2048 ≤ 14843684459^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 100000 14843684459 50000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/100000 : ℝ)) (X := (14843684459/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27773/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (108132410138479243/20000000000000000000 : ℝ) := by
    have hpowers : (27773/100000 : ℝ)^8345 ≤ (108132410138479243/20000000000000000000 : ℝ)^2048 := by
      have hnat : (27773 : ℕ)^8345*20000000000000000000^2048 ≤ 108132410138479243^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27773 100000 108132410138479243 20000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27773/100000 : ℝ)) (X := (108132410138479243/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000014843684459/25000000000000000000 : ℝ) ≤ (5000000000728577/5000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (25000000014843684459/25000000000000000000 : ℝ)^2048 ≤ (5000000000728577/5000000000000000 : ℝ)^8345 := by
      have hnat : (25000000014843684459 : ℕ)^2048*5000000000000000^8345 ≤ 5000000000728577^8345*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000014843684459 25000000000000000000 5000000000728577 5000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000728577/5000000000000000 : ℝ)) (X := (25000000014843684459/25000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100540662080379765133/100000000000000000000 : ℝ) ≤ (2002648350757137/2000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (100540662080379765133/100000000000000000000 : ℝ)^2048 ≤ (2002648350757137/2000000000000000 : ℝ)^8345 := by
      have hnat : (100540662080379765133 : ℕ)^2048*2000000000000000^8345 ≤ 2002648350757137^8345*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100540662080379765133 100000000000000000000 2002648350757137 2000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002648350757137/2000000000000000 : ℝ)) (X := (100540662080379765133/100000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10108132410138479243/10000000000000000000 : ℝ) ≤ (1253310438264277/1250000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (10108132410138479243/10000000000000000000 : ℝ)^2048 ≤ (1253310438264277/1250000000000000 : ℝ)^8345 := by
      have hnat : (10108132410138479243 : ℕ)^2048*1250000000000000^8345 ≤ 1253310438264277^8345*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10108132410138479243 10000000000000000000 1253310438264277 1250000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253310438264277/1250000000000000 : ℝ)) (X := (10108132410138479243/10000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14843684459/50000000000000000000 : ℝ) ≤ ((136563922055581556449/136570000000000000000 : ℝ)+2*(13241752328531/2731400000000000 : ℝ)*(459/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (136563922055581556449/136570000000000000000 : ℝ)+2*(13241752328531/2731400000000000 : ℝ)*(459/100000 : ℝ)=(5000000000728577/5000000000000000 : ℝ) by norm_num, show 1+2*(14843684459/50000000000000000000 : ℝ)=(25000000014843684459/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(108132410138479243/20000000000000000000 : ℝ)+(14843684459/50000000000000000000 : ℝ) ≤ ((136563922055581556449/136570000000000000000 : ℝ)+(13241752328531/2731400000000000 : ℝ)*((27773/100000 : ℝ)+(459/100000 : ℝ)))^(8345/2048 : ℝ) := by
    rw [show (136563922055581556449/136570000000000000000 : ℝ)+(13241752328531/2731400000000000 : ℝ)*((27773/100000 : ℝ)+(459/100000 : ℝ))=(2002648350757137/2000000000000000 : ℝ) by norm_num, show 1+(108132410138479243/20000000000000000000 : ℝ)+(14843684459/50000000000000000000 : ℝ)=(100540662080379765133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(108132410138479243/20000000000000000000 : ℝ) ≤ ((136563922055581556449/136570000000000000000 : ℝ)+2*(13241752328531/2731400000000000 : ℝ)*(27773/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (136563922055581556449/136570000000000000000 : ℝ)+2*(13241752328531/2731400000000000 : ℝ)*(27773/100000 : ℝ)=(1253310438264277/1250000000000000 : ℝ) by norm_num, show 1+2*(108132410138479243/20000000000000000000 : ℝ)=(10108132410138479243/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (136563922055581556449/136570000000000000000 : ℝ)*(X 1 0+X 2 0)+(13241752328531/2731400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (459/100000 : ℝ)) (hi := (27773/100000 : ℝ)) (c := (136563922055581556449/136570000000000000000 : ℝ)) (alpha := (13241752328531/2731400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (136563922055581556449/136570000000000000000 : ℝ)*(X 0 1+X 2 1)+(13241752328531/2731400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (459/100000 : ℝ)) (hi := (27773/100000 : ℝ)) (c := (136563922055581556449/136570000000000000000 : ℝ)) (alpha := (13241752328531/2731400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (136563922055581556449/136570000000000000000 : ℝ)*(X 0 2+X 1 2)+(13241752328531/2731400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (459/100000 : ℝ)) (hi := (27773/100000 : ℝ)) (c := (136563922055581556449/136570000000000000000 : ℝ)) (alpha := (13241752328531/2731400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2092201851/10000000000 : ℝ)*X 0 0+(5698576591/10000000000 : ℝ)*X 0 1+(5004564993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354629691/2500000000 : ℝ)*X 1 0+(-2466519321/10000000000 : ℝ)*X 1 1+(5004564119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((541852083/1000000000 : ℝ)*X 2 0+(5004562271/10000000000 : ℝ)*X 2 1+(-2466518979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158253307/5000000000 : ℝ)*X 0 0+(1839552491/5000000000 : ℝ)*X 0 1+(2531399589/5000000000 : ℝ)*X 0 2+(2158253307/5000000000 : ℝ)*X 1 0+(1839552491/5000000000 : ℝ)*X 1 1+(2531399589/5000000000 : ℝ)*X 1 2+(2158253307/5000000000 : ℝ)*X 2 0+(1839552491/5000000000 : ℝ)*X 2 1+(2531399589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104649867/500000000 : ℝ)*X 0 0+(5014001411/10000000000 : ℝ)*X 0 1+(2844475321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5240488609/10000000000 : ℝ)*X 1 0+(-445532201/2500000000 : ℝ)*X 1 1+(5688954239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5240487399/10000000000 : ℝ)*X 2 0+(568895593/1000000000 : ℝ)*X 2 1+(-891064029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159040699/5000000000 : ℝ)*X 0 0+(1008797247/2000000000 : ℝ)*X 0 1+(462286029/1250000000 : ℝ)*X 0 2+(2159040699/5000000000 : ℝ)*X 1 0+(1008797247/2000000000 : ℝ)*X 1 1+(462286029/1250000000 : ℝ)*X 1 2+(2159040699/5000000000 : ℝ)*X 2 0+(1008797247/2000000000 : ℝ)*X 2 1+(462286029/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5775987/10000000000 : ℝ)*X 0 0+(219616371/400000000 : ℝ)*X 0 1+(6353021707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((491063591/5000000000 : ℝ)*X 1 0+(-2201189873/5000000000 : ℝ)*X 1 1+(6943412437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((196423923/2000000000 : ℝ)*X 2 0+(8679243/12500000 : ℝ)*X 2 1+(-4402405309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((59832307/312500000 : ℝ)*X 0 0+(5809302711/10000000000 : ℝ)*X 0 1+(5020529787/10000000000 : ℝ)*X 0 2+(59832307/312500000 : ℝ)*X 1 0+(5809302711/10000000000 : ℝ)*X 1 1+(5020529787/10000000000 : ℝ)*X 1 2+(59832307/312500000 : ℝ)*X 2 0+(5809302711/10000000000 : ℝ)*X 2 1+(5020529787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13006336216714666513373958459/1707125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4091831/2500000000000 : ℝ)*(lower2) + (270451003431499/25000000000000 : ℝ)*(major0) + (270451003431499/25000000000000 : ℝ)*(major1) + (270451003431499/25000000000000 : ℝ)*(major2) + (720450021780823/50000000000000 : ℝ)*(sp0) + (1440899407072027/100000000000000 : ℝ)*(sp1) + (72044879450683/5000000000000 : ℝ)*(sp2) + (180675726623463/25000000000000 : ℝ)*(sp3) + (3646012923/100000000000000 : ℝ)*(sp4) + (453232929/12500000000000 : ℝ)*(sp5) + (5205219721/100000000000000 : ℝ)*(sp6) + (656639111/100000000000000 : ℝ)*(sp9) + (223835297/25000000000000 : ℝ)*(sp10) + (3679443/312500000000 : ℝ)*(sp11) + (722704083915611/100000000000000 : ℝ)*(f.failure) + (1440903689574569/100000000000000 : ℝ)*(f.sum) + (23665720808977/4267812500000000000000000000 : ℝ)*base66 + (37798953868501112949/3414250000000000000000000000000000 : ℝ)*base68 + (33130303833163362949/3414250000000000000000000000000000 : ℝ)*base70 + (25005069859953862949/3414250000000000000000000000000000 : ℝ)*base72 + (40961743573383/68285000000000000000000000000 : ℝ)*base73 + (50106316484180362949/3414250000000000000000000000000000 : ℝ)*base76 + (59767120282933112949/3414250000000000000000000000000000 : ℝ)*base78 + (37514893222577862949/3414250000000000000000000000000000 : ℝ)*base80 + (85841330572243/17071250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15553347/10000000000000000000000 : ℝ)*base89 + (15553347/10000000000000000000000 : ℝ)*base91 + (15553347/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6518351487563238777410656773/3414250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4585377/25000000000000 : ℝ)*(upper3) + (16332989/12500000000000 : ℝ)*(lower4) + (556175462933347/50000000000000 : ℝ)*(major0) + (556175462933347/50000000000000 : ℝ)*(major1) + (556175462933347/50000000000000 : ℝ)*(major2) + (805129359/20000000000000 : ℝ)*(sp1) + (3377939011/50000000000000 : ℝ)*(sp2) + (1174048639/100000000000000 : ℝ)*(sp3) + (1481587100660391/100000000000000 : ℝ)*(sp4) + (37039666879027/2500000000000 : ℝ)*(sp5) + (1481583944929853/100000000000000 : ℝ)*(sp6) + (371554524249283/50000000000000 : ℝ)*(sp7) + (900036871/25000000000000 : ℝ)*(sp8) + (432369807/50000000000000 : ℝ)*(sp11) + (37155554364341/5000000000000 : ℝ)*(f.failure) + (11852725606463/800000000000 : ℝ)*(f.sum) + (388474978768627/68285000000000000000000000000 : ℝ)*base65 + (41813839717072354803/6828500000000000000000000000000000 : ℝ)*base67 + (80621880801230854803/6828500000000000000000000000000000 : ℝ)*base69 + (14759331000042854803/6828500000000000000000000000000000 : ℝ)*base71 + (117522937313181/34142500000000000000000000000 : ℝ)*base73 + (54391491949553354803/6828500000000000000000000000000000 : ℝ)*base75 + (63873170389493354803/6828500000000000000000000000000000 : ℝ)*base77 + (41743093377418854803/6828500000000000000000000000000000 : ℝ)*base79 + (521166599584157/68285000000000000000000000000 : ℝ)*base81 + (964557/500000000000000000000 : ℝ)*base89 + (964557/500000000000000000000 : ℝ)*base91 + (964557/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1153_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20387/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1153_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1153_s2_0 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072424923/5000000000 : ℝ)*x 0 + (344294909/625000000 : ℝ)*x 1 + (1290233477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072424923/5000000000 : ℝ)^4173 ≤ (520042443911/4000000000000 : ℝ)^3149 := by
    have hnat : (1072424923 : ℕ)^4173*4000000000000^3149 ≤ 520042443911^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072424923 5000000000 520042443911 4000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344294909/625000000 : ℝ)^4173 ≤ (9075587230593/20000000000000 : ℝ)^3149 := by
    have hnat : (344294909 : ℕ)^4173*20000000000000^3149 ≤ 9075587230593^3149*625000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344294909 625000000 9075587230593 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290233477/2500000000 : ℝ)^4173 ≤ (832420054559/2000000000000 : ℝ)^3149 := by
    have hnat : (1290233477 : ℕ)^4173*2000000000000^3149 ≤ 832420054559^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290233477 2500000000 832420054559 2000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072424923/5000000000 : ℝ), (344294909/625000000 : ℝ), (1290233477/2500000000 : ℝ)] ![(520042443911/4000000000000 : ℝ), (9075587230593/20000000000000 : ℝ), (832420054559/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072424923/5000000000 : ℝ)|^4173 ≤ (520042443911/4000000000000 : ℝ)^3149
        have hw : |(-1072424923/5000000000 : ℝ)|=(1072424923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344294909/625000000 : ℝ)|^4173 ≤ (9075587230593/20000000000000 : ℝ)^3149
        have hw : |(344294909/625000000 : ℝ)|=(344294909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1290233477/2500000000 : ℝ)|^4173 ≤ (832420054559/2000000000000 : ℝ)^3149
        have hw : |(1290233477/2500000000 : ℝ)|=(1290233477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_1 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074678007/2000000000 : ℝ)*x 0 + (-116279279/500000000 : ℝ)*x 1 + (5160936249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074678007/2000000000 : ℝ)^4173 ≤ (43906602070863/100000000000000 : ℝ)^3149 := by
    have hnat : (1074678007 : ℕ)^4173*100000000000000^3149 ≤ 43906602070863^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074678007 2000000000 43906602070863 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116279279/500000000 : ℝ)^4173 ≤ (2894474032967/20000000000000 : ℝ)^3149 := by
    have hnat : (116279279 : ℕ)^4173*20000000000000^3149 ≤ 2894474032967^3149*500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116279279 500000000 2894474032967 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5160936249/10000000000 : ℝ)^4173 ≤ (20810513873229/50000000000000 : ℝ)^3149 := by
    have hnat : (5160936249 : ℕ)^4173*50000000000000^3149 ≤ 20810513873229^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160936249 10000000000 20810513873229 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074678007/2000000000 : ℝ), (-116279279/500000000 : ℝ), (5160936249/10000000000 : ℝ)] ![(43906602070863/100000000000000 : ℝ), (2894474032967/20000000000000 : ℝ), (20810513873229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074678007/2000000000 : ℝ)|^4173 ≤ (43906602070863/100000000000000 : ℝ)^3149
        have hw : |(1074678007/2000000000 : ℝ)|=(1074678007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116279279/500000000 : ℝ)|^4173 ≤ (2894474032967/20000000000000 : ℝ)^3149
        have hw : |(-116279279/500000000 : ℝ)|=(116279279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5160936249/10000000000 : ℝ)|^4173 ≤ (20810513873229/50000000000000 : ℝ)^3149
        have hw : |(5160936249/10000000000 : ℝ)|=(5160936249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_2 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373390191/10000000000 : ℝ)*x 0 + (1032187171/2000000000 : ℝ)*x 1 + (-1162792943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373390191/10000000000 : ℝ)^4173 ≤ (21953301880033/50000000000000 : ℝ)^3149 := by
    have hnat : (5373390191 : ℕ)^4173*50000000000000^3149 ≤ 21953301880033^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373390191 10000000000 21953301880033 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032187171/2000000000 : ℝ)^4173 ≤ (2081051176787/5000000000000 : ℝ)^3149 := by
    have hnat : (1032187171 : ℕ)^4173*5000000000000^3149 ≤ 2081051176787^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032187171 2000000000 2081051176787 5000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162792943/5000000000 : ℝ)^4173 ≤ (7236186344171/50000000000000 : ℝ)^3149 := by
    have hnat : (1162792943 : ℕ)^4173*50000000000000^3149 ≤ 7236186344171^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162792943 5000000000 7236186344171 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373390191/10000000000 : ℝ), (1032187171/2000000000 : ℝ), (-1162792943/5000000000 : ℝ)] ![(21953301880033/50000000000000 : ℝ), (2081051176787/5000000000000 : ℝ), (7236186344171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373390191/10000000000 : ℝ)|^4173 ≤ (21953301880033/50000000000000 : ℝ)^3149
        have hw : |(5373390191/10000000000 : ℝ)|=(5373390191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032187171/2000000000 : ℝ)|^4173 ≤ (2081051176787/5000000000000 : ℝ)^3149
        have hw : |(1032187171/2000000000 : ℝ)|=(1032187171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1162792943/5000000000 : ℝ)|^4173 ≤ (7236186344171/50000000000000 : ℝ)^3149
        have hw : |(-1162792943/5000000000 : ℝ)|=(1162792943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_3 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544081243/1250000000 : ℝ)*x 0 + (401960051/1000000000 : ℝ)*x 1 + (2356498663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544081243/1250000000 : ℝ)^4173 ≤ (3321106052727/10000000000000 : ℝ)^3149 := by
    have hnat : (544081243 : ℕ)^4173*10000000000000^3149 ≤ 3321106052727^3149*1250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544081243 1250000000 3321106052727 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401960051/1000000000 : ℝ)^4173 ≤ (149430779463/500000000000 : ℝ)^3149 := by
    have hnat : (401960051 : ℕ)^4173*500000000000^3149 ≤ 149430779463^3149*1000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401960051 1000000000 149430779463 500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2356498663/5000000000 : ℝ)^4173 ≤ (9225695890069/25000000000000 : ℝ)^3149 := by
    have hnat : (2356498663 : ℕ)^4173*25000000000000^3149 ≤ 9225695890069^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356498663 5000000000 9225695890069 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544081243/1250000000 : ℝ), (401960051/1000000000 : ℝ), (2356498663/5000000000 : ℝ)] ![(3321106052727/10000000000000 : ℝ), (149430779463/500000000000 : ℝ), (9225695890069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544081243/1250000000 : ℝ)|^4173 ≤ (3321106052727/10000000000000 : ℝ)^3149
        have hw : |(544081243/1250000000 : ℝ)|=(544081243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401960051/1000000000 : ℝ)|^4173 ≤ (149430779463/500000000000 : ℝ)^3149
        have hw : |(401960051/1000000000 : ℝ)|=(401960051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2356498663/5000000000 : ℝ)|^4173 ≤ (9225695890069/25000000000000 : ℝ)^3149
        have hw : |(2356498663/5000000000 : ℝ)|=(2356498663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_4 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144949501/10000000000 : ℝ)*x 0 + (2581656879/5000000000 : ℝ)*x 1 + (1376578739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144949501/10000000000 : ℝ)^4173 ≤ (13001861595319/100000000000000 : ℝ)^3149 := by
    have hnat : (2144949501 : ℕ)^4173*100000000000000^3149 ≤ 13001861595319^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144949501 10000000000 13001861595319 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2581656879/5000000000 : ℝ)^4173 ≤ (10411609583751/25000000000000 : ℝ)^3149 := by
    have hnat : (2581656879 : ℕ)^4173*25000000000000^3149 ≤ 10411609583751^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581656879 5000000000 10411609583751 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376578739/2500000000 : ℝ)^4173 ≤ (453517000641/1000000000000 : ℝ)^3149 := by
    have hnat : (1376578739 : ℕ)^4173*1000000000000^3149 ≤ 453517000641^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376578739 2500000000 453517000641 1000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144949501/10000000000 : ℝ), (2581656879/5000000000 : ℝ), (1376578739/2500000000 : ℝ)] ![(13001861595319/100000000000000 : ℝ), (10411609583751/25000000000000 : ℝ), (453517000641/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144949501/10000000000 : ℝ)|^4173 ≤ (13001861595319/100000000000000 : ℝ)^3149
        have hw : |(-2144949501/10000000000 : ℝ)|=(2144949501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2581656879/5000000000 : ℝ)|^4173 ≤ (10411609583751/25000000000000 : ℝ)^3149
        have hw : |(2581656879/5000000000 : ℝ)|=(2581656879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376578739/2500000000 : ℝ)|^4173 ≤ (453517000641/1000000000000 : ℝ)^3149
        have hw : |(1376578739/2500000000 : ℝ)|=(1376578739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_5 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057016699/2000000000 : ℝ)*x 0 + (-990102259/5000000000 : ℝ)*x 1 + (5506315743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057016699/2000000000 : ℝ)^4173 ≤ (42952963689067/100000000000000 : ℝ)^3149 := by
    have hnat : (1057016699 : ℕ)^4173*100000000000000^3149 ≤ 42952963689067^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057016699 2000000000 42952963689067 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990102259/5000000000 : ℝ)^4173 ≤ (5847663824729/50000000000000 : ℝ)^3149 := by
    have hnat : (990102259 : ℕ)^4173*50000000000000^3149 ≤ 5847663824729^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990102259 5000000000 5847663824729 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506315743/10000000000 : ℝ)^4173 ≤ (45351708653899/100000000000000 : ℝ)^3149 := by
    have hnat : (5506315743 : ℕ)^4173*100000000000000^3149 ≤ 45351708653899^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506315743 10000000000 45351708653899 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057016699/2000000000 : ℝ), (-990102259/5000000000 : ℝ), (5506315743/10000000000 : ℝ)] ![(42952963689067/100000000000000 : ℝ), (5847663824729/50000000000000 : ℝ), (45351708653899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057016699/2000000000 : ℝ)|^4173 ≤ (42952963689067/100000000000000 : ℝ)^3149
        have hw : |(1057016699/2000000000 : ℝ)|=(1057016699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990102259/5000000000 : ℝ)|^4173 ≤ (5847663824729/50000000000000 : ℝ)^3149
        have hw : |(-990102259/5000000000 : ℝ)|=(990102259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506315743/10000000000 : ℝ)|^4173 ≤ (45351708653899/100000000000000 : ℝ)^3149
        have hw : |(5506315743/10000000000 : ℝ)|=(5506315743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_6 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285081791/10000000000 : ℝ)*x 0 + (5506315453/10000000000 : ℝ)*x 1 + (-396041453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285081791/10000000000 : ℝ)^4173 ≤ (42952945336933/100000000000000 : ℝ)^3149 := by
    have hnat : (5285081791 : ℕ)^4173*100000000000000^3149 ≤ 42952945336933^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285081791 10000000000 42952945336933 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506315453/10000000000 : ℝ)^4173 ≤ (22675852744331/50000000000000 : ℝ)^3149 := by
    have hnat : (5506315453 : ℕ)^4173*50000000000000^3149 ≤ 22675852744331^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506315453 10000000000 22675852744331 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396041453/2000000000 : ℝ)^4173 ≤ (11695349149377/100000000000000 : ℝ)^3149 := by
    have hnat : (396041453 : ℕ)^4173*100000000000000^3149 ≤ 11695349149377^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396041453 2000000000 11695349149377 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285081791/10000000000 : ℝ), (5506315453/10000000000 : ℝ), (-396041453/2000000000 : ℝ)] ![(42952945336933/100000000000000 : ℝ), (22675852744331/50000000000000 : ℝ), (11695349149377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285081791/10000000000 : ℝ)|^4173 ≤ (42952945336933/100000000000000 : ℝ)^3149
        have hw : |(5285081791/10000000000 : ℝ)|=(5285081791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506315453/10000000000 : ℝ)|^4173 ≤ (22675852744331/50000000000000 : ℝ)^3149
        have hw : |(5506315453/10000000000 : ℝ)|=(5506315453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396041453/2000000000 : ℝ)|^4173 ≤ (11695349149377/100000000000000 : ℝ)^3149
        have hw : |(-396041453/2000000000 : ℝ)|=(396041453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s2_7 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4352847359/10000000000 : ℝ)*x 0 + (2354127227/5000000000 : ℝ)*x 1 + (80487819/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352847359/10000000000 : ℝ)^4173 ≤ (33213056653851/100000000000000 : ℝ)^3149 := by
    have hnat : (4352847359 : ℕ)^4173*100000000000000^3149 ≤ 33213056653851^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352847359 10000000000 33213056653851 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2354127227/5000000000 : ℝ)^4173 ≤ (36853578702723/100000000000000 : ℝ)^3149 := by
    have hnat : (2354127227 : ℕ)^4173*100000000000000^3149 ≤ 36853578702723^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354127227 5000000000 36853578702723 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80487819/200000000 : ℝ)^4173 ≤ (7483341158363/25000000000000 : ℝ)^3149 := by
    have hnat : (80487819 : ℕ)^4173*25000000000000^3149 ≤ 7483341158363^3149*200000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80487819 200000000 7483341158363 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352847359/10000000000 : ℝ), (2354127227/5000000000 : ℝ), (80487819/200000000 : ℝ)] ![(33213056653851/100000000000000 : ℝ), (36853578702723/100000000000000 : ℝ), (7483341158363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352847359/10000000000 : ℝ)|^4173 ≤ (33213056653851/100000000000000 : ℝ)^3149
        have hw : |(4352847359/10000000000 : ℝ)|=(4352847359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2354127227/5000000000 : ℝ)|^4173 ≤ (36853578702723/100000000000000 : ℝ)^3149
        have hw : |(2354127227/5000000000 : ℝ)|=(2354127227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80487819/200000000 : ℝ)|^4173 ≤ (7483341158363/25000000000000 : ℝ)^3149
        have hw : |(80487819/200000000 : ℝ)|=(80487819/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1153_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1647/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5711/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (107368357686617/12500000000000000000 : ℝ) := by
    have hpowers : (5711/100000 : ℝ)^8345 ≤ (107368357686617/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5711 : ℕ)^8345*12500000000000000000^2048 ≤ 107368357686617^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5711 100000 107368357686617 12500000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5711/100000 : ℝ)) (X := (107368357686617/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20387/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (15339709276382139/10000000000000000000 : ℝ) := by
    have hpowers : (20387/100000 : ℝ)^8345 ≤ (15339709276382139/10000000000000000000 : ℝ)^2048 := by
      have hnat : (20387 : ℕ)^8345*10000000000000000000^2048 ≤ 15339709276382139^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20387 100000 15339709276382139 10000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20387/100000 : ℝ)) (X := (15339709276382139/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250107368357686617/6250000000000000000 : ℝ) ≤ (312501317489343/312500000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (6250107368357686617/6250000000000000000 : ℝ)^2048 ≤ (312501317489343/312500000000000 : ℝ)^8345 := by
      have hnat : (6250107368357686617 : ℕ)^2048*312500000000000^8345 ≤ 312501317489343^8345*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250107368357686617 6250000000000000000 312501317489343 312500000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501317489343/312500000000000 : ℝ)) (X := (6250107368357686617/6250000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50077128019812657163/50000000000000000000 : ℝ) ≤ (50018917475913/50000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (50077128019812657163/50000000000000000000 : ℝ)^2048 ≤ (50018917475913/50000000000000 : ℝ)^8345 := by
      have hnat : (50077128019812657163 : ℕ)^2048*50000000000000^8345 ≤ 50018917475913^8345*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077128019812657163 50000000000000000000 50018917475913 50000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50018917475913/50000000000000 : ℝ)) (X := (50077128019812657163/50000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5015339709276382139/5000000000000000000 : ℝ) ≤ (625470301919139/625000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (5015339709276382139/5000000000000000000 : ℝ)^2048 ≤ (625470301919139/625000000000000 : ℝ)^8345 := by
      have hnat : (5015339709276382139 : ℕ)^2048*625000000000000^8345 ≤ 625470301919139^8345*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5015339709276382139 5000000000000000000 625470301919139 625000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625470301919139/625000000000000 : ℝ)) (X := (5015339709276382139/5000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(107368357686617/12500000000000000000 : ℝ) ≤ ((3056622608350089551/3057500000000000000 : ℝ)+2*(155888980151/61150000000000 : ℝ)*(5711/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (3056622608350089551/3057500000000000000 : ℝ)+2*(155888980151/61150000000000 : ℝ)*(5711/100000 : ℝ)=(312501317489343/312500000000000 : ℝ) by norm_num, show 1+2*(107368357686617/12500000000000000000 : ℝ)=(6250107368357686617/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15339709276382139/10000000000000000000 : ℝ)+(107368357686617/12500000000000000000 : ℝ) ≤ ((3056622608350089551/3057500000000000000 : ℝ)+(155888980151/61150000000000 : ℝ)*((20387/100000 : ℝ)+(5711/100000 : ℝ)))^(8345/2048 : ℝ) := by
    rw [show (3056622608350089551/3057500000000000000 : ℝ)+(155888980151/61150000000000 : ℝ)*((20387/100000 : ℝ)+(5711/100000 : ℝ))=(50018917475913/50000000000000 : ℝ) by norm_num, show 1+(15339709276382139/10000000000000000000 : ℝ)+(107368357686617/12500000000000000000 : ℝ)=(50077128019812657163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15339709276382139/10000000000000000000 : ℝ) ≤ ((3056622608350089551/3057500000000000000 : ℝ)+2*(155888980151/61150000000000 : ℝ)*(20387/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (3056622608350089551/3057500000000000000 : ℝ)+2*(155888980151/61150000000000 : ℝ)*(20387/100000 : ℝ)=(625470301919139/625000000000000 : ℝ) by norm_num, show 1+2*(15339709276382139/10000000000000000000 : ℝ)=(5015339709276382139/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3056622608350089551/3057500000000000000 : ℝ)*(X 1 0+X 2 0)+(155888980151/61150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (5711/100000 : ℝ)) (hi := (20387/100000 : ℝ)) (c := (3056622608350089551/3057500000000000000 : ℝ)) (alpha := (155888980151/61150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3056622608350089551/3057500000000000000 : ℝ)*(X 0 1+X 2 1)+(155888980151/61150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (5711/100000 : ℝ)) (hi := (20387/100000 : ℝ)) (c := (3056622608350089551/3057500000000000000 : ℝ)) (alpha := (155888980151/61150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3056622608350089551/3057500000000000000 : ℝ)*(X 0 2+X 1 2)+(155888980151/61150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (5711/100000 : ℝ)) (hi := (20387/100000 : ℝ)) (c := (3056622608350089551/3057500000000000000 : ℝ)) (alpha := (155888980151/61150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1072424923/5000000000 : ℝ)*X 0 0+(344294909/625000000 : ℝ)*X 0 1+(1290233477/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074678007/2000000000 : ℝ)*X 1 0+(-116279279/500000000 : ℝ)*X 1 1+(5160936249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373390191/10000000000 : ℝ)*X 2 0+(1032187171/2000000000 : ℝ)*X 2 1+(-1162792943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544081243/1250000000 : ℝ)*X 0 0+(401960051/1000000000 : ℝ)*X 0 1+(2356498663/5000000000 : ℝ)*X 0 2+(544081243/1250000000 : ℝ)*X 1 0+(401960051/1000000000 : ℝ)*X 1 1+(2356498663/5000000000 : ℝ)*X 1 2+(544081243/1250000000 : ℝ)*X 2 0+(401960051/1000000000 : ℝ)*X 2 1+(2356498663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144949501/10000000000 : ℝ)*X 0 0+(2581656879/5000000000 : ℝ)*X 0 1+(1376578739/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057016699/2000000000 : ℝ)*X 1 0+(-990102259/5000000000 : ℝ)*X 1 1+(5506315743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285081791/10000000000 : ℝ)*X 2 0+(5506315453/10000000000 : ℝ)*X 2 1+(-396041453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352847359/10000000000 : ℝ)*X 0 0+(2354127227/5000000000 : ℝ)*X 0 1+(80487819/200000000 : ℝ)*X 0 2+(4352847359/10000000000 : ℝ)*X 1 0+(2354127227/5000000000 : ℝ)*X 1 1+(80487819/200000000 : ℝ)*X 1 2+(4352847359/10000000000 : ℝ)*X 2 0+(2354127227/5000000000 : ℝ)*X 2 1+(80487819/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (490870919706750035798143953/76437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84152703/25000000000000 : ℝ)*(base19) + (151791391/50000000000000 : ℝ)*(base23) + (77229269/100000000000000 : ℝ)*(upper2) + (1665691/625000000000 : ℝ)*(upper3) + (139832431/100000000000000 : ℝ)*(upper4) + (1079390883179899/50000000000000 : ℝ)*(major0) + (1079390883179899/50000000000000 : ℝ)*(major1) + (1079390883179899/50000000000000 : ℝ)*(major2) + (575072573463809/20000000000000 : ℝ)*(sp0) + (1437689509927291/50000000000000 : ℝ)*(sp1) + (2875379052882611/100000000000000 : ℝ)*(sp2) + (721089267048389/50000000000000 : ℝ)*(sp3) + (4122286587/25000000000000 : ℝ)*(sp4) + (2714047711/50000000000000 : ℝ)*(sp7) + (7210919810961/500000000000 : ℝ)*(f.failure) + (2875379356465393/100000000000000 : ℝ)*(f.sum) + (2133125926721/1528750000000000000000000000 : ℝ)*base66 + (291270534413585349/152875000000000000000000000000000 : ℝ)*base67 + (1626096694537085349/152875000000000000000000000000000 : ℝ)*base69 + (119774975706914651/152875000000000000000000000000000 : ℝ)*base72 + (2047611982019/1528750000000000000000000000 : ℝ)*base73 + (39122428526664651/152875000000000000000000000000000 : ℝ)*base76 + (773935586941460349/152875000000000000000000000000000 : ℝ)*base77 + (726017813733210349/152875000000000000000000000000000 : ℝ)*base79 + (4689970778033/3057500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (99703/50000000000000000000 : ℝ)*base90 + (99703/50000000000000000000 : ℝ)*base92 + (99703/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153384409477257527251220109/15287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217794723/12500000000000 : ℝ)*(base19) + (290543393/25000000000000 : ℝ)*(base23) + (381123519/100000000000000 : ℝ)*(upper2) + (114960779/100000000000000 : ℝ)*(upper3) + (12389969/4000000000000 : ℝ)*(upper5) + (218885540448053/10000000000000 : ℝ)*(major0) + (218885540448053/10000000000000 : ℝ)*(major1) + (218885540448053/10000000000000 : ℝ)*(major2) + (1039372167/4000000000000 : ℝ)*(sp1) + (871779403/20000000000000 : ℝ)*(sp2) + (1457717840905893/50000000000000 : ℝ)*(sp4) + (728851988787457/25000000000000 : ℝ)*(sp5) + (2915430160741199/100000000000000 : ℝ)*(sp6) + (731137396352601/50000000000000 : ℝ)*(sp7) + (731137396352601/50000000000000 : ℝ)*(f.failure) + (1457717840905893/50000000000000 : ℝ)*(f.sum) + (387339209653/152875000000000000000000000 : ℝ)*base66 + (276510492226455797/30575000000000000000000000000000 : ℝ)*base68 + (39791801877044203/30575000000000000000000000000000 : ℝ)*base69 + (180102166815480797/30575000000000000000000000000000 : ℝ)*base72 + (259166321889/61150000000000000000000000 : ℝ)*base74 + (364128724971680797/30575000000000000000000000000000 : ℝ)*base76 + (85600628198344203/30575000000000000000000000000000 : ℝ)*base77 + (152164082527255797/30575000000000000000000000000000 : ℝ)*base80 + (1210326026113/1223000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (63418577/5000000000000000000000 : ℝ)*base89 + (63418577/5000000000000000000000 : ℝ)*base91 + (63418577/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1153_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1647/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1153_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1153_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1647/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1153_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1153_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1153_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1647/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1153_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
