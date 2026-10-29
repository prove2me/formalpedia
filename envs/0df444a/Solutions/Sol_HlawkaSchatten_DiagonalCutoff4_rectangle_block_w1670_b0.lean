-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1670_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:39.315704+00:00
-- url     : https://prove2.me/submissions/9252d52c-08bb-4fd2-98e8-0d2d91772a7c

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
theorem support_rectangle_w1670_s0_0 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-364549759/2500000000 : ℝ)*x 0 + (1152212717/2000000000 : ℝ)*x 1 + (4934810873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364549759/2500000000 : ℝ)^4999 ≤ (4439945161817/50000000000000 : ℝ)^3975 := by
    have hnat : (364549759 : ℕ)^4999*50000000000000^3975 ≤ 4439945161817^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364549759 2500000000 4439945161817 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152212717/2000000000 : ℝ)^4999 ≤ (49981092631373/100000000000000 : ℝ)^3975 := by
    have hnat : (1152212717 : ℕ)^4999*100000000000000^3975 ≤ 49981092631373^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152212717 2000000000 49981092631373 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4934810873/10000000000 : ℝ)^4999 ≤ (5142377128713/12500000000000 : ℝ)^3975 := by
    have hnat : (4934810873 : ℕ)^4999*12500000000000^3975 ≤ 5142377128713^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934810873 10000000000 5142377128713 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364549759/2500000000 : ℝ), (1152212717/2000000000 : ℝ), (4934810873/10000000000 : ℝ)] ![(4439945161817/50000000000000 : ℝ), (49981092631373/100000000000000 : ℝ), (5142377128713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364549759/2500000000 : ℝ)|^4999 ≤ (4439945161817/50000000000000 : ℝ)^3975
        have hw : |(-364549759/2500000000 : ℝ)|=(364549759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1152212717/2000000000 : ℝ)|^4999 ≤ (49981092631373/100000000000000 : ℝ)^3975
        have hw : |(1152212717/2000000000 : ℝ)|=(1152212717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4934810873/10000000000 : ℝ)|^4999 ≤ (5142377128713/12500000000000 : ℝ)^3975
        have hw : |(4934810873/10000000000 : ℝ)|=(4934810873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_1 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085937931/2000000000 : ℝ)*x 0 + (-381988273/2000000000 : ℝ)*x 1 + (4934811877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085937931/2000000000 : ℝ)^4999 ≤ (9278555630069/20000000000000 : ℝ)^3975 := by
    have hnat : (1085937931 : ℕ)^4999*20000000000000^3975 ≤ 9278555630069^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085937931 2000000000 9278555630069 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381988273/2000000000 : ℝ)^4999 ≤ (6234097135859/50000000000000 : ℝ)^3975 := by
    have hnat : (381988273 : ℕ)^4999*50000000000000^3975 ≤ 6234097135859^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381988273 2000000000 6234097135859 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4934811877/10000000000 : ℝ)^4999 ≤ (20569513777849/50000000000000 : ℝ)^3975 := by
    have hnat : (4934811877 : ℕ)^4999*50000000000000^3975 ≤ 20569513777849^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934811877 10000000000 20569513777849 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085937931/2000000000 : ℝ), (-381988273/2000000000 : ℝ), (4934811877/10000000000 : ℝ)] ![(9278555630069/20000000000000 : ℝ), (6234097135859/50000000000000 : ℝ), (20569513777849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085937931/2000000000 : ℝ)|^4999 ≤ (9278555630069/20000000000000 : ℝ)^3975
        have hw : |(1085937931/2000000000 : ℝ)|=(1085937931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381988273/2000000000 : ℝ)|^4999 ≤ (6234097135859/50000000000000 : ℝ)^3975
        have hw : |(-381988273/2000000000 : ℝ)|=(381988273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4934811877/10000000000 : ℝ)|^4999 ≤ (20569513777849/50000000000000 : ℝ)^3975
        have hw : |(4934811877/10000000000 : ℝ)|=(4934811877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_2 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2714845981/5000000000 : ℝ)*x 0 + (61685131/125000000 : ℝ)*x 1 + (-1909940129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2714845981/5000000000 : ℝ)^4999 ≤ (9278560587983/20000000000000 : ℝ)^3975 := by
    have hnat : (2714845981 : ℕ)^4999*20000000000000^3975 ≤ 9278560587983^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714845981 5000000000 9278560587983 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61685131/125000000 : ℝ)^4999 ≤ (4113901290947/10000000000000 : ℝ)^3975 := by
    have hnat : (61685131 : ℕ)^4999*10000000000000^3975 ≤ 4113901290947^3975*125000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61685131 125000000 4113901290947 10000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1909940129/10000000000 : ℝ)^4999 ≤ (12468184124477/100000000000000 : ℝ)^3975 := by
    have hnat : (1909940129 : ℕ)^4999*100000000000000^3975 ≤ 12468184124477^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909940129 10000000000 12468184124477 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2714845981/5000000000 : ℝ), (61685131/125000000 : ℝ), (-1909940129/10000000000 : ℝ)] ![(9278560587983/20000000000000 : ℝ), (4113901290947/10000000000000 : ℝ), (12468184124477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2714845981/5000000000 : ℝ)|^4999 ≤ (9278560587983/20000000000000 : ℝ)^3975
        have hw : |(2714845981/5000000000 : ℝ)|=(2714845981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61685131/125000000 : ℝ)|^4999 ≤ (4113901290947/10000000000000 : ℝ)^3975
        have hw : |(61685131/125000000 : ℝ)|=(61685131/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1909940129/10000000000 : ℝ)|^4999 ≤ (12468184124477/100000000000000 : ℝ)^3975
        have hw : |(-1909940129/10000000000 : ℝ)|=(1909940129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_3 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4081352257/10000000000 : ℝ)*x 0 + (385993131/1250000000 : ℝ)*x 1 + (1319905589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4081352257/10000000000 : ℝ)^4999 ≤ (32399871994957/100000000000000 : ℝ)^3975 := by
    have hnat : (4081352257 : ℕ)^4999*100000000000000^3975 ≤ 32399871994957^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081352257 10000000000 32399871994957 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385993131/1250000000 : ℝ)^4999 ≤ (11407049117839/50000000000000 : ℝ)^3975 := by
    have hnat : (385993131 : ℕ)^4999*50000000000000^3975 ≤ 11407049117839^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385993131 1250000000 11407049117839 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319905589/2500000000 : ℝ)^4999 ≤ (11196507438041/25000000000000 : ℝ)^3975 := by
    have hnat : (1319905589 : ℕ)^4999*25000000000000^3975 ≤ 11196507438041^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319905589 2500000000 11196507438041 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4081352257/10000000000 : ℝ), (385993131/1250000000 : ℝ), (1319905589/2500000000 : ℝ)] ![(32399871994957/100000000000000 : ℝ), (11407049117839/50000000000000 : ℝ), (11196507438041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4081352257/10000000000 : ℝ)|^4999 ≤ (32399871994957/100000000000000 : ℝ)^3975
        have hw : |(4081352257/10000000000 : ℝ)|=(4081352257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(385993131/1250000000 : ℝ)|^4999 ≤ (11407049117839/50000000000000 : ℝ)^3975
        have hw : |(385993131/1250000000 : ℝ)|=(385993131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1319905589/2500000000 : ℝ)|^4999 ≤ (11196507438041/25000000000000 : ℝ)^3975
        have hw : |(1319905589/2500000000 : ℝ)|=(1319905589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_4 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-730140221/5000000000 : ℝ)*x 0 + (619385331/1250000000 : ℝ)*x 1 + (1435025741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730140221/5000000000 : ℝ)^4999 ≤ (4447916723601/50000000000000 : ℝ)^3975 := by
    have hnat : (730140221 : ℕ)^4999*50000000000000^3975 ≤ 4447916723601^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730140221 5000000000 4447916723601 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619385331/1250000000 : ℝ)^4999 ≤ (8270331965581/20000000000000 : ℝ)^3975 := by
    have hnat : (619385331 : ℕ)^4999*20000000000000^3975 ≤ 8270331965581^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619385331 1250000000 8270331965581 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435025741/2500000000 : ℝ)^4999 ≤ (24876253357339/50000000000000 : ℝ)^3975 := by
    have hnat : (1435025741 : ℕ)^4999*50000000000000^3975 ≤ 24876253357339^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435025741 2500000000 24876253357339 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-730140221/5000000000 : ℝ), (619385331/1250000000 : ℝ), (1435025741/2500000000 : ℝ)] ![(4447916723601/50000000000000 : ℝ), (8270331965581/20000000000000 : ℝ), (24876253357339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-730140221/5000000000 : ℝ)|^4999 ≤ (4447916723601/50000000000000 : ℝ)^3975
        have hw : |(-730140221/5000000000 : ℝ)|=(730140221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(619385331/1250000000 : ℝ)|^4999 ≤ (8270331965581/20000000000000 : ℝ)^3975
        have hw : |(619385331/1250000000 : ℝ)|=(619385331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1435025741/2500000000 : ℝ)|^4999 ≤ (24876253357339/50000000000000 : ℝ)^3975
        have hw : |(1435025741/2500000000 : ℝ)|=(1435025741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_5 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602196249/5000000000 : ℝ)*x 0 + (-138081139/1250000000 : ℝ)*x 1 + (229604191/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602196249/5000000000 : ℝ)^4999 ≤ (4398495083821/10000000000000 : ℝ)^3975 := by
    have hnat : (2602196249 : ℕ)^4999*10000000000000^3975 ≤ 4398495083821^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602196249 5000000000 4398495083821 10000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138081139/1250000000 : ℝ)^4999 ≤ (1252504536391/20000000000000 : ℝ)^3975 := by
    have hnat : (138081139 : ℕ)^4999*20000000000000^3975 ≤ 1252504536391^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138081139 1250000000 1252504536391 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229604191/400000000 : ℝ)^4999 ≤ (49752526455251/100000000000000 : ℝ)^3975 := by
    have hnat : (229604191 : ℕ)^4999*100000000000000^3975 ≤ 49752526455251^3975*400000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229604191 400000000 49752526455251 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602196249/5000000000 : ℝ), (-138081139/1250000000 : ℝ), (229604191/400000000 : ℝ)] ![(4398495083821/10000000000000 : ℝ), (1252504536391/20000000000000 : ℝ), (49752526455251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602196249/5000000000 : ℝ)|^4999 ≤ (4398495083821/10000000000000 : ℝ)^3975
        have hw : |(2602196249/5000000000 : ℝ)|=(2602196249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138081139/1250000000 : ℝ)|^4999 ≤ (1252504536391/20000000000000 : ℝ)^3975
        have hw : |(-138081139/1250000000 : ℝ)|=(138081139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229604191/400000000 : ℝ)|^4999 ≤ (49752526455251/100000000000000 : ℝ)^3975
        have hw : |(229604191/400000000 : ℝ)|=(229604191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_6 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204392847/10000000000 : ℝ)*x 0 + (5740104253/10000000000 : ℝ)*x 1 + (-1104649391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204392847/10000000000 : ℝ)^4999 ≤ (351879636381/800000000000 : ℝ)^3975 := by
    have hnat : (5204392847 : ℕ)^4999*800000000000^3975 ≤ 351879636381^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204392847 10000000000 351879636381 800000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5740104253/10000000000 : ℝ)^4999 ≤ (49752520765257/100000000000000 : ℝ)^3975 := by
    have hnat : (5740104253 : ℕ)^4999*100000000000000^3975 ≤ 49752520765257^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5740104253 10000000000 49752520765257 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104649391/10000000000 : ℝ)^4999 ≤ (313126233557/5000000000000 : ℝ)^3975 := by
    have hnat : (1104649391 : ℕ)^4999*5000000000000^3975 ≤ 313126233557^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104649391 10000000000 313126233557 5000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204392847/10000000000 : ℝ), (5740104253/10000000000 : ℝ), (-1104649391/10000000000 : ℝ)] ![(351879636381/800000000000 : ℝ), (49752520765257/100000000000000 : ℝ), (313126233557/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204392847/10000000000 : ℝ)|^4999 ≤ (351879636381/800000000000 : ℝ)^3975
        have hw : |(5204392847/10000000000 : ℝ)|=(5204392847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5740104253/10000000000 : ℝ)|^4999 ≤ (49752520765257/100000000000000 : ℝ)^3975
        have hw : |(5740104253/10000000000 : ℝ)|=(5740104253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1104649391/10000000000 : ℝ)|^4999 ≤ (313126233557/5000000000000 : ℝ)^3975
        have hw : |(-1104649391/10000000000 : ℝ)|=(1104649391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s0_7 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4086872861/10000000000 : ℝ)*x 0 + (1045170021/2000000000 : ℝ)*x 1 + (3143542229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4086872861/10000000000 : ℝ)^4999 ≤ (6490999369683/20000000000000 : ℝ)^3975 := by
    have hnat : (4086872861 : ℕ)^4999*20000000000000^3975 ≤ 6490999369683^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4086872861 10000000000 6490999369683 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045170021/2000000000 : ℝ)^4999 ≤ (5526642282407/12500000000000 : ℝ)^3975 := by
    have hnat : (1045170021 : ℕ)^4999*12500000000000^3975 ≤ 5526642282407^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045170021 2000000000 5526642282407 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3143542229/10000000000 : ℝ)^4999 ≤ (23331864888063/100000000000000 : ℝ)^3975 := by
    have hnat : (3143542229 : ℕ)^4999*100000000000000^3975 ≤ 23331864888063^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3143542229 10000000000 23331864888063 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4086872861/10000000000 : ℝ), (1045170021/2000000000 : ℝ), (3143542229/10000000000 : ℝ)] ![(6490999369683/20000000000000 : ℝ), (5526642282407/12500000000000 : ℝ), (23331864888063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4086872861/10000000000 : ℝ)|^4999 ≤ (6490999369683/20000000000000 : ℝ)^3975
        have hw : |(4086872861/10000000000 : ℝ)|=(4086872861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045170021/2000000000 : ℝ)|^4999 ≤ (5526642282407/12500000000000 : ℝ)^3975
        have hw : |(1045170021/2000000000 : ℝ)|=(1045170021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3143542229/10000000000 : ℝ)|^4999 ≤ (23331864888063/100000000000000 : ℝ)^3975
        have hw : |(3143542229/10000000000 : ℝ)|=(3143542229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1670_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (261/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1147/5000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4995/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4995 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4995*1^1024 ≤ 0^1024*1^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4995/1024 : ℝ) ≤ (71574221866326603/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4995 ≤ (71574221866326603/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4995*6250000000000000000^1024 ≤ 71574221866326603^1024*5^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 71574221866326603 6250000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (71574221866326603/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4995 := by
      have hnat : (1 : ℕ)^1024*1^4995 ≤ 1^4995*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6321574221866326603/6250000000000000000 : ℝ) ≤ (2004674155062437/2000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (6321574221866326603/6250000000000000000 : ℝ)^1024 ≤ (2004674155062437/2000000000000000 : ℝ)^4995 := by
      have hnat : (6321574221866326603 : ℕ)^1024*2000000000000000^4995 ≤ 2004674155062437^4995*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6321574221866326603 6250000000000000000 2004674155062437 2000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004674155062437/2000000000000000 : ℝ)) (X := (6321574221866326603/6250000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3196574221866326603/3125000000000000000 : ℝ) ≤ (1004674155062437/1000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (3196574221866326603/3125000000000000000 : ℝ)^1024 ≤ (1004674155062437/1000000000000000 : ℝ)^4995 := by
      have hnat : (3196574221866326603 : ℕ)^1024*1000000000000000^4995 ≤ 1004674155062437^4995*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3196574221866326603 3125000000000000000 1004674155062437 1000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004674155062437/1000000000000000 : ℝ)) (X := (3196574221866326603/3125000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4674155062437/800000000000000 : ℝ)*(0 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4674155062437/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71574221866326603/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4674155062437/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4995/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4674155062437/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2004674155062437/2000000000000000 : ℝ) by norm_num, show 1+(71574221866326603/6250000000000000000 : ℝ)+(0 : ℝ)=(6321574221866326603/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71574221866326603/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4674155062437/800000000000000 : ℝ)*(2/5 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4674155062437/800000000000000 : ℝ)*(2/5 : ℝ)=(1004674155062437/1000000000000000 : ℝ) by norm_num, show 1+2*(71574221866326603/6250000000000000000 : ℝ)=(3196574221866326603/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4674155062437/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4674155062437/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4674155062437/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4674155062437/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4674155062437/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4674155062437/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-364549759/2500000000 : ℝ)*X 0 0+(1152212717/2000000000 : ℝ)*X 0 1+(4934810873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1085937931/2000000000 : ℝ)*X 1 0+(-381988273/2000000000 : ℝ)*X 1 1+(4934811877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2714845981/5000000000 : ℝ)*X 2 0+(61685131/125000000 : ℝ)*X 2 1+(-1909940129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4081352257/10000000000 : ℝ)*X 0 0+(385993131/1250000000 : ℝ)*X 0 1+(1319905589/2500000000 : ℝ)*X 0 2+(4081352257/10000000000 : ℝ)*X 1 0+(385993131/1250000000 : ℝ)*X 1 1+(1319905589/2500000000 : ℝ)*X 1 2+(4081352257/10000000000 : ℝ)*X 2 0+(385993131/1250000000 : ℝ)*X 2 1+(1319905589/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-730140221/5000000000 : ℝ)*X 0 0+(619385331/1250000000 : ℝ)*X 0 1+(1435025741/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2602196249/5000000000 : ℝ)*X 1 0+(-138081139/1250000000 : ℝ)*X 1 1+(229604191/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5204392847/10000000000 : ℝ)*X 2 0+(5740104253/10000000000 : ℝ)*X 2 1+(-1104649391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4086872861/10000000000 : ℝ)*X 0 0+(1045170021/2000000000 : ℝ)*X 0 1+(3143542229/10000000000 : ℝ)*X 0 2+(4086872861/10000000000 : ℝ)*X 1 0+(1045170021/2000000000 : ℝ)*X 1 1+(3143542229/10000000000 : ℝ)*X 1 2+(4086872861/10000000000 : ℝ)*X 2 0+(1045170021/2000000000 : ℝ)*X 2 1+(3143542229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268222095902136934124619/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71552889/50000000000000 : ℝ)*(base1) + (1101218301/100000000000000 : ℝ)*(base19) + (762213987/50000000000000 : ℝ)*(base23) + (91027197/100000000000000 : ℝ)*(base24) + (65477817/25000000000000 : ℝ)*(upper5) + (833285714673371/100000000000000 : ℝ)*(major0) + (833285714673371/100000000000000 : ℝ)*(major1) + (833285714673371/100000000000000 : ℝ)*(major2) + (242057497326933/20000000000000 : ℝ)*(sp0) + (605146900413811/50000000000000 : ℝ)*(sp1) + (37821665205961/3125000000000 : ℝ)*(sp2) + (456274041755743/100000000000000 : ℝ)*(sp3) + (1889629259/25000000000000 : ℝ)*(sp4) + (26486511/1250000000000 : ℝ)*(sp7) + (228138151891201/50000000000000 : ℝ)*(f.failure) + (1210294902045923/100000000000000 : ℝ)*(f.sum) + (33305295105127/40000000000000000000000000000 : ℝ)*base65 + (428067907094873/80000000000000000000000000000 : ℝ)*base68 + (71966424105127/80000000000000000000000000000 : ℝ)*base69 + (39458437014873/80000000000000000000000000000 : ℝ)*base72 + (171995195094873/40000000000000000000000000000 : ℝ)*base74 + (141350315494873/80000000000000000000000000000 : ℝ)*base76 + (48038761865127/80000000000000000000000000000 : ℝ)*base77 + (50770844345127/80000000000000000000000000000 : ℝ)*base79 + (187435765465127/40000000000000000000000000000 : ℝ)*base81 + (9897659/1250000000000000000000 : ℝ)*base89 + (9897659/1250000000000000000000 : ℝ)*base91 + (9897659/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124785921027534136591737/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45530797/5000000000000 : ℝ)*(base19) + (1017035713/100000000000000 : ℝ)*(base23) + (14541587/10000000000000 : ℝ)*(base32) + (158074701/50000000000000 : ℝ)*(upper3) + (27762917/25000000000000 : ℝ)*(upper5) + (877043628542967/100000000000000 : ℝ)*(major0) + (877043628542967/100000000000000 : ℝ)*(major1) + (877043628542967/100000000000000 : ℝ)*(major2) + (3755872937/100000000000000 : ℝ)*(sp1) + (1060217527/25000000000000 : ℝ)*(sp2) + (636925268570703/50000000000000 : ℝ)*(sp4) + (79615366915783/6250000000000 : ℝ)*(sp5) + (254769055847117/20000000000000 : ℝ)*(sp6) + (480236366552117/100000000000000 : ℝ)*(sp7) + (480236511967987/100000000000000 : ℝ)*(f.failure) + (636925268570703/50000000000000 : ℝ)*(f.sum) + (11384610830579/40000000000000000000000000000 : ℝ)*base65 + (695474407609421/80000000000000000000000000000 : ℝ)*base68 + (381972871929421/80000000000000000000000000000 : ℝ)*base70 + (87297348950579/80000000000000000000000000000 : ℝ)*base71 + (300499903529421/40000000000000000000000000000 : ℝ)*base74 + (443517802870579/80000000000000000000000000000 : ℝ)*base75 + (463441108009421/80000000000000000000000000000 : ℝ)*base78 + (450006548169421/80000000000000000000000000000 : ℝ)*base80 + (89339022809421/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (19972833/2500000000000000000000 : ℝ)*base89 + (19972833/2500000000000000000000 : ℝ)*base91 + (19972833/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1670_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (261/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1147/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1670_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1670_s1_0 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-155607323/1000000000 : ℝ)*x 0 + (2741024377/5000000000 : ℝ)*x 1 + (5150044679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155607323/1000000000 : ℝ)^4999 ≤ (602238969487/6250000000000 : ℝ)^3975 := by
    have hnat : (155607323 : ℕ)^4999*6250000000000^3975 ≤ 602238969487^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155607323 1000000000 602238969487 6250000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741024377/5000000000 : ℝ)^4999 ≤ (586951165019/1250000000000 : ℝ)^3975 := by
    have hnat : (2741024377 : ℕ)^4999*1250000000000^3975 ≤ 586951165019^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741024377 5000000000 586951165019 1250000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150044679/10000000000 : ℝ)^4999 ≤ (1356502602137/3125000000000 : ℝ)^3975 := by
    have hnat : (5150044679 : ℕ)^4999*3125000000000^3975 ≤ 1356502602137^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150044679 10000000000 1356502602137 3125000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-155607323/1000000000 : ℝ), (2741024377/5000000000 : ℝ), (5150044679/10000000000 : ℝ)] ![(602238969487/6250000000000 : ℝ), (586951165019/1250000000000 : ℝ), (1356502602137/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-155607323/1000000000 : ℝ)|^4999 ≤ (602238969487/6250000000000 : ℝ)^3975
        have hw : |(-155607323/1000000000 : ℝ)|=(155607323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741024377/5000000000 : ℝ)|^4999 ≤ (586951165019/1250000000000 : ℝ)^3975
        have hw : |(2741024377/5000000000 : ℝ)|=(2741024377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150044679/10000000000 : ℝ)|^4999 ≤ (1356502602137/3125000000000 : ℝ)^3975
        have hw : |(5150044679/10000000000 : ℝ)|=(5150044679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_1 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355463311/10000000000 : ℝ)*x 0 + (-1728254657/10000000000 : ℝ)*x 1 + (643755589/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355463311/10000000000 : ℝ)^4999 ≤ (4559659781011/10000000000000 : ℝ)^3975 := by
    have hnat : (5355463311 : ℕ)^4999*10000000000000^3975 ≤ 4559659781011^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355463311 10000000000 4559659781011 10000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1728254657/10000000000 : ℝ)^4999 ≤ (1374414820917/12500000000000 : ℝ)^3975 := by
    have hnat : (1728254657 : ℕ)^4999*12500000000000^3975 ≤ 1374414820917^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728254657 10000000000 1374414820917 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643755589/1250000000 : ℝ)^4999 ≤ (43408083618183/100000000000000 : ℝ)^3975 := by
    have hnat : (643755589 : ℕ)^4999*100000000000000^3975 ≤ 43408083618183^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643755589 1250000000 43408083618183 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355463311/10000000000 : ℝ), (-1728254657/10000000000 : ℝ), (643755589/1250000000 : ℝ)] ![(4559659781011/10000000000000 : ℝ), (1374414820917/12500000000000 : ℝ), (43408083618183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355463311/10000000000 : ℝ)|^4999 ≤ (4559659781011/10000000000000 : ℝ)^3975
        have hw : |(5355463311/10000000000 : ℝ)|=(5355463311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1728254657/10000000000 : ℝ)|^4999 ≤ (1374414820917/12500000000000 : ℝ)^3975
        have hw : |(-1728254657/10000000000 : ℝ)|=(1728254657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643755589/1250000000 : ℝ)|^4999 ≤ (43408083618183/100000000000000 : ℝ)^3975
        have hw : |(643755589/1250000000 : ℝ)|=(643755589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_2 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071092641/2000000000 : ℝ)*x 0 + (5150044909/10000000000 : ℝ)*x 1 + (-1728254537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071092641/2000000000 : ℝ)^4999 ≤ (45596596675133/100000000000000 : ℝ)^3975 := by
    have hnat : (1071092641 : ℕ)^4999*100000000000000^3975 ≤ 45596596675133^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071092641 2000000000 45596596675133 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150044909/10000000000 : ℝ)^4999 ≤ (21704042853191/50000000000000 : ℝ)^3975 := by
    have hnat : (5150044909 : ℕ)^4999*50000000000000^3975 ≤ 21704042853191^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150044909 10000000000 21704042853191 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1728254537/10000000000 : ℝ)^4999 ≤ (2748829401803/25000000000000 : ℝ)^3975 := by
    have hnat : (1728254537 : ℕ)^4999*25000000000000^3975 ≤ 2748829401803^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728254537 10000000000 2748829401803 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071092641/2000000000 : ℝ), (5150044909/10000000000 : ℝ), (-1728254537/10000000000 : ℝ)] ![(45596596675133/100000000000000 : ℝ), (21704042853191/50000000000000 : ℝ), (2748829401803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071092641/2000000000 : ℝ)|^4999 ≤ (45596596675133/100000000000000 : ℝ)^3975
        have hw : |(1071092641/2000000000 : ℝ)|=(1071092641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150044909/10000000000 : ℝ)|^4999 ≤ (21704042853191/50000000000000 : ℝ)^3975
        have hw : |(5150044909/10000000000 : ℝ)|=(5150044909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1728254537/10000000000 : ℝ)|^4999 ≤ (2748829401803/25000000000000 : ℝ)^3975
        have hw : |(-1728254537/10000000000 : ℝ)|=(1728254537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_3 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039914631/2500000000 : ℝ)*x 0 + (933929971/2500000000 : ℝ)*x 1 + (4616376749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039914631/2500000000 : ℝ)^4999 ≤ (16591784913509/50000000000000 : ℝ)^3975 := by
    have hnat : (1039914631 : ℕ)^4999*50000000000000^3975 ≤ 16591784913509^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039914631 2500000000 16591784913509 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933929971/2500000000 : ℝ)^4999 ≤ (28987690890217/100000000000000 : ℝ)^3975 := by
    have hnat : (933929971 : ℕ)^4999*100000000000000^3975 ≤ 28987690890217^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933929971 2500000000 28987690890217 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4616376749/10000000000 : ℝ)^4999 ≤ (4728592407821/12500000000000 : ℝ)^3975 := by
    have hnat : (4616376749 : ℕ)^4999*12500000000000^3975 ≤ 4728592407821^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616376749 10000000000 4728592407821 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039914631/2500000000 : ℝ), (933929971/2500000000 : ℝ), (4616376749/10000000000 : ℝ)] ![(16591784913509/50000000000000 : ℝ), (28987690890217/100000000000000 : ℝ), (4728592407821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039914631/2500000000 : ℝ)|^4999 ≤ (16591784913509/50000000000000 : ℝ)^3975
        have hw : |(1039914631/2500000000 : ℝ)|=(1039914631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933929971/2500000000 : ℝ)|^4999 ≤ (28987690890217/100000000000000 : ℝ)^3975
        have hw : |(933929971/2500000000 : ℝ)|=(933929971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4616376749/10000000000 : ℝ)|^4999 ≤ (4728592407821/12500000000000 : ℝ)^3975
        have hw : |(4616376749/10000000000 : ℝ)|=(4616376749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_4 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9726293/62500000 : ℝ)*x 0 + (1288328541/2500000000 : ℝ)*x 1 + (5478734321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9726293/62500000 : ℝ)^4999 ≤ (9636864338857/100000000000000 : ℝ)^3975 := by
    have hnat : (9726293 : ℕ)^4999*100000000000000^3975 ≤ 9636864338857^3975*62500000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9726293 62500000 9636864338857 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288328541/2500000000 : ℝ)^4999 ≤ (43442742622999/100000000000000 : ℝ)^3975 := by
    have hnat : (1288328541 : ℕ)^4999*100000000000000^3975 ≤ 43442742622999^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288328541 2500000000 43442742622999 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478734321/10000000000 : ℝ)^4999 ≤ (46920393015147/100000000000000 : ℝ)^3975 := by
    have hnat : (5478734321 : ℕ)^4999*100000000000000^3975 ≤ 46920393015147^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478734321 10000000000 46920393015147 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9726293/62500000 : ℝ), (1288328541/2500000000 : ℝ), (5478734321/10000000000 : ℝ)] ![(9636864338857/100000000000000 : ℝ), (43442742622999/100000000000000 : ℝ), (46920393015147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9726293/62500000 : ℝ)|^4999 ≤ (9636864338857/100000000000000 : ℝ)^3975
        have hw : |(-9726293/62500000 : ℝ)|=(9726293/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288328541/2500000000 : ℝ)|^4999 ≤ (43442742622999/100000000000000 : ℝ)^3975
        have hw : |(1288328541/2500000000 : ℝ)|=(1288328541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478734321/10000000000 : ℝ)|^4999 ≤ (46920393015147/100000000000000 : ℝ)^3975
        have hw : |(5478734321/10000000000 : ℝ)|=(5478734321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_5 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266530521/10000000000 : ℝ)*x 0 + (-699782423/5000000000 : ℝ)*x 1 + (2739367177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266530521/10000000000 : ℝ)^4999 ≤ (2790400613957/6250000000000 : ℝ)^3975 := by
    have hnat : (5266530521 : ℕ)^4999*6250000000000^3975 ≤ 2790400613957^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266530521 10000000000 2790400613957 6250000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699782423/5000000000 : ℝ)^4999 ≤ (8433196794157/100000000000000 : ℝ)^3975 := by
    have hnat : (699782423 : ℕ)^4999*100000000000000^3975 ≤ 8433196794157^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699782423 5000000000 8433196794157 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739367177/5000000000 : ℝ)^4999 ≤ (46920393370567/100000000000000 : ℝ)^3975 := by
    have hnat : (2739367177 : ℕ)^4999*100000000000000^3975 ≤ 46920393370567^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739367177 5000000000 46920393370567 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266530521/10000000000 : ℝ), (-699782423/5000000000 : ℝ), (2739367177/5000000000 : ℝ)] ![(2790400613957/6250000000000 : ℝ), (8433196794157/100000000000000 : ℝ), (46920393370567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266530521/10000000000 : ℝ)|^4999 ≤ (2790400613957/6250000000000 : ℝ)^3975
        have hw : |(5266530521/10000000000 : ℝ)|=(5266530521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-699782423/5000000000 : ℝ)|^4999 ≤ (8433196794157/100000000000000 : ℝ)^3975
        have hw : |(-699782423/5000000000 : ℝ)|=(699782423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739367177/5000000000 : ℝ)|^4999 ≤ (46920393370567/100000000000000 : ℝ)^3975
        have hw : |(2739367177/5000000000 : ℝ)|=(2739367177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_6 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266530443/10000000000 : ℝ)*x 0 + (1095746869/2000000000 : ℝ)*x 1 + (-1399564967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266530443/10000000000 : ℝ)^4999 ≤ (8929281798347/20000000000000 : ℝ)^3975 := by
    have hnat : (5266530443 : ℕ)^4999*20000000000000^3975 ≤ 8929281798347^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266530443 10000000000 8929281798347 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095746869/2000000000 : ℝ)^4999 ≤ (23460196636817/50000000000000 : ℝ)^3975 := by
    have hnat : (1095746869 : ℕ)^4999*50000000000000^3975 ≤ 23460196636817^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095746869 2000000000 23460196636817 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399564967/10000000000 : ℝ)^4999 ≤ (2108299427769/25000000000000 : ℝ)^3975 := by
    have hnat : (1399564967 : ℕ)^4999*25000000000000^3975 ≤ 2108299427769^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399564967 10000000000 2108299427769 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266530443/10000000000 : ℝ), (1095746869/2000000000 : ℝ), (-1399564967/10000000000 : ℝ)] ![(8929281798347/20000000000000 : ℝ), (23460196636817/50000000000000 : ℝ), (2108299427769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266530443/10000000000 : ℝ)|^4999 ≤ (8929281798347/20000000000000 : ℝ)^3975
        have hw : |(5266530443/10000000000 : ℝ)|=(5266530443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095746869/2000000000 : ℝ)|^4999 ≤ (23460196636817/50000000000000 : ℝ)^3975
        have hw : |(1095746869/2000000000 : ℝ)|=(1095746869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1399564967/10000000000 : ℝ)|^4999 ≤ (2108299427769/25000000000000 : ℝ)^3975
        have hw : |(-1399564967/10000000000 : ℝ)|=(1399564967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s1_7 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4160011463/10000000000 : ℝ)*x 0 + (921540747/2000000000 : ℝ)*x 1 + (187225561/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4160011463/10000000000 : ℝ)^4999 ≤ (33187110744661/100000000000000 : ℝ)^3975 := by
    have hnat : (4160011463 : ℕ)^4999*100000000000000^3975 ≤ 33187110744661^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160011463 10000000000 33187110744661 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921540747/2000000000 : ℝ)^4999 ≤ (3773938165837/10000000000000 : ℝ)^3975 := by
    have hnat : (921540747 : ℕ)^4999*10000000000000^3975 ≤ 3773938165837^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921540747 2000000000 3773938165837 10000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187225561/500000000 : ℝ)^4999 ≤ (1162940303107/4000000000000 : ℝ)^3975 := by
    have hnat : (187225561 : ℕ)^4999*4000000000000^3975 ≤ 1162940303107^3975*500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187225561 500000000 1162940303107 4000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4160011463/10000000000 : ℝ), (921540747/2000000000 : ℝ), (187225561/500000000 : ℝ)] ![(33187110744661/100000000000000 : ℝ), (3773938165837/10000000000000 : ℝ), (1162940303107/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4160011463/10000000000 : ℝ)|^4999 ≤ (33187110744661/100000000000000 : ℝ)^3975
        have hw : |(4160011463/10000000000 : ℝ)|=(4160011463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921540747/2000000000 : ℝ)|^4999 ≤ (3773938165837/10000000000000 : ℝ)^3975
        have hw : |(921540747/2000000000 : ℝ)|=(921540747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187225561/500000000 : ℝ)|^4999 ≤ (1162940303107/4000000000000 : ℝ)^3975
        have hw : |(187225561/500000000 : ℝ)|=(187225561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1670_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1147/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (261/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (683/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1147/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (261/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1147/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (261/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1147/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (261/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1147/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (261/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1147/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (261/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1147/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (261/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (261/5000 : ℝ) ^ (4995/1024 : ℝ) ≤ (27787973867027/50000000000000000000 : ℝ) := by
    have hpowers : (261/5000 : ℝ)^4995 ≤ (27787973867027/50000000000000000000 : ℝ)^1024 := by
      have hnat : (261 : ℕ)^4995*50000000000000000000^1024 ≤ 27787973867027^1024*5000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        261 5000 27787973867027 50000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (261/5000 : ℝ)) (X := (27787973867027/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1147/5000 : ℝ) ^ (4995/1024 : ℝ) ≤ (76036064365277473/100000000000000000000 : ℝ) := by
    have hpowers : (1147/5000 : ℝ)^4995 ≤ (76036064365277473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1147 : ℕ)^4995*100000000000000000000^1024 ≤ 76036064365277473^1024*5000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1147 5000 76036064365277473 100000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1147/5000 : ℝ)) (X := (76036064365277473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000027787973867027/25000000000000000000 : ℝ) ≤ (5000001139334241/5000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (25000027787973867027/25000000000000000000 : ℝ)^1024 ≤ (5000001139334241/5000000000000000 : ℝ)^4995 := by
      have hnat : (25000027787973867027 : ℕ)^1024*5000000000000000^4995 ≤ 5000001139334241^4995*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000027787973867027 25000000000000000000 5000001139334241 5000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001139334241/5000000000000000 : ℝ)) (X := (25000027787973867027/25000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100076091640313011527/100000000000000000000 : ℝ) ≤ (10001559445108917/10000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (100076091640313011527/100000000000000000000 : ℝ)^1024 ≤ (10001559445108917/10000000000000000 : ℝ)^4995 := by
      have hnat : (100076091640313011527 : ℕ)^1024*10000000000000000^4995 ≤ 10001559445108917^4995*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100076091640313011527 100000000000000000000 10001559445108917 10000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001559445108917/10000000000000000 : ℝ)) (X := (100076091640313011527/100000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076036064365277473/50000000000000000000 : ℝ) ≤ (1250389576443669/1250000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (50076036064365277473/50000000000000000000 : ℝ)^1024 ≤ (1250389576443669/1250000000000000 : ℝ)^4995 := by
      have hnat : (50076036064365277473 : ℕ)^1024*1250000000000000^4995 ≤ 1250389576443669^4995*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076036064365277473 50000000000000000000 1250389576443669 1250000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250389576443669/1250000000000000 : ℝ)) (X := (50076036064365277473/50000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27787973867027/50000000000000000000 : ℝ) ≤ ((4429594589009183991/4430000000000000000 : ℝ)+2*(311433288087/354400000000000 : ℝ)*(261/5000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (4429594589009183991/4430000000000000000 : ℝ)+2*(311433288087/354400000000000 : ℝ)*(261/5000 : ℝ)=(5000001139334241/5000000000000000 : ℝ) by norm_num, show 1+2*(27787973867027/50000000000000000000 : ℝ)=(25000027787973867027/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76036064365277473/100000000000000000000 : ℝ)+(27787973867027/50000000000000000000 : ℝ) ≤ ((4429594589009183991/4430000000000000000 : ℝ)+(311433288087/354400000000000 : ℝ)*((1147/5000 : ℝ)+(261/5000 : ℝ)))^(4995/1024 : ℝ) := by
    rw [show (4429594589009183991/4430000000000000000 : ℝ)+(311433288087/354400000000000 : ℝ)*((1147/5000 : ℝ)+(261/5000 : ℝ))=(10001559445108917/10000000000000000 : ℝ) by norm_num, show 1+(76036064365277473/100000000000000000000 : ℝ)+(27787973867027/50000000000000000000 : ℝ)=(100076091640313011527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76036064365277473/100000000000000000000 : ℝ) ≤ ((4429594589009183991/4430000000000000000 : ℝ)+2*(311433288087/354400000000000 : ℝ)*(1147/5000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (4429594589009183991/4430000000000000000 : ℝ)+2*(311433288087/354400000000000 : ℝ)*(1147/5000 : ℝ)=(1250389576443669/1250000000000000 : ℝ) by norm_num, show 1+2*(76036064365277473/100000000000000000000 : ℝ)=(50076036064365277473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4429594589009183991/4430000000000000000 : ℝ)*(X 1 0+X 2 0)+(311433288087/354400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (261/5000 : ℝ)) (hi := (1147/5000 : ℝ)) (c := (4429594589009183991/4430000000000000000 : ℝ)) (alpha := (311433288087/354400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4429594589009183991/4430000000000000000 : ℝ)*(X 0 1+X 2 1)+(311433288087/354400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (261/5000 : ℝ)) (hi := (1147/5000 : ℝ)) (c := (4429594589009183991/4430000000000000000 : ℝ)) (alpha := (311433288087/354400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4429594589009183991/4430000000000000000 : ℝ)*(X 0 2+X 1 2)+(311433288087/354400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (261/5000 : ℝ)) (hi := (1147/5000 : ℝ)) (c := (4429594589009183991/4430000000000000000 : ℝ)) (alpha := (311433288087/354400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-155607323/1000000000 : ℝ)*X 0 0+(2741024377/5000000000 : ℝ)*X 0 1+(5150044679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355463311/10000000000 : ℝ)*X 1 0+(-1728254657/10000000000 : ℝ)*X 1 1+(643755589/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071092641/2000000000 : ℝ)*X 2 0+(5150044909/10000000000 : ℝ)*X 2 1+(-1728254537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1039914631/2500000000 : ℝ)*X 0 0+(933929971/2500000000 : ℝ)*X 0 1+(4616376749/10000000000 : ℝ)*X 0 2+(1039914631/2500000000 : ℝ)*X 1 0+(933929971/2500000000 : ℝ)*X 1 1+(4616376749/10000000000 : ℝ)*X 1 2+(1039914631/2500000000 : ℝ)*X 2 0+(933929971/2500000000 : ℝ)*X 2 1+(4616376749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9726293/62500000 : ℝ)*X 0 0+(1288328541/2500000000 : ℝ)*X 0 1+(5478734321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266530521/10000000000 : ℝ)*X 1 0+(-699782423/5000000000 : ℝ)*X 1 1+(2739367177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266530443/10000000000 : ℝ)*X 2 0+(1095746869/2000000000 : ℝ)*X 2 1+(-1399564967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4160011463/10000000000 : ℝ)*X 0 0+(921540747/2000000000 : ℝ)*X 0 1+(187225561/500000000 : ℝ)*X 0 2+(4160011463/10000000000 : ℝ)*X 1 0+(921540747/2000000000 : ℝ)*X 1 1+(187225561/500000000 : ℝ)*X 1 2+(4160011463/10000000000 : ℝ)*X 2 0+(921540747/2000000000 : ℝ)*X 2 1+(187225561/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73863199166171118993909/17720000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177895517/50000000000000 : ℝ)*(base19) + (53536353/50000000000000 : ℝ)*(base23) + (132749979/100000000000000 : ℝ)*(lower2) + (81552989/100000000000000 : ℝ)*(upper3) + (1573859/5000000000000 : ℝ)*(lower4) + (2073768259811831/100000000000000 : ℝ)*(major0) + (2073768259811831/100000000000000 : ℝ)*(major1) + (2073768259811831/100000000000000 : ℝ)*(major2) + (753003710888971/25000000000000 : ℝ)*(sp0) + (60240351177209/2000000000000 : ℝ)*(sp1) + (3012017807578779/100000000000000 : ℝ)*(sp2) + (567758407379041/50000000000000 : ℝ)*(sp3) + (7677739/250000000000 : ℝ)*(sp4) + (825634511/50000000000000 : ℝ)*(sp7) + (35484952063347/3125000000000 : ℝ)*(f.failure) + (753004478662871/25000000000000 : ℝ)*(f.sum) + (42461576458817/17720000000000000000000000000 : ℝ)*base65 + (1035320760158189979/443000000000000000000000000000000 : ℝ)*base68 + (1086851026341810021/443000000000000000000000000000000 : ℝ)*base69 + (3194446114911810021/443000000000000000000000000000000 : ℝ)*base71 + (20689086664463/17720000000000000000000000000 : ℝ)*base74 + (3459996903489810021/443000000000000000000000000000000 : ℝ)*base75 + (406867783123189979/443000000000000000000000000000000 : ℝ)*base78 + (643593214683189979/443000000000000000000000000000000 : ℝ)*base80 + (72877688869097/17720000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (78323/78125000000000000000 : ℝ)*base89 + (78323/78125000000000000000 : ℝ)*base91 + (78323/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1329262676390685025297558521/110750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1961883453/100000000000000 : ℝ)*(base19) + (1948013063/100000000000000 : ℝ)*(base23) + (141488927/50000000000000 : ℝ)*(upper3) + (25372083/100000000000000 : ℝ)*(lower4) + (30229191/10000000000000 : ℝ)*(upper5) + (1057860123205723/50000000000000 : ℝ)*(major0) + (1057860123205723/50000000000000 : ℝ)*(major1) + (1057860123205723/50000000000000 : ℝ)*(major2) + (18685788333/100000000000000 : ℝ)*(sp1) + (1770663097/10000000000000 : ℝ)*(sp2) + (768237569305117/25000000000000 : ℝ)*(sp4) + (1536464814774341/50000000000000 : ℝ)*(sp5) + (614586124515287/20000000000000 : ℝ)*(sp6) + (579244907761681/50000000000000 : ℝ)*(sp7) + (579244907761681/50000000000000 : ℝ)*(f.failure) + (768237569305117/25000000000000 : ℝ)*(f.sum) + (11708140255141/8860000000000000000000000000 : ℝ)*base65 + (670138574201942993/221500000000000000000000000000000 : ℝ)*base67 + (259306002987057007/221500000000000000000000000000000 : ℝ)*base70 + (741083547018442993/221500000000000000000000000000000 : ℝ)*base71 + (11841673293281/8860000000000000000000000000 : ℝ)*base73 + (35919774551057007/221500000000000000000000000000000 : ℝ)*base76 + (592967456113442993/221500000000000000000000000000000 : ℝ)*base77 + (1751660377962442993/221500000000000000000000000000000 : ℝ)*base79 + (3713945311601/8860000000000000000000000000 : ℝ)*base81 + (19979/1250000000000000000000 : ℝ)*base89 + (19979/1250000000000000000000 : ℝ)*base91 + (19979/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1670_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1147/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (261/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (683/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1670_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1670_s2_0 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-39091217/250000000 : ℝ)*x 0 + (340263529/625000000 : ℝ)*x 1 + (2591430303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39091217/250000000 : ℝ)^4999 ≤ (9694855194483/100000000000000 : ℝ)^3975 := by
    have hnat : (39091217 : ℕ)^4999*100000000000000^3975 ≤ 9694855194483^3975*250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39091217 250000000 9694855194483 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340263529/625000000 : ℝ)^4999 ≤ (46548927845493/100000000000000 : ℝ)^3975 := by
    have hnat : (340263529 : ℕ)^4999*100000000000000^3975 ≤ 46548927845493^3975*625000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340263529 625000000 46548927845493 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591430303/5000000000 : ℝ)^4999 ≤ (43756216940293/100000000000000 : ℝ)^3975 := by
    have hnat : (2591430303 : ℕ)^4999*100000000000000^3975 ≤ 43756216940293^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591430303 5000000000 43756216940293 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39091217/250000000 : ℝ), (340263529/625000000 : ℝ), (2591430303/5000000000 : ℝ)] ![(9694855194483/100000000000000 : ℝ), (46548927845493/100000000000000 : ℝ), (43756216940293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39091217/250000000 : ℝ)|^4999 ≤ (9694855194483/100000000000000 : ℝ)^3975
        have hw : |(-39091217/250000000 : ℝ)|=(39091217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340263529/625000000 : ℝ)|^4999 ≤ (46548927845493/100000000000000 : ℝ)^3975
        have hw : |(340263529/625000000 : ℝ)|=(340263529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591430303/5000000000 : ℝ)|^4999 ≤ (43756216940293/100000000000000 : ℝ)^3975
        have hw : |(2591430303/5000000000 : ℝ)|=(2591430303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_1 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345386961/10000000000 : ℝ)*x 0 + (-1698157113/10000000000 : ℝ)*x 1 + (2591430317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345386961/10000000000 : ℝ)^4999 ≤ (2843045819591/6250000000000 : ℝ)^3975 := by
    have hnat : (5345386961 : ℕ)^4999*6250000000000^3975 ≤ 2843045819591^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345386961 10000000000 2843045819591 6250000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698157113/10000000000 : ℝ)^4999 ≤ (1344381203887/12500000000000 : ℝ)^3975 := by
    have hnat : (1698157113 : ℕ)^4999*12500000000000^3975 ≤ 1344381203887^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698157113 10000000000 1344381203887 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591430317/5000000000 : ℝ)^4999 ≤ (43756217237579/100000000000000 : ℝ)^3975 := by
    have hnat : (2591430317 : ℕ)^4999*100000000000000^3975 ≤ 43756217237579^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591430317 5000000000 43756217237579 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345386961/10000000000 : ℝ), (-1698157113/10000000000 : ℝ), (2591430317/5000000000 : ℝ)] ![(2843045819591/6250000000000 : ℝ), (1344381203887/12500000000000 : ℝ), (43756217237579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345386961/10000000000 : ℝ)|^4999 ≤ (2843045819591/6250000000000 : ℝ)^3975
        have hw : |(5345386961/10000000000 : ℝ)|=(5345386961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1698157113/10000000000 : ℝ)|^4999 ≤ (1344381203887/12500000000000 : ℝ)^3975
        have hw : |(-1698157113/10000000000 : ℝ)|=(1698157113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591430317/5000000000 : ℝ)|^4999 ≤ (43756217237579/100000000000000 : ℝ)^3975
        have hw : |(2591430317/5000000000 : ℝ)|=(2591430317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_2 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069077367/2000000000 : ℝ)*x 0 + (2591430317/5000000000 : ℝ)*x 1 + (-1698157283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069077367/2000000000 : ℝ)^4999 ≤ (22744365882493/50000000000000 : ℝ)^3975 := by
    have hnat : (1069077367 : ℕ)^4999*50000000000000^3975 ≤ 22744365882493^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069077367 2000000000 22744365882493 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591430317/5000000000 : ℝ)^4999 ≤ (43756217237579/100000000000000 : ℝ)^3975 := by
    have hnat : (2591430317 : ℕ)^4999*100000000000000^3975 ≤ 43756217237579^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591430317 5000000000 43756217237579 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1698157283/10000000000 : ℝ)^4999 ≤ (10755050985129/100000000000000 : ℝ)^3975 := by
    have hnat : (1698157283 : ℕ)^4999*100000000000000^3975 ≤ 10755050985129^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698157283 10000000000 10755050985129 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069077367/2000000000 : ℝ), (2591430317/5000000000 : ℝ), (-1698157283/10000000000 : ℝ)] ![(22744365882493/50000000000000 : ℝ), (43756217237579/100000000000000 : ℝ), (10755050985129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069077367/2000000000 : ℝ)|^4999 ≤ (22744365882493/50000000000000 : ℝ)^3975
        have hw : |(1069077367/2000000000 : ℝ)|=(1069077367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591430317/5000000000 : ℝ)|^4999 ≤ (43756217237579/100000000000000 : ℝ)^3975
        have hw : |(2591430317/5000000000 : ℝ)|=(2591430317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1698157283/10000000000 : ℝ)|^4999 ≤ (10755050985129/100000000000000 : ℝ)^3975
        have hw : |(-1698157283/10000000000 : ℝ)|=(1698157283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_3 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104133293/250000000 : ℝ)*x 0 + (1914431453/5000000000 : ℝ)*x 1 + (904424411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104133293/250000000 : ℝ)^4999 ≤ (519382757147/1562500000000 : ℝ)^3975 := by
    have hnat : (104133293 : ℕ)^4999*1562500000000^3975 ≤ 519382757147^3975*250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104133293 250000000 519382757147 1562500000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1914431453/5000000000 : ℝ)^4999 ≤ (29899533041769/100000000000000 : ℝ)^3975 := by
    have hnat : (1914431453 : ℕ)^4999*100000000000000^3975 ≤ 29899533041769^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914431453 5000000000 29899533041769 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904424411/2000000000 : ℝ)^4999 ≤ (9214992621593/25000000000000 : ℝ)^3975 := by
    have hnat : (904424411 : ℕ)^4999*25000000000000^3975 ≤ 9214992621593^3975*2000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904424411 2000000000 9214992621593 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104133293/250000000 : ℝ), (1914431453/5000000000 : ℝ), (904424411/2000000000 : ℝ)] ![(519382757147/1562500000000 : ℝ), (29899533041769/100000000000000 : ℝ), (9214992621593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104133293/250000000 : ℝ)|^4999 ≤ (519382757147/1562500000000 : ℝ)^3975
        have hw : |(104133293/250000000 : ℝ)|=(104133293/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1914431453/5000000000 : ℝ)|^4999 ≤ (29899533041769/100000000000000 : ℝ)^3975
        have hw : |(1914431453/5000000000 : ℝ)|=(1914431453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904424411/2000000000 : ℝ)|^4999 ≤ (9214992621593/25000000000000 : ℝ)^3975
        have hw : |(904424411/2000000000 : ℝ)|=(904424411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_4 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-781857237/5000000000 : ℝ)*x 0 + (5184891491/10000000000 : ℝ)*x 1 + (1360540811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (781857237/5000000000 : ℝ)^4999 ≤ (9695368217431/100000000000000 : ℝ)^3975 := by
    have hnat : (781857237 : ℕ)^4999*100000000000000^3975 ≤ 9695368217431^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781857237 5000000000 9695368217431 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184891491/10000000000 : ℝ)^4999 ≤ (10944445162677/25000000000000 : ℝ)^3975 := by
    have hnat : (5184891491 : ℕ)^4999*25000000000000^3975 ≤ 10944445162677^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184891491 10000000000 10944445162677 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360540811/2500000000 : ℝ)^4999 ≤ (46526851118441/100000000000000 : ℝ)^3975 := by
    have hnat : (1360540811 : ℕ)^4999*100000000000000^3975 ≤ 46526851118441^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360540811 2500000000 46526851118441 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-781857237/5000000000 : ℝ), (5184891491/10000000000 : ℝ), (1360540811/2500000000 : ℝ)] ![(9695368217431/100000000000000 : ℝ), (10944445162677/25000000000000 : ℝ), (46526851118441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-781857237/5000000000 : ℝ)|^4999 ≤ (9695368217431/100000000000000 : ℝ)^3975
        have hw : |(-781857237/5000000000 : ℝ)|=(781857237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184891491/10000000000 : ℝ)|^4999 ≤ (10944445162677/25000000000000 : ℝ)^3975
        have hw : |(5184891491/10000000000 : ℝ)|=(5184891491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360540811/2500000000 : ℝ)|^4999 ≤ (46526851118441/100000000000000 : ℝ)^3975
        have hw : |(1360540811/2500000000 : ℝ)|=(1360540811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_5 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637707813/5000000000 : ℝ)*x 0 + (-359713489/2500000000 : ℝ)*x 1 + (217686529/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637707813/5000000000 : ℝ)^4999 ≤ (22370578342019/50000000000000 : ℝ)^3975 := by
    have hnat : (2637707813 : ℕ)^4999*50000000000000^3975 ≤ 22370578342019^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637707813 5000000000 22370578342019 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359713489/2500000000 : ℝ)^4999 ≤ (4365996191823/50000000000000 : ℝ)^3975 := by
    have hnat : (359713489 : ℕ)^4999*50000000000000^3975 ≤ 4365996191823^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359713489 2500000000 4365996191823 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217686529/400000000 : ℝ)^4999 ≤ (23263425457079/50000000000000 : ℝ)^3975 := by
    have hnat : (217686529 : ℕ)^4999*50000000000000^3975 ≤ 23263425457079^3975*400000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217686529 400000000 23263425457079 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637707813/5000000000 : ℝ), (-359713489/2500000000 : ℝ), (217686529/400000000 : ℝ)] ![(22370578342019/50000000000000 : ℝ), (4365996191823/50000000000000 : ℝ), (23263425457079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637707813/5000000000 : ℝ)|^4999 ≤ (22370578342019/50000000000000 : ℝ)^3975
        have hw : |(2637707813/5000000000 : ℝ)|=(2637707813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359713489/2500000000 : ℝ)|^4999 ≤ (4365996191823/50000000000000 : ℝ)^3975
        have hw : |(-359713489/2500000000 : ℝ)|=(359713489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217686529/400000000 : ℝ)|^4999 ≤ (23263425457079/50000000000000 : ℝ)^3975
        have hw : |(217686529/400000000 : ℝ)|=(217686529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_6 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637707339/5000000000 : ℝ)*x 0 + (5442163873/10000000000 : ℝ)*x 1 + (-44964199/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637707339/5000000000 : ℝ)^4999 ≤ (11185286643197/25000000000000 : ℝ)^3975 := by
    have hnat : (2637707339 : ℕ)^4999*25000000000000^3975 ≤ 11185286643197^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637707339 5000000000 11185286643197 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442163873/10000000000 : ℝ)^4999 ≤ (1861074315251/4000000000000 : ℝ)^3975 := by
    have hnat : (5442163873 : ℕ)^4999*4000000000000^3975 ≤ 1861074315251^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442163873 10000000000 1861074315251 4000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44964199/312500000 : ℝ)^4999 ≤ (8731995528061/100000000000000 : ℝ)^3975 := by
    have hnat : (44964199 : ℕ)^4999*100000000000000^3975 ≤ 8731995528061^3975*312500000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44964199 312500000 8731995528061 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637707339/5000000000 : ℝ), (5442163873/10000000000 : ℝ), (-44964199/312500000 : ℝ)] ![(11185286643197/25000000000000 : ℝ), (1861074315251/4000000000000 : ℝ), (8731995528061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637707339/5000000000 : ℝ)|^4999 ≤ (11185286643197/25000000000000 : ℝ)^3975
        have hw : |(2637707339/5000000000 : ℝ)|=(2637707339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442163873/10000000000 : ℝ)|^4999 ≤ (1861074315251/4000000000000 : ℝ)^3975
        have hw : |(5442163873/10000000000 : ℝ)|=(5442163873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44964199/312500000 : ℝ)|^4999 ≤ (8731995528061/100000000000000 : ℝ)^3975
        have hw : |(-44964199/312500000 : ℝ)|=(44964199/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s2_7 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165504129/10000000000 : ℝ)*x 0 + (4516734303/10000000000 : ℝ)*x 1 + (19171543/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165504129/10000000000 : ℝ)^4999 ≤ (33242226776341/100000000000000 : ℝ)^3975 := by
    have hnat : (4165504129 : ℕ)^4999*100000000000000^3975 ≤ 33242226776341^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165504129 10000000000 33242226776341 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516734303/10000000000 : ℝ)^4999 ≤ (9201187518943/25000000000000 : ℝ)^3975 := by
    have hnat : (4516734303 : ℕ)^4999*25000000000000^3975 ≤ 9201187518943^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516734303 10000000000 9201187518943 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19171543/50000000 : ℝ)^4999 ≤ (7488255783691/25000000000000 : ℝ)^3975 := by
    have hnat : (19171543 : ℕ)^4999*25000000000000^3975 ≤ 7488255783691^3975*50000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19171543 50000000 7488255783691 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165504129/10000000000 : ℝ), (4516734303/10000000000 : ℝ), (19171543/50000000 : ℝ)] ![(33242226776341/100000000000000 : ℝ), (9201187518943/25000000000000 : ℝ), (7488255783691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165504129/10000000000 : ℝ)|^4999 ≤ (33242226776341/100000000000000 : ℝ)^3975
        have hw : |(4165504129/10000000000 : ℝ)|=(4165504129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516734303/10000000000 : ℝ)|^4999 ≤ (9201187518943/25000000000000 : ℝ)^3975
        have hw : |(4516734303/10000000000 : ℝ)|=(4516734303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19171543/50000000 : ℝ)|^4999 ≤ (7488255783691/25000000000000 : ℝ)^3975
        have hw : |(19171543/50000000 : ℝ)|=(19171543/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1670_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (683/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10719/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16283/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (683/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (683/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (683/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (683/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (683/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (683/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10011/100000 : ℝ) ^ (4995/1024 : ℝ) ≤ (1331678338750421/100000000000000000000 : ℝ) := by
    have hpowers : (10011/100000 : ℝ)^4995 ≤ (1331678338750421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10011 : ℕ)^4995*100000000000000000000^1024 ≤ 1331678338750421^1024*100000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011 100000 1331678338750421 100000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10011/100000 : ℝ)) (X := (1331678338750421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (683/4000 : ℝ) ^ (4995/1024 : ℝ) ≤ (9004913260173927/50000000000000000000 : ℝ) := by
    have hpowers : (683/4000 : ℝ)^4995 ≤ (9004913260173927/50000000000000000000 : ℝ)^1024 := by
      have hnat : (683 : ℕ)^4995*50000000000000000000^1024 ≤ 9004913260173927^1024*4000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 4000 9004913260173927 50000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/4000 : ℝ)) (X := (9004913260173927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001331678338750421/50000000000000000000 : ℝ) ≤ (1000005459956687/1000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (50001331678338750421/50000000000000000000 : ℝ)^1024 ≤ (1000005459956687/1000000000000000 : ℝ)^4995 := by
      have hnat : (50001331678338750421 : ℕ)^1024*1000000000000000^4995 ≤ 1000005459956687^4995*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001331678338750421 50000000000000000000 1000005459956687 1000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005459956687/1000000000000000 : ℝ)) (X := (50001331678338750421/50000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000773660194363931/4000000000000000000 : ℝ) ≤ (10000396480049051/10000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (4000773660194363931/4000000000000000000 : ℝ)^1024 ≤ (10000396480049051/10000000000000000 : ℝ)^4995 := by
      have hnat : (4000773660194363931 : ℕ)^1024*10000000000000000^4995 ≤ 10000396480049051^4995*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000773660194363931 4000000000000000000 10000396480049051 10000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000396480049051/10000000000000000 : ℝ)) (X := (4000773660194363931/4000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009004913260173927/25000000000000000000 : ℝ) ≤ (312523073766601/312500000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (25009004913260173927/25000000000000000000 : ℝ)^1024 ≤ (312523073766601/312500000000000 : ℝ)^4995 := by
      have hnat : (25009004913260173927 : ℕ)^1024*312500000000000^4995 ≤ 312523073766601^4995*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009004913260173927 25000000000000000000 312523073766601 312500000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312523073766601/312500000000000 : ℝ)) (X := (25009004913260173927/25000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1331678338750421/100000000000000000000 : ℝ) ≤ ((35316770280163070849/35320000000000000000 : ℝ)+2*(341880482181/706400000000000 : ℝ)*(10011/100000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (35316770280163070849/35320000000000000000 : ℝ)+2*(341880482181/706400000000000 : ℝ)*(10011/100000 : ℝ)=(1000005459956687/1000000000000000 : ℝ) by norm_num, show 1+2*(1331678338750421/100000000000000000000 : ℝ)=(50001331678338750421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9004913260173927/50000000000000000000 : ℝ)+(1331678338750421/100000000000000000000 : ℝ) ≤ ((35316770280163070849/35320000000000000000 : ℝ)+(341880482181/706400000000000 : ℝ)*((683/4000 : ℝ)+(10011/100000 : ℝ)))^(4995/1024 : ℝ) := by
    rw [show (35316770280163070849/35320000000000000000 : ℝ)+(341880482181/706400000000000 : ℝ)*((683/4000 : ℝ)+(10011/100000 : ℝ))=(10000396480049051/10000000000000000 : ℝ) by norm_num, show 1+(9004913260173927/50000000000000000000 : ℝ)+(1331678338750421/100000000000000000000 : ℝ)=(4000773660194363931/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9004913260173927/50000000000000000000 : ℝ) ≤ ((35316770280163070849/35320000000000000000 : ℝ)+2*(341880482181/706400000000000 : ℝ)*(683/4000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (35316770280163070849/35320000000000000000 : ℝ)+2*(341880482181/706400000000000 : ℝ)*(683/4000 : ℝ)=(312523073766601/312500000000000 : ℝ) by norm_num, show 1+2*(9004913260173927/50000000000000000000 : ℝ)=(25009004913260173927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35316770280163070849/35320000000000000000 : ℝ)*(X 1 0+X 2 0)+(341880482181/706400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (683/4000 : ℝ)) (c := (35316770280163070849/35320000000000000000 : ℝ)) (alpha := (341880482181/706400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35316770280163070849/35320000000000000000 : ℝ)*(X 0 1+X 2 1)+(341880482181/706400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (683/4000 : ℝ)) (c := (35316770280163070849/35320000000000000000 : ℝ)) (alpha := (341880482181/706400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35316770280163070849/35320000000000000000 : ℝ)*(X 0 2+X 1 2)+(341880482181/706400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (683/4000 : ℝ)) (c := (35316770280163070849/35320000000000000000 : ℝ)) (alpha := (341880482181/706400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-39091217/250000000 : ℝ)*X 0 0+(340263529/625000000 : ℝ)*X 0 1+(2591430303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345386961/10000000000 : ℝ)*X 1 0+(-1698157113/10000000000 : ℝ)*X 1 1+(2591430317/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069077367/2000000000 : ℝ)*X 2 0+(2591430317/5000000000 : ℝ)*X 2 1+(-1698157283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((104133293/250000000 : ℝ)*X 0 0+(1914431453/5000000000 : ℝ)*X 0 1+(904424411/2000000000 : ℝ)*X 0 2+(104133293/250000000 : ℝ)*X 1 0+(1914431453/5000000000 : ℝ)*X 1 1+(904424411/2000000000 : ℝ)*X 1 2+(104133293/250000000 : ℝ)*X 2 0+(1914431453/5000000000 : ℝ)*X 2 1+(904424411/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-781857237/5000000000 : ℝ)*X 0 0+(5184891491/10000000000 : ℝ)*X 0 1+(1360540811/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2637707813/5000000000 : ℝ)*X 1 0+(-359713489/2500000000 : ℝ)*X 1 1+(217686529/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2637707339/5000000000 : ℝ)*X 2 0+(5442163873/10000000000 : ℝ)*X 2 1+(-44964199/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4165504129/10000000000 : ℝ)*X 0 0+(4516734303/10000000000 : ℝ)*X 0 1+(19171543/50000000 : ℝ)*X 0 2+(4165504129/10000000000 : ℝ)*X 1 0+(4516734303/10000000000 : ℝ)*X 1 1+(19171543/50000000 : ℝ)*X 1 2+(4165504129/10000000000 : ℝ)*X 2 0+(4516734303/10000000000 : ℝ)*X 2 1+(19171543/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5827239681281843807377855917/441500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2061525127/100000000000000 : ℝ)*(base19) + (1852117251/100000000000000 : ℝ)*(base23) + (63725859/100000000000000 : ℝ)*(lower2) + (400801953/100000000000000 : ℝ)*(upper3) + (82763293/50000000000000 : ℝ)*(upper5) + (658591761264763/25000000000000 : ℝ)*(major0) + (658591761264763/25000000000000 : ℝ)*(major1) + (658591761264763/25000000000000 : ℝ)*(major2) + (956557214943269/25000000000000 : ℝ)*(sp0) + (1913125026019533/50000000000000 : ℝ)*(sp1) + (191312513072347/5000000000000 : ℝ)*(sp2) + (1442470728021457/100000000000000 : ℝ)*(sp3) + (5813447779/25000000000000 : ℝ)*(sp4) + (2702143687/25000000000000 : ℝ)*(sp7) + (721240768298103/50000000000000 : ℝ)*(f.failure) + (119570378548881/3125000000000 : ℝ)*(f.sum) + (1154590513663/8830000000000000000000000000 : ℝ)*base65 + (5107839831623343787/883000000000000000000000000000000 : ℝ)*base67 + (7796504731136343787/883000000000000000000000000000000 : ℝ)*base69 + (4728152434707343787/883000000000000000000000000000000 : ℝ)*base71 + (16467267065137/8830000000000000000000000000 : ℝ)*base74 + (9780832234764343787/883000000000000000000000000000000 : ℝ)*base75 + (8023493888165343787/883000000000000000000000000000000 : ℝ)*base77 + (18615229692203343787/883000000000000000000000000000000 : ℝ)*base79 + (13856454051347/8830000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (8638477/1250000000000000000000 : ℝ)*base89 + (8638477/1250000000000000000000 : ℝ)*base91 + (8638477/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17551127917723379567555324817/1766000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1176704243/50000000000000 : ℝ)*(base19) + (1059331961/50000000000000 : ℝ)*(base23) + (262979377/100000000000000 : ℝ)*(upper2) + (167162439/50000000000000 : ℝ)*(upper3) + (192469687/50000000000000 : ℝ)*(upper5) + (2676146468744411/100000000000000 : ℝ)*(major0) + (2676146468744411/100000000000000 : ℝ)*(major1) + (2676146468744411/100000000000000 : ℝ)*(major2) + (28188500463/100000000000000 : ℝ)*(sp1) + (12783868547/50000000000000 : ℝ)*(sp2) + (3886934209159739/100000000000000 : ℝ)*(sp4) + (388690366725079/10000000000000 : ℝ)*(sp5) + (1943453261379361/50000000000000 : ℝ)*(sp6) + (146535839705071/10000000000000 : ℝ)*(sp7) + (146535839705071/10000000000000 : ℝ)*(f.failure) + (3886934209159739/100000000000000 : ℝ)*(f.sum) + (97116647023111/35320000000000000000000000000 : ℝ)*base65 + (43359301252742675061/3532000000000000000000000000000000 : ℝ)*base68 + (9201615160973324939/3532000000000000000000000000000000 : ℝ)*base69 + (27610124180750675061/3532000000000000000000000000000000 : ℝ)*base72 + (126445434847329/35320000000000000000000000000 : ℝ)*base74 + (17829621370258675061/3532000000000000000000000000000000 : ℝ)*base76 + (11204537200013324939/3532000000000000000000000000000000 : ℝ)*base77 + (4921700403938675061/3532000000000000000000000000000000 : ℝ)*base80 + (70664319405751/35320000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (731989/250000000000000000000 : ℝ)*base89 + (731989/250000000000000000000 : ℝ)*base91 + (731989/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1670_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (683/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1670_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1670_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1670_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1670_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1670_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1670_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
