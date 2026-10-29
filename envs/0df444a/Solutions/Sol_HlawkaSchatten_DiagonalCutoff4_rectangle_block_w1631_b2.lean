-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1631_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:00.183898+00:00
-- url     : https://prove2.me/submissions/cb88a5cd-801e-445c-983c-dd94e06d577d

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
theorem support_rectangle_w1631_box_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-346956463/2500000000 : ℝ)*x 0 + (5412781421/10000000000 : ℝ)*x 1 + (216511257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (346956463/2500000000 : ℝ)^4843 ≤ (8172720752501/100000000000000 : ℝ)^3819 := by
    have hnat : (346956463 : ℕ)^4843*100000000000000^3819 ≤ 8172720752501^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346956463 2500000000 8172720752501 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412781421/10000000000 : ℝ)^4843 ≤ (45913639594471/100000000000000 : ℝ)^3819 := by
    have hnat : (5412781421 : ℕ)^4843*100000000000000^3819 ≤ 45913639594471^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412781421 10000000000 45913639594471 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216511257/400000000 : ℝ)^4843 ≤ (45913639637499/100000000000000 : ℝ)^3819 := by
    have hnat : (216511257 : ℕ)^4843*100000000000000^3819 ≤ 45913639637499^3819*400000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216511257 400000000 45913639637499 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-346956463/2500000000 : ℝ), (5412781421/10000000000 : ℝ), (216511257/400000000 : ℝ)] ![(8172720752501/100000000000000 : ℝ), (45913639594471/100000000000000 : ℝ), (45913639637499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-346956463/2500000000 : ℝ)|^4843 ≤ (8172720752501/100000000000000 : ℝ)^3819
        have hw : |(-346956463/2500000000 : ℝ)|=(346956463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412781421/10000000000 : ℝ)|^4843 ≤ (45913639594471/100000000000000 : ℝ)^3819
        have hw : |(5412781421/10000000000 : ℝ)|=(5412781421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216511257/400000000 : ℝ)|^4843 ≤ (45913639637499/100000000000000 : ℝ)^3819
        have hw : |(216511257/400000000 : ℝ)|=(216511257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251247917/10000000000 : ℝ)*x 0 + (-1614774713/10000000000 : ℝ)*x 1 + (5412781203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251247917/10000000000 : ℝ)^4843 ≤ (44183047503649/100000000000000 : ℝ)^3819 := by
    have hnat : (5251247917 : ℕ)^4843*100000000000000^3819 ≤ 44183047503649^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251247917 10000000000 44183047503649 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614774713/10000000000 : ℝ)^4843 ≤ (9903315236317/100000000000000 : ℝ)^3819 := by
    have hnat : (1614774713 : ℕ)^4843*100000000000000^3819 ≤ 9903315236317^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614774713 10000000000 9903315236317 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412781203/10000000000 : ℝ)^4843 ≤ (45913637249473/100000000000000 : ℝ)^3819 := by
    have hnat : (5412781203 : ℕ)^4843*100000000000000^3819 ≤ 45913637249473^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412781203 10000000000 45913637249473 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251247917/10000000000 : ℝ), (-1614774713/10000000000 : ℝ), (5412781203/10000000000 : ℝ)] ![(44183047503649/100000000000000 : ℝ), (9903315236317/100000000000000 : ℝ), (45913637249473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251247917/10000000000 : ℝ)|^4843 ≤ (44183047503649/100000000000000 : ℝ)^3819
        have hw : |(5251247917/10000000000 : ℝ)|=(5251247917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1614774713/10000000000 : ℝ)|^4843 ≤ (9903315236317/100000000000000 : ℝ)^3819
        have hw : |(-1614774713/10000000000 : ℝ)|=(1614774713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412781203/10000000000 : ℝ)|^4843 ≤ (45913637249473/100000000000000 : ℝ)^3819
        have hw : |(5412781203/10000000000 : ℝ)|=(5412781203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625623899/5000000000 : ℝ)*x 0 + (5412781287/10000000000 : ℝ)*x 1 + (-807387379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625623899/5000000000 : ℝ)^4843 ≤ (22091523116969/50000000000000 : ℝ)^3819 := by
    have hnat : (2625623899 : ℕ)^4843*50000000000000^3819 ≤ 22091523116969^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625623899 5000000000 22091523116969 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412781287/10000000000 : ℝ)^4843 ≤ (918272763061/2000000000000 : ℝ)^3819 := by
    have hnat : (5412781287 : ℕ)^4843*2000000000000^3819 ≤ 918272763061^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412781287 10000000000 918272763061 2000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807387379/5000000000 : ℝ)^4843 ≤ (9903315586299/100000000000000 : ℝ)^3819 := by
    have hnat : (807387379 : ℕ)^4843*100000000000000^3819 ≤ 9903315586299^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807387379 5000000000 9903315586299 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625623899/5000000000 : ℝ), (5412781287/10000000000 : ℝ), (-807387379/5000000000 : ℝ)] ![(22091523116969/50000000000000 : ℝ), (918272763061/2000000000000 : ℝ), (9903315586299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625623899/5000000000 : ℝ)|^4843 ≤ (22091523116969/50000000000000 : ℝ)^3819
        have hw : |(2625623899/5000000000 : ℝ)|=(2625623899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412781287/10000000000 : ℝ)|^4843 ≤ (918272763061/2000000000000 : ℝ)^3819
        have hw : |(5412781287/10000000000 : ℝ)|=(5412781287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-807387379/5000000000 : ℝ)|^4843 ≤ (9903315586299/100000000000000 : ℝ)^3819
        have hw : |(-807387379/5000000000 : ℝ)|=(807387379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1118428783/2500000000 : ℝ)*x 0 + (2034419311/5000000000 : ℝ)*x 1 + (2034419259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118428783/2500000000 : ℝ)^4843 ≤ (7211588971773/20000000000000 : ℝ)^3819 := by
    have hnat : (1118428783 : ℕ)^4843*20000000000000^3819 ≤ 7211588971773^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118428783 2500000000 7211588971773 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034419311/5000000000 : ℝ)^4843 ≤ (15985514043349/50000000000000 : ℝ)^3819 := by
    have hnat : (2034419311 : ℕ)^4843*50000000000000^3819 ≤ 15985514043349^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034419311 5000000000 15985514043349 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2034419259/5000000000 : ℝ)^4843 ≤ (31971027050401/100000000000000 : ℝ)^3819 := by
    have hnat : (2034419259 : ℕ)^4843*100000000000000^3819 ≤ 31971027050401^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034419259 5000000000 31971027050401 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118428783/2500000000 : ℝ), (2034419311/5000000000 : ℝ), (2034419259/5000000000 : ℝ)] ![(7211588971773/20000000000000 : ℝ), (15985514043349/50000000000000 : ℝ), (31971027050401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118428783/2500000000 : ℝ)|^4843 ≤ (7211588971773/20000000000000 : ℝ)^3819
        have hw : |(1118428783/2500000000 : ℝ)|=(1118428783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2034419311/5000000000 : ℝ)|^4843 ≤ (15985514043349/50000000000000 : ℝ)^3819
        have hw : |(2034419311/5000000000 : ℝ)|=(2034419311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2034419259/5000000000 : ℝ)|^4843 ≤ (31971027050401/100000000000000 : ℝ)^3819
        have hw : |(2034419259/5000000000 : ℝ)|=(2034419259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928504961/10000000000 : ℝ)*x 0 + (325945227/625000000 : ℝ)*x 1 + (5215122263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928504961/10000000000 : ℝ)^4843 ≤ (12404088178381/100000000000000 : ℝ)^3819 := by
    have hnat : (1928504961 : ℕ)^4843*100000000000000^3819 ≤ 12404088178381^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928504961 10000000000 12404088178381 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325945227/625000000 : ℝ)^4843 ≤ (43797963196509/100000000000000 : ℝ)^3819 := by
    have hnat : (325945227 : ℕ)^4843*100000000000000^3819 ≤ 43797963196509^3819*625000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325945227 625000000 43797963196509 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215122263/10000000000 : ℝ)^4843 ≤ (10949487154127/25000000000000 : ℝ)^3819 := by
    have hnat : (5215122263 : ℕ)^4843*25000000000000^3819 ≤ 10949487154127^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215122263 10000000000 10949487154127 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928504961/10000000000 : ℝ), (325945227/625000000 : ℝ), (5215122263/10000000000 : ℝ)] ![(12404088178381/100000000000000 : ℝ), (43797963196509/100000000000000 : ℝ), (10949487154127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928504961/10000000000 : ℝ)|^4843 ≤ (12404088178381/100000000000000 : ℝ)^3819
        have hw : |(-1928504961/10000000000 : ℝ)|=(1928504961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325945227/625000000 : ℝ)|^4843 ≤ (43797963196509/100000000000000 : ℝ)^3819
        have hw : |(325945227/625000000 : ℝ)|=(325945227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215122263/10000000000 : ℝ)|^4843 ≤ (10949487154127/25000000000000 : ℝ)^3819
        have hw : |(5215122263/10000000000 : ℝ)|=(5215122263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387267443/10000000000 : ℝ)*x 0 + (-212371733/1250000000 : ℝ)*x 1 + (1043024521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387267443/10000000000 : ℝ)^4843 ≤ (11409840652519/25000000000000 : ℝ)^3819 := by
    have hnat : (5387267443 : ℕ)^4843*25000000000000^3819 ≤ 11409840652519^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387267443 10000000000 11409840652519 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212371733/1250000000 : ℝ)^4843 ≤ (10562685114369/100000000000000 : ℝ)^3819 := by
    have hnat : (212371733 : ℕ)^4843*100000000000000^3819 ≤ 10562685114369^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212371733 1250000000 10562685114369 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043024521/2000000000 : ℝ)^4843 ≤ (21898976129423/50000000000000 : ℝ)^3819 := by
    have hnat : (1043024521 : ℕ)^4843*50000000000000^3819 ≤ 21898976129423^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043024521 2000000000 21898976129423 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387267443/10000000000 : ℝ), (-212371733/1250000000 : ℝ), (1043024521/2000000000 : ℝ)] ![(11409840652519/25000000000000 : ℝ), (10562685114369/100000000000000 : ℝ), (21898976129423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387267443/10000000000 : ℝ)|^4843 ≤ (11409840652519/25000000000000 : ℝ)^3819
        have hw : |(5387267443/10000000000 : ℝ)|=(5387267443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212371733/1250000000 : ℝ)|^4843 ≤ (10562685114369/100000000000000 : ℝ)^3819
        have hw : |(-212371733/1250000000 : ℝ)|=(212371733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043024521/2000000000 : ℝ)|^4843 ≤ (21898976129423/50000000000000 : ℝ)^3819
        have hw : |(1043024521/2000000000 : ℝ)|=(1043024521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_6 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387267803/10000000000 : ℝ)*x 0 + (2607561087/5000000000 : ℝ)*x 1 + (-1698973957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387267803/10000000000 : ℝ)^4843 ≤ (2852460404853/6250000000000 : ℝ)^3819 := by
    have hnat : (5387267803 : ℕ)^4843*6250000000000^3819 ≤ 2852460404853^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387267803 10000000000 2852460404853 6250000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607561087/5000000000 : ℝ)^4843 ≤ (5474743458581/12500000000000 : ℝ)^3819 := by
    have hnat : (2607561087 : ℕ)^4843*12500000000000^3819 ≤ 5474743458581^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607561087 5000000000 5474743458581 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1698973957/10000000000 : ℝ)^4843 ≤ (10562685847591/100000000000000 : ℝ)^3819 := by
    have hnat : (1698973957 : ℕ)^4843*100000000000000^3819 ≤ 10562685847591^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698973957 10000000000 10562685847591 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387267803/10000000000 : ℝ), (2607561087/5000000000 : ℝ), (-1698973957/10000000000 : ℝ)] ![(2852460404853/6250000000000 : ℝ), (5474743458581/12500000000000 : ℝ), (10562685847591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387267803/10000000000 : ℝ)|^4843 ≤ (2852460404853/6250000000000 : ℝ)^3819
        have hw : |(5387267803/10000000000 : ℝ)|=(5387267803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607561087/5000000000 : ℝ)|^4843 ≤ (5474743458581/12500000000000 : ℝ)^3819
        have hw : |(2607561087/5000000000 : ℝ)|=(2607561087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1698973957/10000000000 : ℝ)|^4843 ≤ (10562685847591/100000000000000 : ℝ)^3819
        have hw : |(-1698973957/10000000000 : ℝ)|=(1698973957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_7 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (244450387/625000000 : ℝ)*x 0 + (2174879949/5000000000 : ℝ)*x 1 + (4349759609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244450387/625000000 : ℝ)^4843 ≤ (30408552824841/100000000000000 : ℝ)^3819 := by
    have hnat : (244450387 : ℕ)^4843*100000000000000^3819 ≤ 30408552824841^3819*625000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244450387 625000000 30408552824841 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174879949/5000000000 : ℝ)^4843 ≤ (8698931261169/25000000000000 : ℝ)^3819 := by
    have hnat : (2174879949 : ℕ)^4843*25000000000000^3819 ≤ 8698931261169^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174879949 5000000000 8698931261169 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4349759609/10000000000 : ℝ)^4843 ≤ (34795722112951/100000000000000 : ℝ)^3819 := by
    have hnat : (4349759609 : ℕ)^4843*100000000000000^3819 ≤ 34795722112951^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349759609 10000000000 34795722112951 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(244450387/625000000 : ℝ), (2174879949/5000000000 : ℝ), (4349759609/10000000000 : ℝ)] ![(30408552824841/100000000000000 : ℝ), (8698931261169/25000000000000 : ℝ), (34795722112951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(244450387/625000000 : ℝ)|^4843 ≤ (30408552824841/100000000000000 : ℝ)^3819
        have hw : |(244450387/625000000 : ℝ)|=(244450387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2174879949/5000000000 : ℝ)|^4843 ≤ (8698931261169/25000000000000 : ℝ)^3819
        have hw : |(2174879949/5000000000 : ℝ)|=(2174879949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4349759609/10000000000 : ℝ)|^4843 ≤ (34795722112951/100000000000000 : ℝ)^3819
        have hw : |(4349759609/10000000000 : ℝ)|=(4349759609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_8 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813339939/10000000000 : ℝ)*x 0 + (2536712747/5000000000 : ℝ)*x 1 + (5442470597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813339939/10000000000 : ℝ)^4843 ≤ (458894671397/4000000000000 : ℝ)^3819 := by
    have hnat : (1813339939 : ℕ)^4843*4000000000000^3819 ≤ 458894671397^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813339939 10000000000 458894671397 4000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536712747/5000000000 : ℝ)^4843 ≤ (8458879277759/20000000000000 : ℝ)^3819 := by
    have hnat : (2536712747 : ℕ)^4843*20000000000000^3819 ≤ 8458879277759^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536712747 5000000000 8458879277759 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442470597/10000000000 : ℝ)^4843 ≤ (46233236822533/100000000000000 : ℝ)^3819 := by
    have hnat : (5442470597 : ℕ)^4843*100000000000000^3819 ≤ 46233236822533^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442470597 10000000000 46233236822533 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813339939/10000000000 : ℝ), (2536712747/5000000000 : ℝ), (5442470597/10000000000 : ℝ)] ![(458894671397/4000000000000 : ℝ), (8458879277759/20000000000000 : ℝ), (46233236822533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813339939/10000000000 : ℝ)|^4843 ≤ (458894671397/4000000000000 : ℝ)^3819
        have hw : |(-1813339939/10000000000 : ℝ)|=(1813339939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536712747/5000000000 : ℝ)|^4843 ≤ (8458879277759/20000000000000 : ℝ)^3819
        have hw : |(2536712747/5000000000 : ℝ)|=(2536712747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442470597/10000000000 : ℝ)|^4843 ≤ (46233236822533/100000000000000 : ℝ)^3819
        have hw : |(5442470597/10000000000 : ℝ)|=(5442470597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_9 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230814871/10000000000 : ℝ)*x 0 + (-400420881/2500000000 : ℝ)*x 1 + (5442471363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230814871/10000000000 : ℝ)^4843 ≤ (10991285996841/25000000000000 : ℝ)^3819 := by
    have hnat : (5230814871 : ℕ)^4843*25000000000000^3819 ≤ 10991285996841^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230814871 10000000000 10991285996841 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400420881/2500000000 : ℝ)^4843 ≤ (9801610930413/100000000000000 : ℝ)^3819 := by
    have hnat : (400420881 : ℕ)^4843*100000000000000^3819 ≤ 9801610930413^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400420881 2500000000 9801610930413 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442471363/10000000000 : ℝ)^4843 ≤ (5779155634299/12500000000000 : ℝ)^3819 := by
    have hnat : (5442471363 : ℕ)^4843*12500000000000^3819 ≤ 5779155634299^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442471363 10000000000 5779155634299 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230814871/10000000000 : ℝ), (-400420881/2500000000 : ℝ), (5442471363/10000000000 : ℝ)] ![(10991285996841/25000000000000 : ℝ), (9801610930413/100000000000000 : ℝ), (5779155634299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230814871/10000000000 : ℝ)|^4843 ≤ (10991285996841/25000000000000 : ℝ)^3819
        have hw : |(5230814871/10000000000 : ℝ)|=(5230814871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400420881/2500000000 : ℝ)|^4843 ≤ (9801610930413/100000000000000 : ℝ)^3819
        have hw : |(-400420881/2500000000 : ℝ)|=(400420881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442471363/10000000000 : ℝ)|^4843 ≤ (5779155634299/12500000000000 : ℝ)^3819
        have hw : |(5442471363/10000000000 : ℝ)|=(5442471363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_10 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230815619/10000000000 : ℝ)*x 0 + (5442471357/10000000000 : ℝ)*x 1 + (-200210313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230815619/10000000000 : ℝ)^4843 ≤ (43965151960067/100000000000000 : ℝ)^3819 := by
    have hnat : (5230815619 : ℕ)^4843*100000000000000^3819 ≤ 43965151960067^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230815619 10000000000 43965151960067 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442471357/10000000000 : ℝ)^4843 ≤ (11558311252439/25000000000000 : ℝ)^3819 := by
    have hnat : (5442471357 : ℕ)^4843*25000000000000^3819 ≤ 11558311252439^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442471357 10000000000 11558311252439 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200210313/1250000000 : ℝ)^4843 ≤ (9801603014779/100000000000000 : ℝ)^3819 := by
    have hnat : (200210313 : ℕ)^4843*100000000000000^3819 ≤ 9801603014779^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200210313 1250000000 9801603014779 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230815619/10000000000 : ℝ), (5442471357/10000000000 : ℝ), (-200210313/1250000000 : ℝ)] ![(43965151960067/100000000000000 : ℝ), (11558311252439/25000000000000 : ℝ), (9801603014779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230815619/10000000000 : ℝ)|^4843 ≤ (43965151960067/100000000000000 : ℝ)^3819
        have hw : |(5230815619/10000000000 : ℝ)|=(5230815619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442471357/10000000000 : ℝ)|^4843 ≤ (11558311252439/25000000000000 : ℝ)^3819
        have hw : |(5442471357/10000000000 : ℝ)|=(5442471357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200210313/1250000000 : ℝ)|^4843 ≤ (9801603014779/100000000000000 : ℝ)^3819
        have hw : |(-200210313/1250000000 : ℝ)|=(200210313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_11 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2277911459/5000000000 : ℝ)*x 0 + (503320729/1250000000 : ℝ)*x 1 + (503320487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2277911459/5000000000 : ℝ)^4843 ≤ (36899232214583/100000000000000 : ℝ)^3819 := by
    have hnat : (2277911459 : ℕ)^4843*100000000000000^3819 ≤ 36899232214583^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277911459 5000000000 36899232214583 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503320729/1250000000 : ℝ)^4843 ≤ (31550393500009/100000000000000 : ℝ)^3819 := by
    have hnat : (503320729 : ℕ)^4843*100000000000000^3819 ≤ 31550393500009^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503320729 1250000000 31550393500009 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503320487/1250000000 : ℝ)^4843 ≤ (31550374262887/100000000000000 : ℝ)^3819 := by
    have hnat : (503320487 : ℕ)^4843*100000000000000^3819 ≤ 31550374262887^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503320487 1250000000 31550374262887 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2277911459/5000000000 : ℝ), (503320729/1250000000 : ℝ), (503320487/1250000000 : ℝ)] ![(36899232214583/100000000000000 : ℝ), (31550393500009/100000000000000 : ℝ), (31550374262887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2277911459/5000000000 : ℝ)|^4843 ≤ (36899232214583/100000000000000 : ℝ)^3819
        have hw : |(2277911459/5000000000 : ℝ)|=(2277911459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503320729/1250000000 : ℝ)|^4843 ≤ (31550393500009/100000000000000 : ℝ)^3819
        have hw : |(503320729/1250000000 : ℝ)|=(503320729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503320487/1250000000 : ℝ)|^4843 ≤ (31550374262887/100000000000000 : ℝ)^3819
        have hw : |(503320487/1250000000 : ℝ)|=(503320487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_12 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-750735079/5000000000 : ℝ)*x 0 + (5548907459/10000000000 : ℝ)*x 1 + (2597634839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (750735079/5000000000 : ℝ)^4843 ≤ (9030538382367/100000000000000 : ℝ)^3819 := by
    have hnat : (750735079 : ℕ)^4843*100000000000000^3819 ≤ 9030538382367^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750735079 5000000000 9030538382367 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5548907459/10000000000 : ℝ)^4843 ≤ (47382837192819/100000000000000 : ℝ)^3819 := by
    have hnat : (5548907459 : ℕ)^4843*100000000000000^3819 ≤ 47382837192819^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548907459 10000000000 47382837192819 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597634839/5000000000 : ℝ)^4843 ≤ (43586624412091/100000000000000 : ℝ)^3819 := by
    have hnat : (2597634839 : ℕ)^4843*100000000000000^3819 ≤ 43586624412091^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597634839 5000000000 43586624412091 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-750735079/5000000000 : ℝ), (5548907459/10000000000 : ℝ), (2597634839/5000000000 : ℝ)] ![(9030538382367/100000000000000 : ℝ), (47382837192819/100000000000000 : ℝ), (43586624412091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-750735079/5000000000 : ℝ)|^4843 ≤ (9030538382367/100000000000000 : ℝ)^3819
        have hw : |(-750735079/5000000000 : ℝ)|=(750735079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5548907459/10000000000 : ℝ)|^4843 ≤ (47382837192819/100000000000000 : ℝ)^3819
        have hw : |(5548907459/10000000000 : ℝ)|=(5548907459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597634839/5000000000 : ℝ)|^4843 ≤ (43586624412091/100000000000000 : ℝ)^3819
        have hw : |(2597634839/5000000000 : ℝ)|=(2597634839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_13 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400937177/10000000000 : ℝ)*x 0 + (-34142791/200000000 : ℝ)*x 1 + (5195269671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400937177/10000000000 : ℝ)^4843 ≤ (22893134981227/50000000000000 : ℝ)^3819 := by
    have hnat : (5400937177 : ℕ)^4843*50000000000000^3819 ≤ 22893134981227^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400937177 10000000000 22893134981227 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34142791/200000000 : ℝ)^4843 ≤ (5313552840817/50000000000000 : ℝ)^3819 := by
    have hnat : (34142791 : ℕ)^4843*50000000000000^3819 ≤ 5313552840817^3819*200000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34142791 200000000 5313552840817 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195269671/10000000000 : ℝ)^4843 ≤ (2724164021101/6250000000000 : ℝ)^3819 := by
    have hnat : (5195269671 : ℕ)^4843*6250000000000^3819 ≤ 2724164021101^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195269671 10000000000 2724164021101 6250000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400937177/10000000000 : ℝ), (-34142791/200000000 : ℝ), (5195269671/10000000000 : ℝ)] ![(22893134981227/50000000000000 : ℝ), (5313552840817/50000000000000 : ℝ), (2724164021101/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400937177/10000000000 : ℝ)|^4843 ≤ (22893134981227/50000000000000 : ℝ)^3819
        have hw : |(5400937177/10000000000 : ℝ)|=(5400937177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34142791/200000000 : ℝ)|^4843 ≤ (5313552840817/50000000000000 : ℝ)^3819
        have hw : |(-34142791/200000000 : ℝ)|=(34142791/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195269671/10000000000 : ℝ)|^4843 ≤ (2724164021101/6250000000000 : ℝ)^3819
        have hw : |(5195269671/10000000000 : ℝ)|=(5195269671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_14 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400937607/10000000000 : ℝ)*x 0 + (519526921/1000000000 : ℝ)*x 1 + (-853569793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400937607/10000000000 : ℝ)^4843 ≤ (22893137292597/50000000000000 : ℝ)^3819 := by
    have hnat : (5400937607 : ℕ)^4843*50000000000000^3819 ≤ 22893137292597^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400937607 10000000000 22893137292597 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519526921/1000000000 : ℝ)^4843 ≤ (21793309716467/50000000000000 : ℝ)^3819 := by
    have hnat : (519526921 : ℕ)^4843*50000000000000^3819 ≤ 21793309716467^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519526921 1000000000 21793309716467 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853569793/5000000000 : ℝ)^4843 ≤ (10627105965827/100000000000000 : ℝ)^3819 := by
    have hnat : (853569793 : ℕ)^4843*100000000000000^3819 ≤ 10627105965827^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853569793 5000000000 10627105965827 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400937607/10000000000 : ℝ), (519526921/1000000000 : ℝ), (-853569793/5000000000 : ℝ)] ![(22893137292597/50000000000000 : ℝ), (21793309716467/50000000000000 : ℝ), (10627105965827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400937607/10000000000 : ℝ)|^4843 ≤ (22893137292597/50000000000000 : ℝ)^3819
        have hw : |(5400937607/10000000000 : ℝ)|=(5400937607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519526921/1000000000 : ℝ)|^4843 ≤ (21793309716467/50000000000000 : ℝ)^3819
        have hw : |(519526921/1000000000 : ℝ)|=(519526921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-853569793/5000000000 : ℝ)|^4843 ≤ (10627105965827/100000000000000 : ℝ)^3819
        have hw : |(-853569793/5000000000 : ℝ)|=(853569793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_box_15 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3853079253/10000000000 : ℝ)*x 0 + (4377926297/10000000000 : ℝ)*x 1 + (1094481339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3853079253/10000000000 : ℝ)^4843 ≤ (29836602951779/100000000000000 : ℝ)^3819 := by
    have hnat : (3853079253 : ℕ)^4843*100000000000000^3819 ≤ 29836602951779^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3853079253 10000000000 29836602951779 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4377926297/10000000000 : ℝ)^4843 ≤ (8770425824887/25000000000000 : ℝ)^3819 := by
    have hnat : (4377926297 : ℕ)^4843*25000000000000^3819 ≤ 8770425824887^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377926297 10000000000 8770425824887 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094481339/2500000000 : ℝ)^4843 ≤ (17540846868577/50000000000000 : ℝ)^3819 := by
    have hnat : (1094481339 : ℕ)^4843*50000000000000^3819 ≤ 17540846868577^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094481339 2500000000 17540846868577 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3853079253/10000000000 : ℝ), (4377926297/10000000000 : ℝ), (1094481339/2500000000 : ℝ)] ![(29836602951779/100000000000000 : ℝ), (8770425824887/25000000000000 : ℝ), (17540846868577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3853079253/10000000000 : ℝ)|^4843 ≤ (29836602951779/100000000000000 : ℝ)^3819
        have hw : |(3853079253/10000000000 : ℝ)|=(3853079253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4377926297/10000000000 : ℝ)|^4843 ≤ (8770425824887/25000000000000 : ℝ)^3819
        have hw : |(4377926297/10000000000 : ℝ)|=(4377926297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094481339/2500000000 : ℝ)|^4843 ≤ (17540846868577/50000000000000 : ℝ)^3819
        have hw : |(1094481339/2500000000 : ℝ)|=(1094481339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2031/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58421/100000 : ℝ) ∧ (80843/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88037/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5283/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5283/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5283/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5283/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5283/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5283/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5283/50000 : ℝ) ^ (4839/1024 : ℝ) ≤ (2440089115235469/100000000000000000000 : ℝ) := by
    have hpowers : (5283/50000 : ℝ)^4839 ≤ (2440089115235469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5283 : ℕ)^4839*100000000000000000000^1024 ≤ 2440089115235469^1024*50000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5283 50000 2440089115235469 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5283/50000 : ℝ)) (X := (2440089115235469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1019/6250 : ℝ) ^ (4839/1024 : ℝ) ≤ (18950836778237221/100000000000000000000 : ℝ) := by
    have hpowers : (1019/6250 : ℝ)^4839 ≤ (18950836778237221/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1019 : ℕ)^4839*100000000000000000000^1024 ≤ 18950836778237221^1024*6250^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1019 6250 18950836778237221 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1019/6250 : ℝ)) (X := (18950836778237221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002440089115235469/50000000000000000000 : ℝ) ≤ (400004130776091/400000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50002440089115235469/50000000000000000000 : ℝ)^1024 ≤ (400004130776091/400000000000000 : ℝ)^4839 := by
      have hnat : (50002440089115235469 : ℕ)^1024*400000000000000^4839 ≤ 400004130776091^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002440089115235469 50000000000000000000 400004130776091 400000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400004130776091/400000000000000 : ℝ)) (X := (50002440089115235469/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002139092589347269/10000000000000000000 : ℝ) ≤ (2000090524742077/2000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (10002139092589347269/10000000000000000000 : ℝ)^1024 ≤ (2000090524742077/2000000000000000 : ℝ)^4839 := by
      have hnat : (10002139092589347269 : ℕ)^1024*2000000000000000^4839 ≤ 2000090524742077^4839*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002139092589347269 10000000000000000000 2000090524742077 2000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000090524742077/2000000000000000 : ℝ)) (X := (10002139092589347269/10000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018950836778237221/50000000000000000000 : ℝ) ≤ (2000160395603699/2000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50018950836778237221/50000000000000000000 : ℝ)^1024 ≤ (2000160395603699/2000000000000000 : ℝ)^4839 := by
      have hnat : (50018950836778237221 : ℕ)^1024*2000000000000000^4839 ≤ 2000160395603699^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018950836778237221 50000000000000000000 2000160395603699 2000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000160395603699/2000000000000000 : ℝ)) (X := (50018950836778237221/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2440089115235469/100000000000000000000 : ℝ) ≤ ((5737321000459127343/5738000000000000000 : ℝ)+2*(34935430811/57380000000000 : ℝ)*(5283/50000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (5737321000459127343/5738000000000000000 : ℝ)+2*(34935430811/57380000000000 : ℝ)*(5283/50000 : ℝ)=(400004130776091/400000000000000 : ℝ) by norm_num, show 1+2*(2440089115235469/100000000000000000000 : ℝ)=(50002440089115235469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18950836778237221/100000000000000000000 : ℝ)+(2440089115235469/100000000000000000000 : ℝ) ≤ ((5737321000459127343/5738000000000000000 : ℝ)+(34935430811/57380000000000 : ℝ)*((1019/6250 : ℝ)+(5283/50000 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (5737321000459127343/5738000000000000000 : ℝ)+(34935430811/57380000000000 : ℝ)*((1019/6250 : ℝ)+(5283/50000 : ℝ))=(2000090524742077/2000000000000000 : ℝ) by norm_num, show 1+(18950836778237221/100000000000000000000 : ℝ)+(2440089115235469/100000000000000000000 : ℝ)=(10002139092589347269/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18950836778237221/100000000000000000000 : ℝ) ≤ ((5737321000459127343/5738000000000000000 : ℝ)+2*(34935430811/57380000000000 : ℝ)*(1019/6250 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (5737321000459127343/5738000000000000000 : ℝ)+2*(34935430811/57380000000000 : ℝ)*(1019/6250 : ℝ)=(2000160395603699/2000000000000000 : ℝ) by norm_num, show 1+2*(18950836778237221/100000000000000000000 : ℝ)=(50018950836778237221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5737321000459127343/5738000000000000000 : ℝ)*(X 1 0+X 2 0)+(34935430811/57380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (5283/50000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (5737321000459127343/5738000000000000000 : ℝ)) (alpha := (34935430811/57380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5737321000459127343/5738000000000000000 : ℝ)*(X 0 1+X 2 1)+(34935430811/57380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (5283/50000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (5737321000459127343/5738000000000000000 : ℝ)) (alpha := (34935430811/57380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5737321000459127343/5738000000000000000 : ℝ)*(X 0 2+X 1 2)+(34935430811/57380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (5283/50000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (5737321000459127343/5738000000000000000 : ℝ)) (alpha := (34935430811/57380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-346956463/2500000000 : ℝ)*X 0 0+(5412781421/10000000000 : ℝ)*X 0 1+(216511257/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251247917/10000000000 : ℝ)*X 1 0+(-1614774713/10000000000 : ℝ)*X 1 1+(5412781203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625623899/5000000000 : ℝ)*X 2 0+(5412781287/10000000000 : ℝ)*X 2 1+(-807387379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1118428783/2500000000 : ℝ)*X 0 0+(2034419311/5000000000 : ℝ)*X 0 1+(2034419259/5000000000 : ℝ)*X 0 2+(1118428783/2500000000 : ℝ)*X 1 0+(2034419311/5000000000 : ℝ)*X 1 1+(2034419259/5000000000 : ℝ)*X 1 2+(1118428783/2500000000 : ℝ)*X 2 0+(2034419311/5000000000 : ℝ)*X 2 1+(2034419259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1928504961/10000000000 : ℝ)*X 0 0+(325945227/625000000 : ℝ)*X 0 1+(5215122263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5387267443/10000000000 : ℝ)*X 1 0+(-212371733/1250000000 : ℝ)*X 1 1+(1043024521/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5387267803/10000000000 : ℝ)*X 2 0+(2607561087/5000000000 : ℝ)*X 2 1+(-1698973957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((244450387/625000000 : ℝ)*X 0 0+(2174879949/5000000000 : ℝ)*X 0 1+(4349759609/10000000000 : ℝ)*X 0 2+(244450387/625000000 : ℝ)*X 1 0+(2174879949/5000000000 : ℝ)*X 1 1+(4349759609/10000000000 : ℝ)*X 1 2+(244450387/625000000 : ℝ)*X 2 0+(2174879949/5000000000 : ℝ)*X 2 1+(4349759609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1813339939/10000000000 : ℝ)*X 0 0+(2536712747/5000000000 : ℝ)*X 0 1+(5442470597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230814871/10000000000 : ℝ)*X 1 0+(-400420881/2500000000 : ℝ)*X 1 1+(5442471363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230815619/10000000000 : ℝ)*X 2 0+(5442471357/10000000000 : ℝ)*X 2 1+(-200210313/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2277911459/5000000000 : ℝ)*X 0 0+(503320729/1250000000 : ℝ)*X 0 1+(503320487/1250000000 : ℝ)*X 0 2+(2277911459/5000000000 : ℝ)*X 1 0+(503320729/1250000000 : ℝ)*X 1 1+(503320487/1250000000 : ℝ)*X 1 2+(2277911459/5000000000 : ℝ)*X 2 0+(503320729/1250000000 : ℝ)*X 2 1+(503320487/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-750735079/5000000000 : ℝ)*X 0 0+(5548907459/10000000000 : ℝ)*X 0 1+(2597634839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5400937177/10000000000 : ℝ)*X 1 0+(-34142791/200000000 : ℝ)*X 1 1+(5195269671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5400937607/10000000000 : ℝ)*X 2 0+(519526921/1000000000 : ℝ)*X 2 1+(-853569793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3853079253/10000000000 : ℝ)*X 0 0+(4377926297/10000000000 : ℝ)*X 0 1+(1094481339/2500000000 : ℝ)*X 0 2+(3853079253/10000000000 : ℝ)*X 1 0+(4377926297/10000000000 : ℝ)*X 1 1+(1094481339/2500000000 : ℝ)*X 1 2+(3853079253/10000000000 : ℝ)*X 2 0+(4377926297/10000000000 : ℝ)*X 2 1+(1094481339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2031/3125 : ℝ) ≤ (-93227790573494280195375659028189/143450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36528803/100000000000000 : ℝ)*(lower2) + (26200463/100000000000000 : ℝ)*(lower3) + (44728013/100000000000000 : ℝ)*(lower5) + (861284360685041/50000000000000 : ℝ)*(major0) + (861284360685041/50000000000000 : ℝ)*(major1) + (861284360685041/50000000000000 : ℝ)*(major2) + (2675662791/50000000000000 : ℝ)*(sp1) + (185096841/2000000000000 : ℝ)*(sp2) + (168283401/100000000000000 : ℝ)*(sp3) + (1244782620223201/50000000000000 : ℝ)*(sp4) + (311196179889073/12500000000000 : ℝ)*(sp5) + (2489565535596117/100000000000000 : ℝ)*(sp6) + (1954451465341/200000000000 : ℝ)*(sp7) + (1909998353/20000000000000 : ℝ)*(sp8) + (977225900953901/100000000000000 : ℝ)*(f.failure) + (2489574790438167/100000000000000 : ℝ)*(f.sum) + (2484163325473/2869000000000000000000000000 : ℝ)*base66 + (1654767560846876063/286900000000000000000000000000000 : ℝ)*base67 + (1015151480661176063/286900000000000000000000000000000 : ℝ)*base69 + (1797981171887076063/286900000000000000000000000000000 : ℝ)*base71 + (5560098425391/1434500000000000000000000000 : ℝ)*base73 + (1701440657119676063/286900000000000000000000000000000 : ℝ)*base75 + (257689301683423937/286900000000000000000000000000000 : ℝ)*base78 + (386551110037723937/286900000000000000000000000000000 : ℝ)*base80 + (4084256479779/2869000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9572477/2500000000000000000000 : ℝ)*base90 + (9572477/2500000000000000000000 : ℝ)*base92 + (9572477/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58421/100000 : ℝ) ≤ (41904155393398566094984546414449/71725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12232133/100000000000000 : ℝ)*(upper2) + (27986333/100000000000000 : ℝ)*(lower3) + (772549/1250000000000 : ℝ)*(lower5) + (452573240412673/25000000000000 : ℝ)*(major0) + (452573240412673/25000000000000 : ℝ)*(major1) + (452573240412673/25000000000000 : ℝ)*(major2) + (1287059060767743/50000000000000 : ℝ)*(sp0) + (1287057650335163/50000000000000 : ℝ)*(sp1) + (2574118159622237/100000000000000 : ℝ)*(sp2) + (1026985317180827/100000000000000 : ℝ)*(sp3) + (100334999/12500000000000 : ℝ)*(sp6) + (1830815951/50000000000000 : ℝ)*(sp9) + (7190283571/100000000000000 : ℝ)*(sp11) + (420383371/50000000000000 : ℝ)*(sp12) + (1026992507464399/100000000000000 : ℝ)*(f.failure) + (643529740575557/25000000000000 : ℝ)*(f.sum) + (3235061995667/1434500000000000000000000000 : ℝ)*base66 + (732689433315817839/143450000000000000000000000000000 : ℝ)*base67 + (1278048609121717839/143450000000000000000000000000000 : ℝ)*base69 + (1390249992173617839/143450000000000000000000000000000 : ℝ)*base71 + (457962951501/358625000000000000000000000 : ℝ)*base74 + (1238986029677617839/143450000000000000000000000000000 : ℝ)*base75 + (192276647046517839/143450000000000000000000000000000 : ℝ)*base77 + (194452489617467839/143450000000000000000000000000000 : ℝ)*base79 + (1676362308973/358625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13933377/2500000000000000000000 : ℝ)*base89 + (13933377/2500000000000000000000 : ℝ)*base91 + (13933377/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80843/100000 : ℝ) ≤ (231945841154163491278583393317971/286900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31395817/25000000000000 : ℝ)*(lower3) + (19275077/5000000000000 : ℝ)*(upper4) + (35226507/20000000000000 : ℝ)*(lower5) + (1910153197853533/100000000000000 : ℝ)*(major0) + (1910153197853533/100000000000000 : ℝ)*(major1) + (955076598926767/50000000000000 : ℝ)*(major2) + (6082009187/50000000000000 : ℝ)*(sp0) + (124371616331/100000000000000 : ℝ)*(sp1) + (213850923017/100000000000000 : ℝ)*(sp2) + (83015570707/100000000000000 : ℝ)*(sp3) + (169356360386601/6250000000000 : ℝ)*(sp8) + (135479477929383/5000000000000 : ℝ)*(sp9) + (1354750039640487/50000000000000 : ℝ)*(sp10) + (541780469060863/50000000000000 : ℝ)*(sp11) + (1083643953692433/100000000000000 : ℝ)*(f.failure) + (2709713930203991/100000000000000 : ℝ)*(f.sum) + (433923499683/302000000000000000000000000 : ℝ)*base65 + (1055767134369652819/573800000000000000000000000000000 : ℝ)*base67 + (1643818801001840081/286900000000000000000000000000000 : ℝ)*base69 + (371470643393347181/573800000000000000000000000000000 : ℝ)*base72 + (268989721663/302000000000000000000000000 : ℝ)*base74 + (1250888860731940081/286900000000000000000000000000000 : ℝ)*base75 + (722385790247447181/573800000000000000000000000000000 : ℝ)*base78 + (901469986129647181/573800000000000000000000000000000 : ℝ)*base80 + (9276727519597/2869000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8883359/2500000000000000000000 : ℝ)*base89 + (8883359/2500000000000000000000 : ℝ)*base91 + (16116641/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88037/100000 : ℝ) ≤ (-2525696796831061369927885407/2869000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141463047/100000000000000 : ℝ)*(upper1) + (17510577/100000000000000 : ℝ)*(lower2) + (62121417/50000000000000 : ℝ)*(upper3) + (106715137/50000000000000 : ℝ)*(upper5) + (1953251612201473/100000000000000 : ℝ)*(major0) + (1953251612201473/100000000000000 : ℝ)*(major1) + (1953251612201473/100000000000000 : ℝ)*(major2) + (959622267/12500000000000 : ℝ)*(sp4) + (30456279/40000000000 : ℝ)*(sp6) + (17511086923/50000000000000 : ℝ)*(sp7) + (706936557146727/25000000000000 : ℝ)*(sp12) + (706938476391261/25000000000000 : ℝ)*(sp13) + (353459720608443/12500000000000 : ℝ)*(sp14) + (55402948943131/5000000000000 : ℝ)*(sp15) + (554047000518233/50000000000000 : ℝ)*(f.failure) + (706938476391261/25000000000000 : ℝ)*(f.sum) + (2724294829779/573800000000000000000000000 : ℝ)*base65 + (3204969568674123761/573800000000000000000000000000000 : ℝ)*base68 + (2604771184719323761/573800000000000000000000000000000 : ℝ)*base70 + (675458792835476239/573800000000000000000000000000000 : ℝ)*base71 + (306954269509/2869000000000000000000000000 : ℝ)*base74 + (2173282570139076239/573800000000000000000000000000000 : ℝ)*base75 + (1740042028539476239/573800000000000000000000000000000 : ℝ)*base77 + (287786731154923761/573800000000000000000000000000000 : ℝ)*base80 + (9826586113753/2869000000000000000000000000 : ℝ)*base81 + (12383241/1250000000000000000000 : ℝ)*base90 + (12383241/1250000000000000000000 : ℝ)*base92 + (12383241/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1631_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2031/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58421/100000 : ℝ) else (80843/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88037/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1631_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1631_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2031/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58421/100000 : ℝ) else (80843/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88037/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1631_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2031/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58421/100000 : ℝ) else (80843/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88037/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1631_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
