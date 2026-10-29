-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:02.466354+00:00
-- url     : https://prove2.me/submissions/729b233b-a0a1-478c-bea8-c8dd2d61adc7

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
theorem support_rectangle_w1352_s3_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1016852119/5000000000 : ℝ)*x 0 + (5425909811/10000000000 : ℝ)*x 1 + (163508801/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016852119/5000000000 : ℝ)^539 ≤ (12384088325623/100000000000000 : ℝ)^411 := by
    have hnat : (1016852119 : ℕ)^539*100000000000000^411 ≤ 12384088325623^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016852119 5000000000 12384088325623 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425909811/10000000000 : ℝ)^539 ≤ (22425797753767/50000000000000 : ℝ)^411 := by
    have hnat : (5425909811 : ℕ)^539*50000000000000^411 ≤ 22425797753767^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425909811 10000000000 22425797753767 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163508801/312500000 : ℝ)^539 ≤ (42764316153129/100000000000000 : ℝ)^411 := by
    have hnat : (163508801 : ℕ)^539*100000000000000^411 ≤ 42764316153129^411*312500000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163508801 312500000 42764316153129 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1016852119/5000000000 : ℝ), (5425909811/10000000000 : ℝ), (163508801/312500000 : ℝ)] ![(12384088325623/100000000000000 : ℝ), (22425797753767/50000000000000 : ℝ), (42764316153129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1016852119/5000000000 : ℝ)|^539 ≤ (12384088325623/100000000000000 : ℝ)^411
        have hw : |(-1016852119/5000000000 : ℝ)|=(1016852119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425909811/10000000000 : ℝ)|^539 ≤ (22425797753767/50000000000000 : ℝ)^411
        have hw : |(5425909811/10000000000 : ℝ)|=(5425909811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163508801/312500000 : ℝ)|^539 ≤ (42764316153129/100000000000000 : ℝ)^411
        have hw : |(163508801/312500000 : ℝ)|=(163508801/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5352326807/10000000000 : ℝ)*x 0 + (-2132637669/10000000000 : ℝ)*x 1 + (1308070443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352326807/10000000000 : ℝ)^539 ≤ (22027801652307/50000000000000 : ℝ)^411 := by
    have hnat : (5352326807 : ℕ)^539*50000000000000^411 ≤ 22027801652307^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352326807 10000000000 22027801652307 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132637669/10000000000 : ℝ)^539 ≤ (13180079031401/100000000000000 : ℝ)^411 := by
    have hnat : (2132637669 : ℕ)^539*100000000000000^411 ≤ 13180079031401^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132637669 10000000000 13180079031401 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308070443/2500000000 : ℝ)^539 ≤ (42764317653731/100000000000000 : ℝ)^411 := by
    have hnat : (1308070443 : ℕ)^539*100000000000000^411 ≤ 42764317653731^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308070443 2500000000 42764317653731 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352326807/10000000000 : ℝ), (-2132637669/10000000000 : ℝ), (1308070443/2500000000 : ℝ)] ![(22027801652307/50000000000000 : ℝ), (13180079031401/100000000000000 : ℝ), (42764317653731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352326807/10000000000 : ℝ)|^539 ≤ (22027801652307/50000000000000 : ℝ)^411
        have hw : |(5352326807/10000000000 : ℝ)|=(5352326807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132637669/10000000000 : ℝ)|^539 ≤ (13180079031401/100000000000000 : ℝ)^411
        have hw : |(-2132637669/10000000000 : ℝ)|=(2132637669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308070443/2500000000 : ℝ)|^539 ≤ (42764317653731/100000000000000 : ℝ)^411
        have hw : |(1308070443/2500000000 : ℝ)|=(1308070443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (334520403/625000000 : ℝ)*x 0 + (2616140731/5000000000 : ℝ)*x 1 + (-1066319279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334520403/625000000 : ℝ)^539 ≤ (22027799714681/50000000000000 : ℝ)^411 := by
    have hnat : (334520403 : ℕ)^539*50000000000000^411 ≤ 22027799714681^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334520403 625000000 22027799714681 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616140731/5000000000 : ℝ)^539 ≤ (4276431433097/10000000000000 : ℝ)^411 := by
    have hnat : (2616140731 : ℕ)^539*10000000000000^411 ≤ 4276431433097^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616140731 5000000000 4276431433097 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066319279/5000000000 : ℝ)^539 ≤ (13180086236661/100000000000000 : ℝ)^411 := by
    have hnat : (1066319279 : ℕ)^539*100000000000000^411 ≤ 13180086236661^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066319279 5000000000 13180086236661 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334520403/625000000 : ℝ), (2616140731/5000000000 : ℝ), (-1066319279/5000000000 : ℝ)] ![(22027799714681/50000000000000 : ℝ), (4276431433097/10000000000000 : ℝ), (13180086236661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334520403/625000000 : ℝ)|^539 ≤ (22027799714681/50000000000000 : ℝ)^411
        have hw : |(334520403/625000000 : ℝ)|=(334520403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616140731/5000000000 : ℝ)|^539 ≤ (4276431433097/10000000000000 : ℝ)^411
        have hw : |(2616140731/5000000000 : ℝ)|=(2616140731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066319279/5000000000 : ℝ)|^539 ≤ (13180086236661/100000000000000 : ℝ)^411
        have hw : |(-1066319279/5000000000 : ℝ)|=(1066319279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1080751473/2500000000 : ℝ)*x 0 + (4123914529/10000000000 : ℝ)*x 1 + (90620187/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080751473/2500000000 : ℝ)^539 ≤ (33293280984727/100000000000000 : ℝ)^411 := by
    have hnat : (1080751473 : ℕ)^539*100000000000000^411 ≤ 33293280984727^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080751473 2500000000 33293280984727 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4123914529/10000000000 : ℝ)^539 ≤ (489016421237/1562500000000 : ℝ)^411 := by
    have hnat : (4123914529 : ℕ)^539*1562500000000^411 ≤ 489016421237^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123914529 10000000000 489016421237 1562500000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90620187/200000000 : ℝ)^539 ≤ (8852417010969/25000000000000 : ℝ)^411 := by
    have hnat : (90620187 : ℕ)^539*25000000000000^411 ≤ 8852417010969^411*200000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90620187 200000000 8852417010969 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080751473/2500000000 : ℝ), (4123914529/10000000000 : ℝ), (90620187/200000000 : ℝ)] ![(33293280984727/100000000000000 : ℝ), (489016421237/1562500000000 : ℝ), (8852417010969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080751473/2500000000 : ℝ)|^539 ≤ (33293280984727/100000000000000 : ℝ)^411
        have hw : |(1080751473/2500000000 : ℝ)|=(1080751473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4123914529/10000000000 : ℝ)|^539 ≤ (489016421237/1562500000000 : ℝ)^411
        have hw : |(4123914529/10000000000 : ℝ)|=(4123914529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90620187/200000000 : ℝ)|^539 ≤ (8852417010969/25000000000000 : ℝ)^411
        have hw : |(90620187/200000000 : ℝ)|=(90620187/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2033722899/10000000000 : ℝ)*x 0 + (2616541931/5000000000 : ℝ)*x 1 + (678137853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033722899/10000000000 : ℝ)^539 ≤ (3096059337621/25000000000000 : ℝ)^411 := by
    have hnat : (2033722899 : ℕ)^539*25000000000000^411 ≤ 3096059337621^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033722899 10000000000 3096059337621 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616541931/5000000000 : ℝ)^539 ≤ (42772915127009/100000000000000 : ℝ)^411 := by
    have hnat : (2616541931 : ℕ)^539*100000000000000^411 ≤ 42772915127009^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616541931 5000000000 42772915127009 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678137853/1250000000 : ℝ)^539 ≤ (8968569501607/20000000000000 : ℝ)^411 := by
    have hnat : (678137853 : ℕ)^539*20000000000000^411 ≤ 8968569501607^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678137853 1250000000 8968569501607 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2033722899/10000000000 : ℝ), (2616541931/5000000000 : ℝ), (678137853/1250000000 : ℝ)] ![(3096059337621/25000000000000 : ℝ), (42772915127009/100000000000000 : ℝ), (8968569501607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2033722899/10000000000 : ℝ)|^539 ≤ (3096059337621/25000000000000 : ℝ)^411
        have hw : |(-2033722899/10000000000 : ℝ)|=(2033722899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616541931/5000000000 : ℝ)|^539 ≤ (42772915127009/100000000000000 : ℝ)^411
        have hw : |(2616541931/5000000000 : ℝ)|=(2616541931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678137853/1250000000 : ℝ)|^539 ≤ (8968569501607/20000000000000 : ℝ)^411
        have hw : |(678137853/1250000000 : ℝ)|=(678137853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2651197181/5000000000 : ℝ)*x 0 + (-15154817/78125000 : ℝ)*x 1 + (2712551579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651197181/5000000000 : ℝ)^539 ≤ (10879347141821/25000000000000 : ℝ)^411 := by
    have hnat : (2651197181 : ℕ)^539*25000000000000^411 ≤ 10879347141821^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651197181 5000000000 10879347141821 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15154817/78125000 : ℝ)^539 ≤ (727485018243/6250000000000 : ℝ)^411 := by
    have hnat : (15154817 : ℕ)^539*6250000000000^411 ≤ 727485018243^411*78125000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15154817 78125000 727485018243 6250000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712551579/5000000000 : ℝ)^539 ≤ (44842851128619/100000000000000 : ℝ)^411 := by
    have hnat : (2712551579 : ℕ)^539*100000000000000^411 ≤ 44842851128619^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712551579 5000000000 44842851128619 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651197181/5000000000 : ℝ), (-15154817/78125000 : ℝ), (2712551579/5000000000 : ℝ)] ![(10879347141821/25000000000000 : ℝ), (727485018243/6250000000000 : ℝ), (44842851128619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651197181/5000000000 : ℝ)|^539 ≤ (10879347141821/25000000000000 : ℝ)^411
        have hw : |(2651197181/5000000000 : ℝ)|=(2651197181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15154817/78125000 : ℝ)|^539 ≤ (727485018243/6250000000000 : ℝ)^411
        have hw : |(-15154817/78125000 : ℝ)|=(15154817/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712551579/5000000000 : ℝ)|^539 ≤ (44842851128619/100000000000000 : ℝ)^411
        have hw : |(2712551579/5000000000 : ℝ)|=(2712551579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5302395153/10000000000 : ℝ)*x 0 + (678137829/1250000000 : ℝ)*x 1 + (-969908109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302395153/10000000000 : ℝ)^539 ≤ (5439674635113/12500000000000 : ℝ)^411 := by
    have hnat : (5302395153 : ℕ)^539*12500000000000^411 ≤ 5439674635113^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302395153 10000000000 5439674635113 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678137829/1250000000 : ℝ)^539 ≤ (22421422713371/50000000000000 : ℝ)^411 := by
    have hnat : (678137829 : ℕ)^539*50000000000000^411 ≤ 22421422713371^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678137829 1250000000 22421422713371 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969908109/5000000000 : ℝ)^539 ≤ (11639757474717/100000000000000 : ℝ)^411 := by
    have hnat : (969908109 : ℕ)^539*100000000000000^411 ≤ 11639757474717^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969908109 5000000000 11639757474717 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302395153/10000000000 : ℝ), (678137829/1250000000 : ℝ), (-969908109/5000000000 : ℝ)] ![(5439674635113/12500000000000 : ℝ), (22421422713371/50000000000000 : ℝ), (11639757474717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302395153/10000000000 : ℝ)|^539 ≤ (5439674635113/12500000000000 : ℝ)^411
        have hw : |(5302395153/10000000000 : ℝ)|=(5302395153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678137829/1250000000 : ℝ)|^539 ≤ (22421422713371/50000000000000 : ℝ)^411
        have hw : |(678137829/1250000000 : ℝ)|=(678137829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969908109/5000000000 : ℝ)|^539 ≤ (11639757474717/100000000000000 : ℝ)^411
        have hw : |(-969908109/5000000000 : ℝ)|=(969908109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s3_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4323045891/10000000000 : ℝ)*x 0 + (1132330611/2500000000 : ℝ)*x 1 + (165024433/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323045891/10000000000 : ℝ)^539 ≤ (33293684971803/100000000000000 : ℝ)^411 := by
    have hnat : (4323045891 : ℕ)^539*100000000000000^411 ≤ 33293684971803^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323045891 10000000000 33293684971803 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132330611/2500000000 : ℝ)^539 ≤ (35392380251323/100000000000000 : ℝ)^411 := by
    have hnat : (1132330611 : ℕ)^539*100000000000000^411 ≤ 35392380251323^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132330611 2500000000 35392380251323 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165024433/400000000 : ℝ)^539 ≤ (3914241844689/12500000000000 : ℝ)^411 := by
    have hnat : (165024433 : ℕ)^539*12500000000000^411 ≤ 3914241844689^411*400000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165024433 400000000 3914241844689 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323045891/10000000000 : ℝ), (1132330611/2500000000 : ℝ), (165024433/400000000 : ℝ)] ![(33293684971803/100000000000000 : ℝ), (35392380251323/100000000000000 : ℝ), (3914241844689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323045891/10000000000 : ℝ)|^539 ≤ (33293684971803/100000000000000 : ℝ)^411
        have hw : |(4323045891/10000000000 : ℝ)|=(4323045891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132330611/2500000000 : ℝ)|^539 ≤ (35392380251323/100000000000000 : ℝ)^411
        have hw : |(1132330611/2500000000 : ℝ)|=(1132330611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165024433/400000000 : ℝ)|^539 ≤ (3914241844689/12500000000000 : ℝ)^411
        have hw : |(165024433/400000000 : ℝ)|=(165024433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5451/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3/20 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3213/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2479/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3213/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2479/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3213/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2479/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3213/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2479/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3213/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2479/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3213/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2479/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2479/25000 : ℝ) ^ (4311/1024 : ℝ) ≤ (1190271246560329/20000000000000000000 : ℝ) := by
    have hpowers : (2479/25000 : ℝ)^4311 ≤ (1190271246560329/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2479 : ℕ)^4311*20000000000000000000^1024 ≤ 1190271246560329^1024*25000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2479 25000 1190271246560329 20000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2479/25000 : ℝ)) (X := (1190271246560329/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3213/20000 : ℝ) ^ (4311/1024 : ℝ) ≤ (45372101307512809/100000000000000000000 : ℝ) := by
    have hpowers : (3213/20000 : ℝ)^4311 ≤ (45372101307512809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3213 : ℕ)^4311*100000000000000000000^1024 ≤ 45372101307512809^1024*20000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3213 20000 45372101307512809 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3213/20000 : ℝ)) (X := (45372101307512809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001190271246560329/10000000000000000000 : ℝ) ≤ (10000282714556463/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (10001190271246560329/10000000000000000000 : ℝ)^1024 ≤ (10000282714556463/10000000000000000 : ℝ)^4311 := by
      have hnat : (10001190271246560329 : ℕ)^1024*10000000000000000^4311 ≤ 10000282714556463^4311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001190271246560329 10000000000000000000 10000282714556463 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282714556463/10000000000000000 : ℝ)) (X := (10001190271246560329/10000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025661728770157227/50000000000000000000 : ℝ) ≤ (625076178584631/625000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50025661728770157227/50000000000000000000 : ℝ)^1024 ≤ (625076178584631/625000000000000 : ℝ)^4311 := by
      have hnat : (50025661728770157227 : ℕ)^1024*625000000000000^4311 ≤ 625076178584631^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025661728770157227 50000000000000000000 625076178584631 625000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625076178584631/625000000000000 : ℝ)) (X := (50025661728770157227/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045372101307512809/50000000000000000000 : ℝ) ≤ (10002155000151729/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50045372101307512809/50000000000000000000 : ℝ)^1024 ≤ (10002155000151729/10000000000000000 : ℝ)^4311 := by
      have hnat : (50045372101307512809 : ℕ)^1024*10000000000000000^4311 ≤ 10002155000151729^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045372101307512809 50000000000000000000 10002155000151729 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002155000151729/10000000000000000 : ℝ)) (X := (50045372101307512809/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1190271246560329/20000000000000000000 : ℝ) ≤ ((61473172827845033331/61490000000000000000 : ℝ)+2*(936142797633/614900000000000 : ℝ)*(2479/25000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (61473172827845033331/61490000000000000000 : ℝ)+2*(936142797633/614900000000000 : ℝ)*(2479/25000 : ℝ)=(10000282714556463/10000000000000000 : ℝ) by norm_num, show 1+2*(1190271246560329/20000000000000000000 : ℝ)=(10001190271246560329/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45372101307512809/100000000000000000000 : ℝ)+(1190271246560329/20000000000000000000 : ℝ) ≤ ((61473172827845033331/61490000000000000000 : ℝ)+(936142797633/614900000000000 : ℝ)*((3213/20000 : ℝ)+(2479/25000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (61473172827845033331/61490000000000000000 : ℝ)+(936142797633/614900000000000 : ℝ)*((3213/20000 : ℝ)+(2479/25000 : ℝ))=(625076178584631/625000000000000 : ℝ) by norm_num, show 1+(45372101307512809/100000000000000000000 : ℝ)+(1190271246560329/20000000000000000000 : ℝ)=(50025661728770157227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45372101307512809/100000000000000000000 : ℝ) ≤ ((61473172827845033331/61490000000000000000 : ℝ)+2*(936142797633/614900000000000 : ℝ)*(3213/20000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (61473172827845033331/61490000000000000000 : ℝ)+2*(936142797633/614900000000000 : ℝ)*(3213/20000 : ℝ)=(10002155000151729/10000000000000000 : ℝ) by norm_num, show 1+2*(45372101307512809/100000000000000000000 : ℝ)=(50045372101307512809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61473172827845033331/61490000000000000000 : ℝ)*(X 1 0+X 2 0)+(936142797633/614900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2479/25000 : ℝ)) (hi := (3213/20000 : ℝ)) (c := (61473172827845033331/61490000000000000000 : ℝ)) (alpha := (936142797633/614900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61473172827845033331/61490000000000000000 : ℝ)*(X 0 1+X 2 1)+(936142797633/614900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2479/25000 : ℝ)) (hi := (3213/20000 : ℝ)) (c := (61473172827845033331/61490000000000000000 : ℝ)) (alpha := (936142797633/614900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61473172827845033331/61490000000000000000 : ℝ)*(X 0 2+X 1 2)+(936142797633/614900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2479/25000 : ℝ)) (hi := (3213/20000 : ℝ)) (c := (61473172827845033331/61490000000000000000 : ℝ)) (alpha := (936142797633/614900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1016852119/5000000000 : ℝ)*X 0 0+(5425909811/10000000000 : ℝ)*X 0 1+(163508801/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352326807/10000000000 : ℝ)*X 1 0+(-2132637669/10000000000 : ℝ)*X 1 1+(1308070443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334520403/625000000 : ℝ)*X 2 0+(2616140731/5000000000 : ℝ)*X 2 1+(-1066319279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080751473/2500000000 : ℝ)*X 0 0+(4123914529/10000000000 : ℝ)*X 0 1+(90620187/200000000 : ℝ)*X 0 2+(1080751473/2500000000 : ℝ)*X 1 0+(4123914529/10000000000 : ℝ)*X 1 1+(90620187/200000000 : ℝ)*X 1 2+(1080751473/2500000000 : ℝ)*X 2 0+(4123914529/10000000000 : ℝ)*X 2 1+(90620187/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2033722899/10000000000 : ℝ)*X 0 0+(2616541931/5000000000 : ℝ)*X 0 1+(678137853/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651197181/5000000000 : ℝ)*X 1 0+(-15154817/78125000 : ℝ)*X 1 1+(2712551579/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302395153/10000000000 : ℝ)*X 2 0+(678137829/1250000000 : ℝ)*X 2 1+(-969908109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323045891/10000000000 : ℝ)*X 0 0+(1132330611/2500000000 : ℝ)*X 0 1+(165024433/400000000 : ℝ)*X 0 2+(4323045891/10000000000 : ℝ)*X 1 0+(1132330611/2500000000 : ℝ)*X 1 1+(165024433/400000000 : ℝ)*X 1 2+(4323045891/10000000000 : ℝ)*X 2 0+(1132330611/2500000000 : ℝ)*X 2 1+(165024433/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18859256897491326810556467/1625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (965832387/50000000000000 : ℝ)*(base19) + (1562913871/100000000000000 : ℝ)*(base23) + (147287553/25000000000000 : ℝ)*(upper3) + (117561/312500000000 : ℝ)*(lower4) + (1905266137308413/50000000000000 : ℝ)*(major0) + (1905266137308413/50000000000000 : ℝ)*(major1) + (1905266137308413/50000000000000 : ℝ)*(major2) + (5164581294244081/100000000000000 : ℝ)*(sp0) + (258230016036489/5000000000000 : ℝ)*(sp1) + (322786922516187/6250000000000 : ℝ)*(sp2) + (2456442978369889/100000000000000 : ℝ)*(sp3) + (20958150473/100000000000000 : ℝ)*(sp4) + (9929221691/100000000000000 : ℝ)*(sp6) + (18931612653/100000000000000 : ℝ)*(sp7) + (1228230954991271/50000000000000 : ℝ)*(f.failure) + (2582301126197277/50000000000000 : ℝ)*(f.sum) + (1504176782899/349375000000000000000000000 : ℝ)*base66 + (325778605210873973/279500000000000000000000000000000 : ℝ)*base67 + (2105994427614626027/279500000000000000000000000000000 : ℝ)*base70 + (255397531051373973/279500000000000000000000000000000 : ℝ)*base71 + (11582497156357/2795000000000000000000000000 : ℝ)*base74 + (17838249013373973/279500000000000000000000000000000 : ℝ)*base75 + (720744996770873973/279500000000000000000000000000000 : ℝ)*base77 + (1677034883290373973/279500000000000000000000000000000 : ℝ)*base79 + (22997876147217/2795000000000000000000000000 : ℝ)*base82 + (38157361/5000000000000000000000 : ℝ)*base89 + (38157361/5000000000000000000000 : ℝ)*base91 + (38157361/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50466282807408198738395403/17875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168519629/25000000000000 : ℝ)*(base19) + (1951830767/100000000000000 : ℝ)*(base23) + (210388673/100000000000000 : ℝ)*(upper3) + (167212841/100000000000000 : ℝ)*(lower4) + (173008893/100000000000000 : ℝ)*(upper5) + (1921209672063953/50000000000000 : ℝ)*(major0) + (1921209672063953/50000000000000 : ℝ)*(major1) + (1921209672063953/50000000000000 : ℝ)*(major2) + (14103026093/100000000000000 : ℝ)*(sp1) + (16901543431/50000000000000 : ℝ)*(sp2) + (2542881184439/48828125000 : ℝ)*(sp4) + (2603902944313231/50000000000000 : ℝ)*(sp5) + (2603892455406721/50000000000000 : ℝ)*(sp6) + (1238508964207557/50000000000000 : ℝ)*(sp7) + (1238508964207557/50000000000000 : ℝ)*(f.failure) + (2542881184439/48828125000 : ℝ)*(f.sum) + (52242953856557/7686250000000000000000000000 : ℝ)*base65 + (167353368044225687/279500000000000000000000000000000 : ℝ)*base68 + (2220330534635225687/279500000000000000000000000000000 : ℝ)*base70 + (1842950329130274313/279500000000000000000000000000000 : ℝ)*base71 + (132425729407683/30745000000000000000000000000 : ℝ)*base73 + (3056341996323225687/279500000000000000000000000000000 : ℝ)*base76 + (464263617576225687/279500000000000000000000000000000 : ℝ)*base78 + (2000418209002225687/279500000000000000000000000000000 : ℝ)*base80 + (4018244171343/1921562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (45131587/5000000000000000000000 : ℝ)*base89 + (45131587/5000000000000000000000 : ℝ)*base91 + (45131587/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1352_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5451/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3/20 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1352_s4_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-508771827/2500000000 : ℝ)*x 0 + (5414576063/10000000000 : ℝ)*x 1 + (5242706843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508771827/2500000000 : ℝ)^539 ≤ (6197567268299/50000000000000 : ℝ)^411 := by
    have hnat : (508771827 : ℕ)^539*50000000000000^411 ≤ 6197567268299^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508771827 2500000000 6197567268299 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414576063/10000000000 : ℝ)^539 ≤ (11182192789743/25000000000000 : ℝ)^411 := by
    have hnat : (5414576063 : ℕ)^539*25000000000000^411 ≤ 11182192789743^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414576063 10000000000 11182192789743 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242706843/10000000000 : ℝ)^539 ≤ (42876094293463/100000000000000 : ℝ)^411 := by
    have hnat : (5242706843 : ℕ)^539*100000000000000^411 ≤ 42876094293463^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242706843 10000000000 42876094293463 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-508771827/2500000000 : ℝ), (5414576063/10000000000 : ℝ), (5242706843/10000000000 : ℝ)] ![(6197567268299/50000000000000 : ℝ), (11182192789743/25000000000000 : ℝ), (42876094293463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-508771827/2500000000 : ℝ)|^539 ≤ (6197567268299/50000000000000 : ℝ)^411
        have hw : |(-508771827/2500000000 : ℝ)|=(508771827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414576063/10000000000 : ℝ)|^539 ≤ (11182192789743/25000000000000 : ℝ)^411
        have hw : |(5414576063/10000000000 : ℝ)|=(5414576063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242706843/10000000000 : ℝ)|^539 ≤ (42876094293463/100000000000000 : ℝ)^411
        have hw : |(5242706843/10000000000 : ℝ)|=(5242706843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (213977343/400000000 : ℝ)*x 0 + (-212269229/1000000000 : ℝ)*x 1 + (2621353407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213977343/400000000 : ℝ)^539 ≤ (44024374729377/100000000000000 : ℝ)^411 := by
    have hnat : (213977343 : ℕ)^539*100000000000000^411 ≤ 44024374729377^411*400000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213977343 400000000 44024374729377 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212269229/1000000000 : ℝ)^539 ≤ (3274882821341/25000000000000 : ℝ)^411 := by
    have hnat : (212269229 : ℕ)^539*25000000000000^411 ≤ 3274882821341^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212269229 1000000000 3274882821341 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621353407/5000000000 : ℝ)^539 ≤ (42876093982431/100000000000000 : ℝ)^411 := by
    have hnat : (2621353407 : ℕ)^539*100000000000000^411 ≤ 42876093982431^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621353407 5000000000 42876093982431 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213977343/400000000 : ℝ), (-212269229/1000000000 : ℝ), (2621353407/5000000000 : ℝ)] ![(44024374729377/100000000000000 : ℝ), (3274882821341/25000000000000 : ℝ), (42876093982431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213977343/400000000 : ℝ)|^539 ≤ (44024374729377/100000000000000 : ℝ)^411
        have hw : |(213977343/400000000 : ℝ)|=(213977343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212269229/1000000000 : ℝ)|^539 ≤ (3274882821341/25000000000000 : ℝ)^411
        have hw : |(-212269229/1000000000 : ℝ)|=(212269229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621353407/5000000000 : ℝ)|^539 ≤ (42876093982431/100000000000000 : ℝ)^411
        have hw : |(2621353407/5000000000 : ℝ)|=(2621353407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337358393/2500000000 : ℝ)*x 0 + (1310676709/2500000000 : ℝ)*x 1 + (-2122692263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337358393/2500000000 : ℝ)^539 ≤ (44024374696999/100000000000000 : ℝ)^411 := by
    have hnat : (1337358393 : ℕ)^539*100000000000000^411 ≤ 44024374696999^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337358393 2500000000 44024374696999 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310676709/2500000000 : ℝ)^539 ≤ (21438047109193/50000000000000 : ℝ)^411 := by
    have hnat : (1310676709 : ℕ)^539*50000000000000^411 ≤ 21438047109193^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310676709 2500000000 21438047109193 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122692263/10000000000 : ℝ)^539 ≤ (261990621337/2000000000000 : ℝ)^411 := by
    have hnat : (2122692263 : ℕ)^539*2000000000000^411 ≤ 261990621337^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122692263 10000000000 261990621337 2000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337358393/2500000000 : ℝ), (1310676709/2500000000 : ℝ), (-2122692263/10000000000 : ℝ)] ![(44024374696999/100000000000000 : ℝ), (21438047109193/50000000000000 : ℝ), (261990621337/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337358393/2500000000 : ℝ)|^539 ≤ (44024374696999/100000000000000 : ℝ)^411
        have hw : |(1337358393/2500000000 : ℝ)|=(1337358393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310676709/2500000000 : ℝ)|^539 ≤ (21438047109193/50000000000000 : ℝ)^411
        have hw : |(1310676709/2500000000 : ℝ)|=(1310676709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122692263/10000000000 : ℝ)|^539 ≤ (261990621337/2000000000000 : ℝ)^411
        have hw : |(-2122692263/10000000000 : ℝ)|=(2122692263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4323846307/10000000000 : ℝ)*x 0 + (1036671121/2500000000 : ℝ)*x 1 + (1127007979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323846307/10000000000 : ℝ)^539 ≤ (33301769361601/100000000000000 : ℝ)^411 := by
    have hnat : (4323846307 : ℕ)^539*100000000000000^411 ≤ 33301769361601^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323846307 10000000000 33301769361601 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036671121/2500000000 : ℝ)^539 ≤ (31523867981891/100000000000000 : ℝ)^411 := by
    have hnat : (1036671121 : ℕ)^539*100000000000000^411 ≤ 31523867981891^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036671121 2500000000 31523867981891 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127007979/2500000000 : ℝ)^539 ≤ (2198397665603/6250000000000 : ℝ)^411 := by
    have hnat : (1127007979 : ℕ)^539*6250000000000^411 ≤ 2198397665603^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127007979 2500000000 2198397665603 6250000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323846307/10000000000 : ℝ), (1036671121/2500000000 : ℝ), (1127007979/2500000000 : ℝ)] ![(33301769361601/100000000000000 : ℝ), (31523867981891/100000000000000 : ℝ), (2198397665603/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323846307/10000000000 : ℝ)|^539 ≤ (33301769361601/100000000000000 : ℝ)^411
        have hw : |(4323846307/10000000000 : ℝ)|=(4323846307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036671121/2500000000 : ℝ)|^539 ≤ (31523867981891/100000000000000 : ℝ)^411
        have hw : |(1036671121/2500000000 : ℝ)|=(1036671121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127007979/2500000000 : ℝ)|^539 ≤ (2198397665603/6250000000000 : ℝ)^411
        have hw : |(1127007979/2500000000 : ℝ)|=(1127007979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-407020087/2000000000 : ℝ)*x 0 + (5243339509/10000000000 : ℝ)*x 1 + (2706970009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407020087/2000000000 : ℝ)^539 ≤ (12395239389647/100000000000000 : ℝ)^411 := by
    have hnat : (407020087 : ℕ)^539*100000000000000^411 ≤ 12395239389647^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407020087 2000000000 12395239389647 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243339509/10000000000 : ℝ)^539 ≤ (428828799089/1000000000000 : ℝ)^411 := by
    have hnat : (5243339509 : ℕ)^539*1000000000000^411 ≤ 428828799089^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243339509 10000000000 428828799089 1000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706970009/5000000000 : ℝ)^539 ≤ (44721880680983/100000000000000 : ℝ)^411 := by
    have hnat : (2706970009 : ℕ)^539*100000000000000^411 ≤ 44721880680983^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706970009 5000000000 44721880680983 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407020087/2000000000 : ℝ), (5243339509/10000000000 : ℝ), (2706970009/5000000000 : ℝ)] ![(12395239389647/100000000000000 : ℝ), (428828799089/1000000000000 : ℝ), (44721880680983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407020087/2000000000 : ℝ)|^539 ≤ (12395239389647/100000000000000 : ℝ)^411
        have hw : |(-407020087/2000000000 : ℝ)|=(407020087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243339509/10000000000 : ℝ)|^539 ≤ (428828799089/1000000000000 : ℝ)^411
        have hw : |(5243339509/10000000000 : ℝ)|=(5243339509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706970009/5000000000 : ℝ)|^539 ≤ (44721880680983/100000000000000 : ℝ)^411
        have hw : |(2706970009/5000000000 : ℝ)|=(2706970009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305113019/10000000000 : ℝ)*x 0 + (-1951459349/10000000000 : ℝ)*x 1 + (676742527/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305113019/10000000000 : ℝ)^539 ≤ (21773326052619/50000000000000 : ℝ)^411 := by
    have hnat : (5305113019 : ℕ)^539*50000000000000^411 ≤ 21773326052619^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305113019 10000000000 21773326052619 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1951459349/10000000000 : ℝ)^539 ≤ (11731465055621/100000000000000 : ℝ)^411 := by
    have hnat : (1951459349 : ℕ)^539*100000000000000^411 ≤ 11731465055621^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951459349 10000000000 11731465055621 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676742527/1250000000 : ℝ)^539 ≤ (44721882825941/100000000000000 : ℝ)^411 := by
    have hnat : (676742527 : ℕ)^539*100000000000000^411 ≤ 44721882825941^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676742527 1250000000 44721882825941 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305113019/10000000000 : ℝ), (-1951459349/10000000000 : ℝ), (676742527/1250000000 : ℝ)] ![(21773326052619/50000000000000 : ℝ), (11731465055621/100000000000000 : ℝ), (44721882825941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305113019/10000000000 : ℝ)|^539 ≤ (21773326052619/50000000000000 : ℝ)^411
        have hw : |(5305113019/10000000000 : ℝ)|=(5305113019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1951459349/10000000000 : ℝ)|^539 ≤ (11731465055621/100000000000000 : ℝ)^411
        have hw : |(-1951459349/10000000000 : ℝ)|=(1951459349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676742527/1250000000 : ℝ)|^539 ≤ (44721882825941/100000000000000 : ℝ)^411
        have hw : |(676742527/1250000000 : ℝ)|=(676742527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305113411/10000000000 : ℝ)*x 0 + (676742501/1250000000 : ℝ)*x 1 + (-1951459099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305113411/10000000000 : ℝ)^539 ≤ (43546656325051/100000000000000 : ℝ)^411 := by
    have hnat : (5305113411 : ℕ)^539*100000000000000^411 ≤ 43546656325051^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305113411 10000000000 43546656325051 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676742501/1250000000 : ℝ)^539 ≤ (11180470143163/25000000000000 : ℝ)^411 := by
    have hnat : (676742501 : ℕ)^539*25000000000000^411 ≤ 11180470143163^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676742501 1250000000 11180470143163 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1951459099/10000000000 : ℝ)^539 ≤ (2932865771163/25000000000000 : ℝ)^411 := by
    have hnat : (1951459099 : ℕ)^539*25000000000000^411 ≤ 2932865771163^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951459099 10000000000 2932865771163 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305113411/10000000000 : ℝ), (676742501/1250000000 : ℝ), (-1951459099/10000000000 : ℝ)] ![(43546656325051/100000000000000 : ℝ), (11180470143163/25000000000000 : ℝ), (2932865771163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305113411/10000000000 : ℝ)|^539 ≤ (43546656325051/100000000000000 : ℝ)^411
        have hw : |(5305113411/10000000000 : ℝ)|=(5305113411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676742501/1250000000 : ℝ)|^539 ≤ (11180470143163/25000000000000 : ℝ)^411
        have hw : |(676742501/1250000000 : ℝ)|=(676742501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1951459099/10000000000 : ℝ)|^539 ≤ (2932865771163/25000000000000 : ℝ)^411
        have hw : |(-1951459099/10000000000 : ℝ)|=(1951459099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s4_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1080968523/2500000000 : ℝ)*x 0 + (4506702117/10000000000 : ℝ)*x 1 + (207401053/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080968523/2500000000 : ℝ)^539 ≤ (6660410001001/20000000000000 : ℝ)^411 := by
    have hnat : (1080968523 : ℕ)^539*20000000000000^411 ≤ 6660410001001^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080968523 2500000000 6660410001001 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506702117/10000000000 : ℝ)^539 ≤ (35160755967203/100000000000000 : ℝ)^411 := by
    have hnat : (4506702117 : ℕ)^539*100000000000000^411 ≤ 35160755967203^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506702117 10000000000 35160755967203 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207401053/500000000 : ℝ)^539 ≤ (492768656493/1562500000000 : ℝ)^411 := by
    have hnat : (207401053 : ℕ)^539*1562500000000^411 ≤ 492768656493^411*500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207401053 500000000 492768656493 1562500000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080968523/2500000000 : ℝ), (4506702117/10000000000 : ℝ), (207401053/500000000 : ℝ)] ![(6660410001001/20000000000000 : ℝ), (35160755967203/100000000000000 : ℝ), (492768656493/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080968523/2500000000 : ℝ)|^539 ≤ (6660410001001/20000000000000 : ℝ)^411
        have hw : |(1080968523/2500000000 : ℝ)|=(1080968523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506702117/10000000000 : ℝ)|^539 ≤ (35160755967203/100000000000000 : ℝ)^411
        have hw : |(4506702117/10000000000 : ℝ)|=(4506702117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207401053/500000000 : ℝ)|^539 ≤ (492768656493/1562500000000 : ℝ)^411
        have hw : |(207401053/500000000 : ℝ)|=(207401053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3/20 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5451/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (89/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3/20 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5451/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3/20 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5451/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3/20 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5451/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3/20 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5451/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3/20 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5451/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3/20 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5451/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5451/50000 : ℝ) ^ (4311/1024 : ℝ) ≤ (8870306071453681/100000000000000000000 : ℝ) := by
    have hpowers : (5451/50000 : ℝ)^4311 ≤ (8870306071453681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5451 : ℕ)^4311*100000000000000000000^1024 ≤ 8870306071453681^1024*50000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5451 50000 8870306071453681 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5451/50000 : ℝ)) (X := (8870306071453681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3/20 : ℝ) ^ (4311/1024 : ℝ) ≤ (8497993473857753/25000000000000000000 : ℝ) := by
    have hpowers : (3/20 : ℝ)^4311 ≤ (8497993473857753/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3 : ℕ)^4311*25000000000000000000^1024 ≤ 8497993473857753^1024*20^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 20 8497993473857753 25000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/20 : ℝ)) (X := (8497993473857753/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008870306071453681/50000000000000000000 : ℝ) ≤ (400016854704997/400000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50008870306071453681/50000000000000000000 : ℝ)^1024 ≤ (400016854704997/400000000000000 : ℝ)^4311 := by
      have hnat : (50008870306071453681 : ℕ)^1024*400000000000000^4311 ≤ 400016854704997^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008870306071453681 50000000000000000000 400016854704997 400000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016854704997/400000000000000 : ℝ)) (X := (50008870306071453681/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042862279966884693/100000000000000000000 : ℝ) ≤ (2500254487383787/2500000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (100042862279966884693/100000000000000000000 : ℝ)^1024 ≤ (2500254487383787/2500000000000000 : ℝ)^4311 := by
      have hnat : (100042862279966884693 : ℕ)^1024*2500000000000000^4311 ≤ 2500254487383787^4311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042862279966884693 100000000000000000000 2500254487383787 2500000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500254487383787/2500000000000000 : ℝ)) (X := (100042862279966884693/100000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508497993473857753/12500000000000000000 : ℝ) ≤ (10001614531445371/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (12508497993473857753/12500000000000000000 : ℝ)^1024 ≤ (10001614531445371/10000000000000000 : ℝ)^4311 := by
      have hnat : (12508497993473857753 : ℕ)^1024*10000000000000000^4311 ≤ 10001614531445371^4311*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508497993473857753 12500000000000000000 10001614531445371 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001614531445371/10000000000000000 : ℝ)) (X := (12508497993473857753/12500000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8870306071453681/100000000000000000000 : ℝ) ≤ ((6828119815426073393/6830000000000000000 : ℝ)+2*(198860636741/136600000000000 : ℝ)*(5451/50000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (6828119815426073393/6830000000000000000 : ℝ)+2*(198860636741/136600000000000 : ℝ)*(5451/50000 : ℝ)=(400016854704997/400000000000000 : ℝ) by norm_num, show 1+2*(8870306071453681/100000000000000000000 : ℝ)=(50008870306071453681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8497993473857753/25000000000000000000 : ℝ)+(8870306071453681/100000000000000000000 : ℝ) ≤ ((6828119815426073393/6830000000000000000 : ℝ)+(198860636741/136600000000000 : ℝ)*((3/20 : ℝ)+(5451/50000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (6828119815426073393/6830000000000000000 : ℝ)+(198860636741/136600000000000 : ℝ)*((3/20 : ℝ)+(5451/50000 : ℝ))=(2500254487383787/2500000000000000 : ℝ) by norm_num, show 1+(8497993473857753/25000000000000000000 : ℝ)+(8870306071453681/100000000000000000000 : ℝ)=(100042862279966884693/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8497993473857753/25000000000000000000 : ℝ) ≤ ((6828119815426073393/6830000000000000000 : ℝ)+2*(198860636741/136600000000000 : ℝ)*(3/20 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (6828119815426073393/6830000000000000000 : ℝ)+2*(198860636741/136600000000000 : ℝ)*(3/20 : ℝ)=(10001614531445371/10000000000000000 : ℝ) by norm_num, show 1+2*(8497993473857753/25000000000000000000 : ℝ)=(12508497993473857753/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6828119815426073393/6830000000000000000 : ℝ)*(X 1 0+X 2 0)+(198860636741/136600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (5451/50000 : ℝ)) (hi := (3/20 : ℝ)) (c := (6828119815426073393/6830000000000000000 : ℝ)) (alpha := (198860636741/136600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6828119815426073393/6830000000000000000 : ℝ)*(X 0 1+X 2 1)+(198860636741/136600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (5451/50000 : ℝ)) (hi := (3/20 : ℝ)) (c := (6828119815426073393/6830000000000000000 : ℝ)) (alpha := (198860636741/136600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6828119815426073393/6830000000000000000 : ℝ)*(X 0 2+X 1 2)+(198860636741/136600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (5451/50000 : ℝ)) (hi := (3/20 : ℝ)) (c := (6828119815426073393/6830000000000000000 : ℝ)) (alpha := (198860636741/136600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-508771827/2500000000 : ℝ)*X 0 0+(5414576063/10000000000 : ℝ)*X 0 1+(5242706843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213977343/400000000 : ℝ)*X 1 0+(-212269229/1000000000 : ℝ)*X 1 1+(2621353407/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337358393/2500000000 : ℝ)*X 2 0+(1310676709/2500000000 : ℝ)*X 2 1+(-2122692263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323846307/10000000000 : ℝ)*X 0 0+(1036671121/2500000000 : ℝ)*X 0 1+(1127007979/2500000000 : ℝ)*X 0 2+(4323846307/10000000000 : ℝ)*X 1 0+(1036671121/2500000000 : ℝ)*X 1 1+(1127007979/2500000000 : ℝ)*X 1 2+(4323846307/10000000000 : ℝ)*X 2 0+(1036671121/2500000000 : ℝ)*X 2 1+(1127007979/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407020087/2000000000 : ℝ)*X 0 0+(5243339509/10000000000 : ℝ)*X 0 1+(2706970009/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305113019/10000000000 : ℝ)*X 1 0+(-1951459349/10000000000 : ℝ)*X 1 1+(676742527/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305113411/10000000000 : ℝ)*X 2 0+(676742501/1250000000 : ℝ)*X 2 1+(-1951459099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080968523/2500000000 : ℝ)*X 0 0+(4506702117/10000000000 : ℝ)*X 0 1+(207401053/500000000 : ℝ)*X 0 2+(1080968523/2500000000 : ℝ)*X 1 0+(4506702117/10000000000 : ℝ)*X 1 1+(207401053/500000000 : ℝ)*X 1 2+(1080968523/2500000000 : ℝ)*X 2 0+(4506702117/10000000000 : ℝ)*X 2 1+(207401053/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124420590169997477390911329/17075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54980089/4000000000000 : ℝ)*(base19) + (646277721/50000000000000 : ℝ)*(base23) + (42091357/100000000000000 : ℝ)*(lower2) + (31558617/20000000000000 : ℝ)*(upper3) + (65202337/50000000000000 : ℝ)*(upper5) + (214646996433149/5000000000000 : ℝ)*(major0) + (214646996433149/5000000000000 : ℝ)*(major1) + (214646996433149/5000000000000 : ℝ)*(major2) + (2909202667537569/50000000000000 : ℝ)*(sp0) + (1163686389446581/20000000000000 : ℝ)*(sp1) + (727304003647461/12500000000000 : ℝ)*(sp2) + (1383716293774703/50000000000000 : ℝ)*(sp3) + (3498332499/12500000000000 : ℝ)*(sp4) + (3426287763/25000000000000 : ℝ)*(sp7) + (1383723146350229/50000000000000 : ℝ)*(f.failure) + (581843332173513/10000000000000 : ℝ)*(f.sum) + (324374547187/170750000000000000000000000 : ℝ)*base66 + (151564176958945443/34150000000000000000000000000000 : ℝ)*base68 + (63939842127654557/34150000000000000000000000000000 : ℝ)*base69 + (407415501758404557/34150000000000000000000000000000 : ℝ)*base71 + (239502873109/170750000000000000000000000 : ℝ)*base74 + (97534522014345443/34150000000000000000000000000000 : ℝ)*base76 + (193776511260254557/34150000000000000000000000000000 : ℝ)*base77 + (387134945245154557/34150000000000000000000000000000 : ℝ)*base79 + (313734618321/341500000000000000000000000 : ℝ)*base81 + (14030861/5000000000000000000000 : ℝ)*base90 + (14030861/5000000000000000000000 : ℝ)*base92 + (14030861/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (531953750350748490725090781/170750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67406381/100000000000000 : ℝ)*(base19) + (231757683/50000000000000 : ℝ)*(base23) + (65605237/100000000000000 : ℝ)*(lower2) + (2296463/1562500000000 : ℝ)*(upper3) + (4444827/6250000000000 : ℝ)*(upper5) + (4324825600167239/100000000000000 : ℝ)*(major0) + (4324825600167239/100000000000000 : ℝ)*(major1) + (4324825600167239/100000000000000 : ℝ)*(major2) + (207440043/2000000000000 : ℝ)*(sp2) + (719307241/25000000000000 : ℝ)*(sp3) + (5861649686580863/100000000000000 : ℝ)*(sp4) + (2930824809587241/50000000000000 : ℝ)*(sp5) + (5861638851063347/100000000000000 : ℝ)*(sp6) + (696999633169533/25000000000000 : ℝ)*(sp7) + (2788001409907097/100000000000000 : ℝ)*(f.failure) + (5861649686580863/100000000000000 : ℝ)*(f.sum) + (16168615955889/6830000000000000000000000000 : ℝ)*base65 + (5971383174272121927/683000000000000000000000000000000 : ℝ)*base67 + (2436984878180878073/683000000000000000000000000000000 : ℝ)*base70 + (5392751231456878073/683000000000000000000000000000000 : ℝ)*base72 + (31355454840439/6830000000000000000000000000 : ℝ)*base73 + (9971904108954878073/683000000000000000000000000000000 : ℝ)*base76 + (3586656943353878073/683000000000000000000000000000000 : ℝ)*base78 + (5220369507574878073/683000000000000000000000000000000 : ℝ)*base80 + (40923620015069/6830000000000000000000000000 : ℝ)*base81 + (37347727/10000000000000000000000 : ℝ)*base89 + (37347727/10000000000000000000000 : ℝ)*base91 + (37347727/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1352_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3/20 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5451/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1352_s5_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035321787/10000000000 : ℝ)*x 0 + (1353136033/2500000000 : ℝ)*x 1 + (5244584433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035321787/10000000000 : ℝ)^539 ≤ (12397007489633/100000000000000 : ℝ)^411 := by
    have hnat : (2035321787 : ℕ)^539*100000000000000^411 ≤ 12397007489633^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035321787 10000000000 12397007489633 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353136033/2500000000 : ℝ)^539 ≤ (44706759487317/100000000000000 : ℝ)^411 := by
    have hnat : (1353136033 : ℕ)^539*100000000000000^411 ≤ 44706759487317^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353136033 2500000000 44706759487317 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244584433/10000000000 : ℝ)^539 ≤ (21448116499859/50000000000000 : ℝ)^411 := by
    have hnat : (5244584433 : ℕ)^539*50000000000000^411 ≤ 21448116499859^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244584433 10000000000 21448116499859 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2035321787/10000000000 : ℝ), (1353136033/2500000000 : ℝ), (5244584433/10000000000 : ℝ)] ![(12397007489633/100000000000000 : ℝ), (44706759487317/100000000000000 : ℝ), (21448116499859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2035321787/10000000000 : ℝ)|^539 ≤ (12397007489633/100000000000000 : ℝ)^411
        have hw : |(-2035321787/10000000000 : ℝ)|=(2035321787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353136033/2500000000 : ℝ)|^539 ≤ (44706759487317/100000000000000 : ℝ)^411
        have hw : |(1353136033/2500000000 : ℝ)|=(1353136033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244584433/10000000000 : ℝ)|^539 ≤ (21448116499859/50000000000000 : ℝ)^411
        have hw : |(5244584433/10000000000 : ℝ)|=(5244584433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348913751/10000000000 : ℝ)*x 0 + (-1060448371/5000000000 : ℝ)*x 1 + (1048916903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348913751/10000000000 : ℝ)^539 ≤ (2751172780057/6250000000000 : ℝ)^411 := by
    have hnat : (5348913751 : ℕ)^539*6250000000000^411 ≤ 2751172780057^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348913751 10000000000 2751172780057 6250000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060448371/5000000000 : ℝ)^539 ≤ (2617000325037/20000000000000 : ℝ)^411 := by
    have hnat : (1060448371 : ℕ)^539*20000000000000^411 ≤ 2617000325037^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060448371 5000000000 2617000325037 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048916903/2000000000 : ℝ)^539 ≤ (8579246775857/20000000000000 : ℝ)^411 := by
    have hnat : (1048916903 : ℕ)^539*20000000000000^411 ≤ 8579246775857^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048916903 2000000000 8579246775857 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348913751/10000000000 : ℝ), (-1060448371/5000000000 : ℝ), (1048916903/2000000000 : ℝ)] ![(2751172780057/6250000000000 : ℝ), (2617000325037/20000000000000 : ℝ), (8579246775857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348913751/10000000000 : ℝ)|^539 ≤ (2751172780057/6250000000000 : ℝ)^411
        have hw : |(5348913751/10000000000 : ℝ)|=(5348913751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060448371/5000000000 : ℝ)|^539 ≤ (2617000325037/20000000000000 : ℝ)^411
        have hw : |(-1060448371/5000000000 : ℝ)|=(1060448371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048916903/2000000000 : ℝ)|^539 ≤ (8579246775857/20000000000000 : ℝ)^411
        have hw : |(1048916903/2000000000 : ℝ)|=(1048916903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668614179/1250000000 : ℝ)*x 0 + (5244584617/10000000000 : ℝ)*x 1 + (-265112129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668614179/1250000000 : ℝ)^539 ≤ (44018761038127/100000000000000 : ℝ)^411 := by
    have hnat : (668614179 : ℕ)^539*100000000000000^411 ≤ 44018761038127^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668614179 1250000000 44018761038127 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244584617/10000000000 : ℝ)^539 ≤ (2144811748669/5000000000000 : ℝ)^411 := by
    have hnat : (5244584617 : ℕ)^539*5000000000000^411 ≤ 2144811748669^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244584617 10000000000 2144811748669 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265112129/1250000000 : ℝ)^539 ≤ (13085003971569/100000000000000 : ℝ)^411 := by
    have hnat : (265112129 : ℕ)^539*100000000000000^411 ≤ 13085003971569^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265112129 1250000000 13085003971569 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668614179/1250000000 : ℝ), (5244584617/10000000000 : ℝ), (-265112129/1250000000 : ℝ)] ![(44018761038127/100000000000000 : ℝ), (2144811748669/5000000000000 : ℝ), (13085003971569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668614179/1250000000 : ℝ)|^539 ≤ (44018761038127/100000000000000 : ℝ)^411
        have hw : |(668614179/1250000000 : ℝ)|=(668614179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244584617/10000000000 : ℝ)|^539 ≤ (2144811748669/5000000000000 : ℝ)^411
        have hw : |(5244584617/10000000000 : ℝ)|=(5244584617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265112129/1250000000 : ℝ)|^539 ≤ (13085003971569/100000000000000 : ℝ)^411
        have hw : |(-265112129/1250000000 : ℝ)|=(265112129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4323986581/10000000000 : ℝ)*x 0 + (1037694271/2500000000 : ℝ)*x 1 + (450390477/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323986581/10000000000 : ℝ)^539 ≤ (6660637241997/20000000000000 : ℝ)^411 := by
    have hnat : (4323986581 : ℕ)^539*20000000000000^411 ≤ 6660637241997^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323986581 10000000000 6660637241997 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037694271/2500000000 : ℝ)^539 ≤ (31564676561289/100000000000000 : ℝ)^411 := by
    have hnat : (1037694271 : ℕ)^539*100000000000000^411 ≤ 31564676561289^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037694271 2500000000 31564676561289 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450390477/1000000000 : ℝ)^539 ≤ (17566068608909/50000000000000 : ℝ)^411 := by
    have hnat : (450390477 : ℕ)^539*50000000000000^411 ≤ 17566068608909^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450390477 1000000000 17566068608909 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323986581/10000000000 : ℝ), (1037694271/2500000000 : ℝ), (450390477/1000000000 : ℝ)] ![(6660637241997/20000000000000 : ℝ), (31564676561289/100000000000000 : ℝ), (17566068608909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323986581/10000000000 : ℝ)|^539 ≤ (6660637241997/20000000000000 : ℝ)^411
        have hw : |(4323986581/10000000000 : ℝ)|=(4323986581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037694271/2500000000 : ℝ)|^539 ≤ (31564676561289/100000000000000 : ℝ)^411
        have hw : |(1037694271/2500000000 : ℝ)|=(1037694271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450390477/1000000000 : ℝ)|^539 ≤ (17566068608909/50000000000000 : ℝ)^411
        have hw : |(450390477/1000000000 : ℝ)|=(450390477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017666913/5000000000 : ℝ)*x 0 + (1049037789/2000000000 : ℝ)*x 1 + (1352984157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017666913/5000000000 : ℝ)^539 ≤ (12397103655631/100000000000000 : ℝ)^411 := by
    have hnat : (1017666913 : ℕ)^539*100000000000000^411 ≤ 12397103655631^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017666913 5000000000 12397103655631 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049037789/2000000000 : ℝ)^539 ≤ (2145135868449/5000000000000 : ℝ)^411 := by
    have hnat : (1049037789 : ℕ)^539*5000000000000^411 ≤ 2145135868449^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049037789 2000000000 2145135868449 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352984157/2500000000 : ℝ)^539 ≤ (2235008948349/5000000000000 : ℝ)^411 := by
    have hnat : (1352984157 : ℕ)^539*5000000000000^411 ≤ 2235008948349^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352984157 2500000000 2235008948349 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017666913/5000000000 : ℝ), (1049037789/2000000000 : ℝ), (1352984157/2500000000 : ℝ)] ![(12397103655631/100000000000000 : ℝ), (2145135868449/5000000000000 : ℝ), (2235008948349/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017666913/5000000000 : ℝ)|^539 ≤ (12397103655631/100000000000000 : ℝ)^411
        have hw : |(-1017666913/5000000000 : ℝ)|=(1017666913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049037789/2000000000 : ℝ)|^539 ≤ (2145135868449/5000000000000 : ℝ)^411
        have hw : |(1049037789/2000000000 : ℝ)|=(1049037789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352984157/2500000000 : ℝ)|^539 ≤ (2235008948349/5000000000000 : ℝ)^411
        have hw : |(1352984157/2500000000 : ℝ)|=(1352984157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652800347/5000000000 : ℝ)*x 0 + (-122096547/625000000 : ℝ)*x 1 + (216477503/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652800347/5000000000 : ℝ)^539 ≤ (680498467463/1562500000000 : ℝ)^411 := by
    have hnat : (2652800347 : ℕ)^539*1562500000000^411 ≤ 680498467463^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652800347 5000000000 680498467463 1562500000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122096547/625000000 : ℝ)^539 ≤ (734244302859/6250000000000 : ℝ)^411 := by
    have hnat : (122096547 : ℕ)^539*6250000000000^411 ≤ 734244302859^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122096547 625000000 734244302859 6250000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216477503/400000000 : ℝ)^539 ≤ (22350094612381/50000000000000 : ℝ)^411 := by
    have hnat : (216477503 : ℕ)^539*50000000000000^411 ≤ 22350094612381^411*400000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216477503 400000000 22350094612381 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652800347/5000000000 : ℝ), (-122096547/625000000 : ℝ), (216477503/400000000 : ℝ)] ![(680498467463/1562500000000 : ℝ), (734244302859/6250000000000 : ℝ), (22350094612381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652800347/5000000000 : ℝ)|^539 ≤ (680498467463/1562500000000 : ℝ)^411
        have hw : |(2652800347/5000000000 : ℝ)|=(2652800347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122096547/625000000 : ℝ)|^539 ≤ (734244302859/6250000000000 : ℝ)^411
        have hw : |(-122096547/625000000 : ℝ)|=(122096547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216477503/400000000 : ℝ)|^539 ≤ (22350094612381/50000000000000 : ℝ)^411
        have hw : |(216477503/400000000 : ℝ)|=(216477503/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305600849/10000000000 : ℝ)*x 0 + (42280761/78125000 : ℝ)*x 1 + (-1953544769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305600849/10000000000 : ℝ)^539 ≤ (10887975896557/25000000000000 : ℝ)^411 := by
    have hnat : (5305600849 : ℕ)^539*25000000000000^411 ≤ 10887975896557^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305600849 10000000000 10887975896557 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42280761/78125000 : ℝ)^539 ≤ (279376171349/625000000000 : ℝ)^411 := by
    have hnat : (42280761 : ℕ)^539*625000000000^411 ≤ 279376171349^411*78125000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42280761 78125000 279376171349 625000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953544769/10000000000 : ℝ)^539 ≤ (2349581795963/20000000000000 : ℝ)^411 := by
    have hnat : (1953544769 : ℕ)^539*20000000000000^411 ≤ 2349581795963^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953544769 10000000000 2349581795963 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305600849/10000000000 : ℝ), (42280761/78125000 : ℝ), (-1953544769/10000000000 : ℝ)] ![(10887975896557/25000000000000 : ℝ), (279376171349/625000000000 : ℝ), (2349581795963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305600849/10000000000 : ℝ)|^539 ≤ (10887975896557/25000000000000 : ℝ)^411
        have hw : |(5305600849/10000000000 : ℝ)|=(5305600849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42280761/78125000 : ℝ)|^539 ≤ (279376171349/625000000000 : ℝ)^411
        have hw : |(42280761/78125000 : ℝ)|=(42280761/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953544769/10000000000 : ℝ)|^539 ≤ (2349581795963/20000000000000 : ℝ)^411
        have hw : |(-1953544769/10000000000 : ℝ)|=(1953544769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s5_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4324012113/10000000000 : ℝ)*x 0 + (2251317387/5000000000 : ℝ)*x 1 + (415205381/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324012113/10000000000 : ℝ)^539 ≤ (6660688819893/20000000000000 : ℝ)^411 := by
    have hnat : (4324012113 : ℕ)^539*20000000000000^411 ≤ 6660688819893^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324012113 10000000000 6660688819893 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251317387/5000000000 : ℝ)^539 ≤ (35119146127669/100000000000000 : ℝ)^411 := by
    have hnat : (2251317387 : ℕ)^539*100000000000000^411 ≤ 35119146127669^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251317387 5000000000 35119146127669 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415205381/1000000000 : ℝ)^539 ≤ (31577409755951/100000000000000 : ℝ)^411 := by
    have hnat : (415205381 : ℕ)^539*100000000000000^411 ≤ 31577409755951^411*1000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415205381 1000000000 31577409755951 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324012113/10000000000 : ℝ), (2251317387/5000000000 : ℝ), (415205381/1000000000 : ℝ)] ![(6660688819893/20000000000000 : ℝ), (35119146127669/100000000000000 : ℝ), (31577409755951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324012113/10000000000 : ℝ)|^539 ≤ (6660688819893/20000000000000 : ℝ)^411
        have hw : |(4324012113/10000000000 : ℝ)|=(4324012113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251317387/5000000000 : ℝ)|^539 ≤ (35119146127669/100000000000000 : ℝ)^411
        have hw : |(2251317387/5000000000 : ℝ)|=(2251317387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415205381/1000000000 : ℝ)|^539 ≤ (31577409755951/100000000000000 : ℝ)^411
        have hw : |(415205381/1000000000 : ℝ)|=(415205381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    (2233/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (89/800 : ℝ) ^ (4311/1024 : ℝ) ≤ (9659626552812309/100000000000000000000 : ℝ) := by
    have hpowers : (89/800 : ℝ)^4311 ≤ (9659626552812309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^4311*100000000000000000000^1024 ≤ 9659626552812309^1024*800^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 800 9659626552812309 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/800 : ℝ)) (X := (9659626552812309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (15893795017529269/50000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^4311 ≤ (15893795017529269/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14763 : ℕ)^4311*50000000000000000000^1024 ≤ 15893795017529269^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 15893795017529269 50000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (15893795017529269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009659626552812309/50000000000000000000 : ℝ) ≤ (1000045886008589/1000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50009659626552812309/50000000000000000000 : ℝ)^1024 ≤ (1000045886008589/1000000000000000 : ℝ)^4311 := by
      have hnat : (50009659626552812309 : ℕ)^1024*1000000000000000^4311 ≤ 1000045886008589^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009659626552812309 50000000000000000000 1000045886008589 1000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000045886008589/1000000000000000 : ℝ)) (X := (50009659626552812309/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041447216587870847/100000000000000000000 : ℝ) ≤ (1250123043508257/1250000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (100041447216587870847/100000000000000000000 : ℝ)^1024 ≤ (1250123043508257/1250000000000000 : ℝ)^4311 := by
      have hnat : (100041447216587870847 : ℕ)^1024*1250000000000000^4311 ≤ 1250123043508257^4311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041447216587870847 100000000000000000000 1250123043508257 1250000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250123043508257/1250000000000000 : ℝ)) (X := (100041447216587870847/100000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015893795017529269/25000000000000000000 : ℝ) ≤ (5000754918023111/5000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (25015893795017529269/25000000000000000000 : ℝ)^1024 ≤ (5000754918023111/5000000000000000 : ℝ)^4311 := by
      have hnat : (25015893795017529269 : ℕ)^1024*5000000000000000^4311 ≤ 5000754918023111^4311*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015893795017529269 25000000000000000000 5000754918023111 5000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000754918023111/5000000000000000 : ℝ)) (X := (25015893795017529269/25000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9659626552812309/100000000000000000000 : ℝ) ≤ ((454624715317922179/454750000000000000 : ℝ)+2*(262743990083/181900000000000 : ℝ)*(89/800 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (454624715317922179/454750000000000000 : ℝ)+2*(262743990083/181900000000000 : ℝ)*(89/800 : ℝ)=(1000045886008589/1000000000000000 : ℝ) by norm_num, show 1+2*(9659626552812309/100000000000000000000 : ℝ)=(50009659626552812309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15893795017529269/50000000000000000000 : ℝ)+(9659626552812309/100000000000000000000 : ℝ) ≤ ((454624715317922179/454750000000000000 : ℝ)+(262743990083/181900000000000 : ℝ)*((14763/100000 : ℝ)+(89/800 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (454624715317922179/454750000000000000 : ℝ)+(262743990083/181900000000000 : ℝ)*((14763/100000 : ℝ)+(89/800 : ℝ))=(1250123043508257/1250000000000000 : ℝ) by norm_num, show 1+(15893795017529269/50000000000000000000 : ℝ)+(9659626552812309/100000000000000000000 : ℝ)=(100041447216587870847/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15893795017529269/50000000000000000000 : ℝ) ≤ ((454624715317922179/454750000000000000 : ℝ)+2*(262743990083/181900000000000 : ℝ)*(14763/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (454624715317922179/454750000000000000 : ℝ)+2*(262743990083/181900000000000 : ℝ)*(14763/100000 : ℝ)=(5000754918023111/5000000000000000 : ℝ) by norm_num, show 1+2*(15893795017529269/50000000000000000000 : ℝ)=(25015893795017529269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (454624715317922179/454750000000000000 : ℝ)*(X 1 0+X 2 0)+(262743990083/181900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (454624715317922179/454750000000000000 : ℝ)) (alpha := (262743990083/181900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (454624715317922179/454750000000000000 : ℝ)*(X 0 1+X 2 1)+(262743990083/181900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (454624715317922179/454750000000000000 : ℝ)) (alpha := (262743990083/181900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (454624715317922179/454750000000000000 : ℝ)*(X 0 2+X 1 2)+(262743990083/181900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (454624715317922179/454750000000000000 : ℝ)) (alpha := (262743990083/181900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2035321787/10000000000 : ℝ)*X 0 0+(1353136033/2500000000 : ℝ)*X 0 1+(5244584433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348913751/10000000000 : ℝ)*X 1 0+(-1060448371/5000000000 : ℝ)*X 1 1+(1048916903/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668614179/1250000000 : ℝ)*X 2 0+(5244584617/10000000000 : ℝ)*X 2 1+(-265112129/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323986581/10000000000 : ℝ)*X 0 0+(1037694271/2500000000 : ℝ)*X 0 1+(450390477/1000000000 : ℝ)*X 0 2+(4323986581/10000000000 : ℝ)*X 1 0+(1037694271/2500000000 : ℝ)*X 1 1+(450390477/1000000000 : ℝ)*X 1 2+(4323986581/10000000000 : ℝ)*X 2 0+(1037694271/2500000000 : ℝ)*X 2 1+(450390477/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1017666913/5000000000 : ℝ)*X 0 0+(1049037789/2000000000 : ℝ)*X 0 1+(1352984157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652800347/5000000000 : ℝ)*X 1 0+(-122096547/625000000 : ℝ)*X 1 1+(216477503/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305600849/10000000000 : ℝ)*X 2 0+(42280761/78125000 : ℝ)*X 2 1+(-1953544769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324012113/10000000000 : ℝ)*X 0 0+(2251317387/5000000000 : ℝ)*X 0 1+(415205381/1000000000 : ℝ)*X 0 2+(4324012113/10000000000 : ℝ)*X 1 0+(2251317387/5000000000 : ℝ)*X 1 1+(415205381/1000000000 : ℝ)*X 1 2+(4324012113/10000000000 : ℝ)*X 2 0+(2251317387/5000000000 : ℝ)*X 2 1+(415205381/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78429453007275629724483/9095000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298668401/20000000000000 : ℝ)*(base19) + (544304621/50000000000000 : ℝ)*(base23) + (12132973/20000000000000 : ℝ)*(upper2) + (453228639/100000000000000 : ℝ)*(upper3) + (43612339/50000000000000 : ℝ)*(upper4) + (4392863581859501/100000000000000 : ℝ)*(major0) + (4392863581859501/100000000000000 : ℝ)*(major1) + (4392863581859501/100000000000000 : ℝ)*(major2) + (2976923235782539/50000000000000 : ℝ)*(sp0) + (2976931623715937/50000000000000 : ℝ)*(sp1) + (5953863652164637/100000000000000 : ℝ)*(sp2) + (2831846688411587/100000000000000 : ℝ)*(sp3) + (18269208801/100000000000000 : ℝ)*(sp4) + (15447088219/100000000000000 : ℝ)*(sp7) + (1415931067749903/50000000000000 : ℝ)*(f.failure) + (5953864740773879/100000000000000 : ℝ)*(f.sum) + (128741776681293/9095000000000000000000000000 : ℝ)*base65 + (275786522925105179/45475000000000000000000000000000 : ℝ)*base67 + (230456991674780179/45475000000000000000000000000000 : ℝ)*base69 + (8562548361430179/45475000000000000000000000000000 : ℝ)*base71 + (34092917270513/9095000000000000000000000000 : ℝ)*base73 + (677257537406519821/45475000000000000000000000000000 : ℝ)*base76 + (284769610373319821/45475000000000000000000000000000 : ℝ)*base78 + (145978721884194821/45475000000000000000000000000000 : ℝ)*base80 + (30748397549963/9095000000000000000000000000 : ℝ)*base81 + (6660727/5000000000000000000000 : ℝ)*base90 + (6660727/5000000000000000000000 : ℝ)*base92 + (6660727/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104502125309061829725099/9095000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269504539/100000000000000 : ℝ)*(base15) + (8222861/25000000000000 : ℝ)*(upper2) + (37389681/10000000000000 : ℝ)*(upper3) + (8539643/25000000000000 : ℝ)*(upper4) + (38244917/100000000000000 : ℝ)*(upper5) + (2212370627092247/50000000000000 : ℝ)*(major0) + (2212370627092247/50000000000000 : ℝ)*(major1) + (2212370627092247/50000000000000 : ℝ)*(major2) + (1439219153/50000000000000 : ℝ)*(sp1) + (109197223/1000000000000 : ℝ)*(sp2) + (374816876833507/6250000000000 : ℝ)*(sp4) + (5997066881393267/100000000000000 : ℝ)*(sp5) + (1499264777403453/25000000000000 : ℝ)*(sp6) + (1426206048015373/50000000000000 : ℝ)*(sp7) + (1426206048015373/50000000000000 : ℝ)*(f.failure) + (374816876833507/6250000000000 : ℝ)*(f.sum) + (78554810092667/2273750000000000000000000000 : ℝ)*base66 + (69827876693951287/22737500000000000000000000000000 : ℝ)*base68 + (435685653164948713/22737500000000000000000000000000 : ℝ)*base69 + (276531218586476287/22737500000000000000000000000000 : ℝ)*base72 + (15577709696021/4547500000000000000000000000 : ℝ)*base73 + (26323596302436213/22737500000000000000000000000000 : ℝ)*base75 + (1862212337861426287/22737500000000000000000000000000 : ℝ)*base78 + (209014442363998713/22737500000000000000000000000000 : ℝ)*base79 + (94903837378981/4547500000000000000000000000 : ℝ)*base81 + (29333957/5000000000000000000000 : ℝ)*base90 + (29333957/5000000000000000000000 : ℝ)*base92 + (29333957/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1352_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1352_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1352_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1352_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1352_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2479/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
