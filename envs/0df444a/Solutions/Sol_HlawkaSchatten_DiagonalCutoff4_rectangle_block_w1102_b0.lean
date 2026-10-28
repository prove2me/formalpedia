-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:01:34.675754+00:00
-- url     : https://prove2.me/submissions/43f40d0d-55f8-40d6-a885-a2c71e835981

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
theorem support_rectangle_w1102_s0_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-952267313/5000000000 : ℝ)*x 0 + (6063621371/10000000000 : ℝ)*x 1 + (4775393421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952267313/5000000000 : ℝ)^8295 ≤ (11058004362943/100000000000000 : ℝ)^6247 := by
    have hnat : (952267313 : ℕ)^8295*100000000000000^6247 ≤ 11058004362943^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952267313 5000000000 11058004362943 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6063621371/10000000000 : ℝ)^8295 ≤ (12865999797567/25000000000000 : ℝ)^6247 := by
    have hnat : (6063621371 : ℕ)^8295*25000000000000^6247 ≤ 12865999797567^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6063621371 10000000000 12865999797567 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775393421/10000000000 : ℝ)^8295 ≤ (585593694241/1562500000000 : ℝ)^6247 := by
    have hnat : (4775393421 : ℕ)^8295*1562500000000^6247 ≤ 585593694241^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775393421 10000000000 585593694241 1562500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952267313/5000000000 : ℝ), (6063621371/10000000000 : ℝ), (4775393421/10000000000 : ℝ)] ![(11058004362943/100000000000000 : ℝ), (12865999797567/25000000000000 : ℝ), (585593694241/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952267313/5000000000 : ℝ)|^8295 ≤ (11058004362943/100000000000000 : ℝ)^6247
        have hw : |(-952267313/5000000000 : ℝ)|=(952267313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6063621371/10000000000 : ℝ)|^8295 ≤ (12865999797567/25000000000000 : ℝ)^6247
        have hw : |(6063621371/10000000000 : ℝ)|=(6063621371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775393421/10000000000 : ℝ)|^8295 ≤ (585593694241/1562500000000 : ℝ)^6247
        have hw : |(4775393421/10000000000 : ℝ)|=(4775393421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759523739/5000000000 : ℝ)*x 0 + (-2644989661/10000000000 : ℝ)*x 1 + (4775391383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759523739/5000000000 : ℝ)^8295 ≤ (45418997856009/100000000000000 : ℝ)^6247 := by
    have hnat : (2759523739 : ℕ)^8295*100000000000000^6247 ≤ 45418997856009^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759523739 5000000000 45418997856009 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2644989661/10000000000 : ℝ)^8295 ≤ (8551513466733/50000000000000 : ℝ)^6247 := by
    have hnat : (2644989661 : ℕ)^8295*50000000000000^6247 ≤ 8551513466733^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644989661 10000000000 8551513466733 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775391383/10000000000 : ℝ)^8295 ≤ (2342373449581/6250000000000 : ℝ)^6247 := by
    have hnat : (4775391383 : ℕ)^8295*6250000000000^6247 ≤ 2342373449581^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775391383 10000000000 2342373449581 6250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759523739/5000000000 : ℝ), (-2644989661/10000000000 : ℝ), (4775391383/10000000000 : ℝ)] ![(45418997856009/100000000000000 : ℝ), (8551513466733/50000000000000 : ℝ), (2342373449581/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759523739/5000000000 : ℝ)|^8295 ≤ (45418997856009/100000000000000 : ℝ)^6247
        have hw : |(2759523739/5000000000 : ℝ)|=(2759523739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2644989661/10000000000 : ℝ)|^8295 ≤ (8551513466733/50000000000000 : ℝ)^6247
        have hw : |(-2644989661/10000000000 : ℝ)|=(2644989661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775391383/10000000000 : ℝ)|^8295 ≤ (2342373449581/6250000000000 : ℝ)^6247
        have hw : |(4775391383/10000000000 : ℝ)|=(4775391383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689880891/1250000000 : ℝ)*x 0 + (238769601/500000000 : ℝ)*x 1 + (-1322494667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689880891/1250000000 : ℝ)^8295 ≤ (45418994031407/100000000000000 : ℝ)^6247 := by
    have hnat : (689880891 : ℕ)^8295*100000000000000^6247 ≤ 45418994031407^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689880891 1250000000 45418994031407 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238769601/500000000 : ℝ)^8295 ≤ (37477981831513/100000000000000 : ℝ)^6247 := by
    have hnat : (238769601 : ℕ)^8295*100000000000000^6247 ≤ 37477981831513^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238769601 500000000 37477981831513 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322494667/5000000000 : ℝ)^8295 ≤ (684120965033/4000000000000 : ℝ)^6247 := by
    have hnat : (1322494667 : ℕ)^8295*4000000000000^6247 ≤ 684120965033^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322494667 5000000000 684120965033 4000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689880891/1250000000 : ℝ), (238769601/500000000 : ℝ), (-1322494667/5000000000 : ℝ)] ![(45418994031407/100000000000000 : ℝ), (37477981831513/100000000000000 : ℝ), (684120965033/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689880891/1250000000 : ℝ)|^8295 ≤ (45418994031407/100000000000000 : ℝ)^6247
        have hw : |(689880891/1250000000 : ℝ)|=(689880891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238769601/500000000 : ℝ)|^8295 ≤ (37477981831513/100000000000000 : ℝ)^6247
        have hw : |(238769601/500000000 : ℝ)|=(238769601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322494667/5000000000 : ℝ)|^8295 ≤ (684120965033/4000000000000 : ℝ)^6247
        have hw : |(-1322494667/5000000000 : ℝ)|=(1322494667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (420424547/1000000000 : ℝ)*x 0 + (3123005841/10000000000 : ℝ)*x 1 + (5665810059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420424547/1000000000 : ℝ)^8295 ≤ (7911502351783/25000000000000 : ℝ)^6247 := by
    have hnat : (420424547 : ℕ)^8295*25000000000000^6247 ≤ 7911502351783^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420424547 1000000000 7911502351783 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123005841/10000000000 : ℝ)^8295 ≤ (10662152251353/50000000000000 : ℝ)^6247 := by
    have hnat : (3123005841 : ℕ)^8295*50000000000000^6247 ≤ 10662152251353^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123005841 10000000000 10662152251353 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665810059/10000000000 : ℝ)^8295 ≤ (5878710758313/12500000000000 : ℝ)^6247 := by
    have hnat : (5665810059 : ℕ)^8295*12500000000000^6247 ≤ 5878710758313^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665810059 10000000000 5878710758313 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420424547/1000000000 : ℝ), (3123005841/10000000000 : ℝ), (5665810059/10000000000 : ℝ)] ![(7911502351783/25000000000000 : ℝ), (10662152251353/50000000000000 : ℝ), (5878710758313/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420424547/1000000000 : ℝ)|^8295 ≤ (7911502351783/25000000000000 : ℝ)^6247
        have hw : |(420424547/1000000000 : ℝ)|=(420424547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123005841/10000000000 : ℝ)|^8295 ≤ (10662152251353/50000000000000 : ℝ)^6247
        have hw : |(3123005841/10000000000 : ℝ)|=(3123005841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665810059/10000000000 : ℝ)|^8295 ≤ (5878710758313/12500000000000 : ℝ)^6247
        have hw : |(5665810059/10000000000 : ℝ)|=(5665810059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909800771/10000000000 : ℝ)*x 0 + (601080431/1250000000 : ℝ)*x 1 + (6029204157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909800771/10000000000 : ℝ)^8295 ≤ (2774655677747/25000000000000 : ℝ)^6247 := by
    have hnat : (1909800771 : ℕ)^8295*25000000000000^6247 ≤ 2774655677747^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909800771 10000000000 2774655677747 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601080431/1250000000 : ℝ)^8295 ≤ (37824891971311/100000000000000 : ℝ)^6247 := by
    have hnat : (601080431 : ℕ)^8295*100000000000000^6247 ≤ 37824891971311^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601080431 1250000000 37824891971311 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6029204157/10000000000 : ℝ)^8295 ≤ (51076485295053/100000000000000 : ℝ)^6247 := by
    have hnat : (6029204157 : ℕ)^8295*100000000000000^6247 ≤ 51076485295053^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029204157 10000000000 51076485295053 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909800771/10000000000 : ℝ), (601080431/1250000000 : ℝ), (6029204157/10000000000 : ℝ)] ![(2774655677747/25000000000000 : ℝ), (37824891971311/100000000000000 : ℝ), (51076485295053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909800771/10000000000 : ℝ)|^8295 ≤ (2774655677747/25000000000000 : ℝ)^6247
        have hw : |(-1909800771/10000000000 : ℝ)|=(1909800771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601080431/1250000000 : ℝ)|^8295 ≤ (37824891971311/100000000000000 : ℝ)^6247
        have hw : |(601080431/1250000000 : ℝ)|=(601080431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6029204157/10000000000 : ℝ)|^8295 ≤ (51076485295053/100000000000000 : ℝ)^6247
        have hw : |(6029204157/10000000000 : ℝ)|=(6029204157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169207991/10000000000 : ℝ)*x 0 + (-278235827/2000000000 : ℝ)*x 1 + (60292051/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169207991/10000000000 : ℝ)^8295 ≤ (41636449599047/100000000000000 : ℝ)^6247 := by
    have hnat : (5169207991 : ℕ)^8295*100000000000000^6247 ≤ 41636449599047^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169207991 10000000000 41636449599047 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278235827/2000000000 : ℝ)^8295 ≤ (7287054475647/100000000000000 : ℝ)^6247 := by
    have hnat : (278235827 : ℕ)^8295*100000000000000^6247 ≤ 7287054475647^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278235827 2000000000 7287054475647 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60292051/100000000 : ℝ)^8295 ≤ (6384561987833/12500000000000 : ℝ)^6247 := by
    have hnat : (60292051 : ℕ)^8295*12500000000000^6247 ≤ 6384561987833^6247*100000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60292051 100000000 6384561987833 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169207991/10000000000 : ℝ), (-278235827/2000000000 : ℝ), (60292051/100000000 : ℝ)] ![(41636449599047/100000000000000 : ℝ), (7287054475647/100000000000000 : ℝ), (6384561987833/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169207991/10000000000 : ℝ)|^8295 ≤ (41636449599047/100000000000000 : ℝ)^6247
        have hw : |(5169207991/10000000000 : ℝ)|=(5169207991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278235827/2000000000 : ℝ)|^8295 ≤ (7287054475647/100000000000000 : ℝ)^6247
        have hw : |(-278235827/2000000000 : ℝ)|=(278235827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60292051/100000000 : ℝ)|^8295 ≤ (6384561987833/12500000000000 : ℝ)^6247
        have hw : |(60292051/100000000 : ℝ)|=(60292051/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169209643/10000000000 : ℝ)*x 0 + (47103161/78125000 : ℝ)*x 1 + (-139117739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169209643/10000000000 : ℝ)^8295 ≤ (10409116816937/25000000000000 : ℝ)^6247 := by
    have hnat : (5169209643 : ℕ)^8295*25000000000000^6247 ≤ 10409116816937^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169209643 10000000000 10409116816937 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47103161/78125000 : ℝ)^8295 ≤ (25538245184129/50000000000000 : ℝ)^6247 := by
    have hnat : (47103161 : ℕ)^8295*50000000000000^6247 ≤ 25538245184129^6247*78125000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47103161 78125000 25538245184129 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139117739/1000000000 : ℝ)^8295 ≤ (7287042338707/100000000000000 : ℝ)^6247 := by
    have hnat : (139117739 : ℕ)^8295*100000000000000^6247 ≤ 7287042338707^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139117739 1000000000 7287042338707 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169209643/10000000000 : ℝ), (47103161/78125000 : ℝ), (-139117739/1000000000 : ℝ)] ![(10409116816937/25000000000000 : ℝ), (25538245184129/50000000000000 : ℝ), (7287042338707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169209643/10000000000 : ℝ)|^8295 ≤ (10409116816937/25000000000000 : ℝ)^6247
        have hw : |(5169209643/10000000000 : ℝ)|=(5169209643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47103161/78125000 : ℝ)|^8295 ≤ (25538245184129/50000000000000 : ℝ)^6247
        have hw : |(47103161/78125000 : ℝ)|=(47103161/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139117739/1000000000 : ℝ)|^8295 ≤ (7287042338707/100000000000000 : ℝ)^6247
        have hw : |(-139117739/1000000000 : ℝ)|=(139117739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s0_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2107317829/5000000000 : ℝ)*x 0 + (350011173/625000000 : ℝ)*x 1 + (1595469483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107317829/5000000000 : ℝ)^8295 ≤ (15874949850953/50000000000000 : ℝ)^6247 := by
    have hnat : (2107317829 : ℕ)^8295*50000000000000^6247 ≤ 15874949850953^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107317829 5000000000 15874949850953 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350011173/625000000 : ℝ)^8295 ≤ (23153842094737/50000000000000 : ℝ)^6247 := by
    have hnat : (350011173 : ℕ)^8295*50000000000000^6247 ≤ 23153842094737^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350011173 625000000 23153842094737 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595469483/5000000000 : ℝ)^8295 ≤ (10971208045893/50000000000000 : ℝ)^6247 := by
    have hnat : (1595469483 : ℕ)^8295*50000000000000^6247 ≤ 10971208045893^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595469483 5000000000 10971208045893 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107317829/5000000000 : ℝ), (350011173/625000000 : ℝ), (1595469483/5000000000 : ℝ)] ![(15874949850953/50000000000000 : ℝ), (23153842094737/50000000000000 : ℝ), (10971208045893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107317829/5000000000 : ℝ)|^8295 ≤ (15874949850953/50000000000000 : ℝ)^6247
        have hw : |(2107317829/5000000000 : ℝ)|=(2107317829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350011173/625000000 : ℝ)|^8295 ≤ (23153842094737/50000000000000 : ℝ)^6247
        have hw : |(350011173/625000000 : ℝ)|=(350011173/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595469483/5000000000 : ℝ)|^8295 ≤ (10971208045893/50000000000000 : ℝ)^6247
        have hw : |(1595469483/5000000000 : ℝ)|=(1595469483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (31/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27969/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4147/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4147 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4147*1^1024 ≤ 0^1024*1^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4147/1024 : ℝ) ≤ (489159714897188237/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4147 ≤ (489159714897188237/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4147*20000000000000000000^1024 ≤ 489159714897188237^1024*5^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 489159714897188237 20000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (489159714897188237/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4147 := by
      have hnat : (1 : ℕ)^1024*1^4147 ≤ 1^4147*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20489159714897188237/20000000000000000000 : ℝ) ≤ (1005984463852661/1000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (20489159714897188237/20000000000000000000 : ℝ)^1024 ≤ (1005984463852661/1000000000000000 : ℝ)^4147 := by
      have hnat : (20489159714897188237 : ℕ)^1024*1000000000000000^4147 ≤ 1005984463852661^4147*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20489159714897188237 20000000000000000000 1005984463852661 1000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005984463852661/1000000000000000 : ℝ)) (X := (20489159714897188237/20000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10489159714897188237/10000000000000000000 : ℝ) ≤ (505984463852661/500000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (10489159714897188237/10000000000000000000 : ℝ)^1024 ≤ (505984463852661/500000000000000 : ℝ)^4147 := by
      have hnat : (10489159714897188237 : ℕ)^1024*500000000000000^4147 ≤ 505984463852661^4147*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10489159714897188237 10000000000000000000 505984463852661 500000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505984463852661/500000000000000 : ℝ)) (X := (10489159714897188237/10000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5984463852661/400000000000000 : ℝ)*(0 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5984463852661/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(489159714897188237/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5984463852661/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5984463852661/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005984463852661/1000000000000000 : ℝ) by norm_num, show 1+(489159714897188237/20000000000000000000 : ℝ)+(0 : ℝ)=(20489159714897188237/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(489159714897188237/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5984463852661/400000000000000 : ℝ)*(2/5 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5984463852661/400000000000000 : ℝ)*(2/5 : ℝ)=(505984463852661/500000000000000 : ℝ) by norm_num, show 1+2*(489159714897188237/20000000000000000000 : ℝ)=(10489159714897188237/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5984463852661/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5984463852661/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5984463852661/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5984463852661/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5984463852661/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5984463852661/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-952267313/5000000000 : ℝ)*X 0 0+(6063621371/10000000000 : ℝ)*X 0 1+(4775393421/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2759523739/5000000000 : ℝ)*X 1 0+(-2644989661/10000000000 : ℝ)*X 1 1+(4775391383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689880891/1250000000 : ℝ)*X 2 0+(238769601/500000000 : ℝ)*X 2 1+(-1322494667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((420424547/1000000000 : ℝ)*X 0 0+(3123005841/10000000000 : ℝ)*X 0 1+(5665810059/10000000000 : ℝ)*X 0 2+(420424547/1000000000 : ℝ)*X 1 0+(3123005841/10000000000 : ℝ)*X 1 1+(5665810059/10000000000 : ℝ)*X 1 2+(420424547/1000000000 : ℝ)*X 2 0+(3123005841/10000000000 : ℝ)*X 2 1+(5665810059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1909800771/10000000000 : ℝ)*X 0 0+(601080431/1250000000 : ℝ)*X 0 1+(6029204157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169207991/10000000000 : ℝ)*X 1 0+(-278235827/2000000000 : ℝ)*X 1 1+(60292051/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169209643/10000000000 : ℝ)*X 2 0+(47103161/78125000 : ℝ)*X 2 1+(-139117739/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2107317829/5000000000 : ℝ)*X 0 0+(350011173/625000000 : ℝ)*X 0 1+(1595469483/5000000000 : ℝ)*X 0 2+(2107317829/5000000000 : ℝ)*X 1 0+(350011173/625000000 : ℝ)*X 1 1+(1595469483/5000000000 : ℝ)*X 1 2+(2107317829/5000000000 : ℝ)*X 2 0+(350011173/625000000 : ℝ)*X 2 1+(1595469483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15677634082735264856067/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125363099/100000000000000 : ℝ)*(base1) + (660353527/100000000000000 : ℝ)*(base19) + (580110641/100000000000000 : ℝ)*(base23) + (15507473/50000000000000 : ℝ)*(base24) + (21615621/50000000000000 : ℝ)*(upper3) + (584764578530349/100000000000000 : ℝ)*(major0) + (584764578530349/100000000000000 : ℝ)*(major1) + (584764578530349/100000000000000 : ℝ)*(major2) + (388130522374721/50000000000000 : ℝ)*(sp0) + (194065231668777/25000000000000 : ℝ)*(sp1) + (776260975903049/100000000000000 : ℝ)*(sp2) + (49158364582917/12500000000000 : ℝ)*(sp3) + (166910573/25000000000000 : ℝ)*(sp4) + (211744031/50000000000000 : ℝ)*(sp7) + (393267465514497/100000000000000 : ℝ)*(f.failure) + (155252317405727/20000000000000 : ℝ)*(f.sum) + (40510484931311/20000000000000000000000000000 : ℝ)*base66 + (212035786691311/40000000000000000000000000000 : ℝ)*base68 + (51040132771311/40000000000000000000000000000 : ℝ)*base70 + (280473360691311/40000000000000000000000000000 : ℝ)*base72 + (23865243171311/20000000000000000000000000000 : ℝ)*base74 + (104966750291311/40000000000000000000000000000 : ℝ)*base76 + (362757986611311/40000000000000000000000000000 : ℝ)*base78 + (436165433971311/40000000000000000000000000000 : ℝ)*base80 + (80785025908689/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10402917/10000000000000000000000 : ℝ)*base89 + (10402917/10000000000000000000000 : ℝ)*base91 + (10402917/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18097365147348828766341/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173532023/100000000000000 : ℝ)*(base19) + (30081749/3125000000000 : ℝ)*(base23) + (512255399/100000000000000 : ℝ)*(base39) + (20379591/20000000000000 : ℝ)*(base45) + (22133659/50000000000000 : ℝ)*(upper3) + (132909747/50000000000000 : ℝ)*(upper5) + (617180391201969/100000000000000 : ℝ)*(major0) + (617180391201969/100000000000000 : ℝ)*(major1) + (61717987894657/10000000000000 : ℝ)*(major2) + (44064323/10000000000000 : ℝ)*(sp2) + (819292313442659/100000000000000 : ℝ)*(sp4) + (163858427982127/20000000000000 : ℝ)*(sp5) + (40964571121943/5000000000000 : ℝ)*(sp6) + (16602713442271/4000000000000 : ℝ)*(sp7) + (16602713442271/4000000000000 : ℝ)*(f.failure) + (819292825698057/100000000000000 : ℝ)*(f.sum) + (70254965972279/40000000000000000000000000000 : ℝ)*base65 + (10895968595723/4000000000000000000000000000 : ℝ)*base68 + (391838815430491/40000000000000000000000000000 : ℝ)*base70 + (1991031807723/4000000000000000000000000000 : ℝ)*base72 + (2383418587721/40000000000000000000000000000 : ℝ)*base74 + (109668983089509/40000000000000000000000000000 : ℝ)*base75 + (110311825710491/40000000000000000000000000000 : ℝ)*base78 + (150123478110491/40000000000000000000000000000 : ℝ)*base80 + (21391899510491/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (401669/400000000000000000000 : ℝ)*base90 + (401669/400000000000000000000 : ℝ)*base92 + (401669/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1102_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (31/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27969/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1102_s1_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056043267/5000000000 : ℝ)*x 0 + (285616489/500000000 : ℝ)*x 1 + (624223909/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056043267/5000000000 : ℝ)^8295 ≤ (3171516564439/25000000000000 : ℝ)^6247 := by
    have hnat : (1056043267 : ℕ)^8295*25000000000000^6247 ≤ 3171516564439^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056043267 5000000000 3171516564439 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285616489/500000000 : ℝ)^8295 ≤ (47543108801437/100000000000000 : ℝ)^6247 := by
    have hnat : (285616489 : ℕ)^8295*100000000000000^6247 ≤ 47543108801437^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285616489 500000000 47543108801437 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624223909/1250000000 : ℝ)^8295 ≤ (19885412465599/50000000000000 : ℝ)^6247 := by
    have hnat : (624223909 : ℕ)^8295*50000000000000^6247 ≤ 19885412465599^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624223909 1250000000 19885412465599 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056043267/5000000000 : ℝ), (285616489/500000000 : ℝ), (624223909/1250000000 : ℝ)] ![(3171516564439/25000000000000 : ℝ), (47543108801437/100000000000000 : ℝ), (19885412465599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056043267/5000000000 : ℝ)|^8295 ≤ (3171516564439/25000000000000 : ℝ)^6247
        have hw : |(-1056043267/5000000000 : ℝ)|=(1056043267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285616489/500000000 : ℝ)|^8295 ≤ (47543108801437/100000000000000 : ℝ)^6247
        have hw : |(285616489/500000000 : ℝ)|=(285616489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624223909/1250000000 : ℝ)|^8295 ≤ (19885412465599/50000000000000 : ℝ)^6247
        have hw : |(624223909/1250000000 : ℝ)|=(624223909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421323099/10000000000 : ℝ)*x 0 + (-1250324921/5000000000 : ℝ)*x 1 + (2496895683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421323099/10000000000 : ℝ)^8295 ≤ (2217711637509/5000000000000 : ℝ)^6247 := by
    have hnat : (5421323099 : ℕ)^8295*5000000000000^6247 ≤ 2217711637509^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421323099 10000000000 2217711637509 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250324921/5000000000 : ℝ)^8295 ≤ (15874941307373/100000000000000 : ℝ)^6247 := by
    have hnat : (1250324921 : ℕ)^8295*100000000000000^6247 ≤ 15874941307373^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250324921 5000000000 15874941307373 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2496895683/5000000000 : ℝ)^8295 ≤ (7954165185049/20000000000000 : ℝ)^6247 := by
    have hnat : (2496895683 : ℕ)^8295*20000000000000^6247 ≤ 7954165185049^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496895683 5000000000 7954165185049 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421323099/10000000000 : ℝ), (-1250324921/5000000000 : ℝ), (2496895683/5000000000 : ℝ)] ![(2217711637509/5000000000000 : ℝ), (15874941307373/100000000000000 : ℝ), (7954165185049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421323099/10000000000 : ℝ)|^8295 ≤ (2217711637509/5000000000000 : ℝ)^6247
        have hw : |(5421323099/10000000000 : ℝ)|=(5421323099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1250324921/5000000000 : ℝ)|^8295 ≤ (15874941307373/100000000000000 : ℝ)^6247
        have hw : |(-1250324921/5000000000 : ℝ)|=(1250324921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2496895683/5000000000 : ℝ)|^8295 ≤ (7954165185049/20000000000000 : ℝ)^6247
        have hw : |(2496895683/5000000000 : ℝ)|=(2496895683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (677665527/1250000000 : ℝ)*x 0 + (199751611/400000000 : ℝ)*x 1 + (-2500649771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677665527/1250000000 : ℝ)^8295 ≤ (44354244884847/100000000000000 : ℝ)^6247 := by
    have hnat : (677665527 : ℕ)^8295*100000000000000^6247 ≤ 44354244884847^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677665527 1250000000 44354244884847 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199751611/400000000 : ℝ)^8295 ≤ (19885407193977/50000000000000 : ℝ)^6247 := by
    have hnat : (199751611 : ℕ)^8295*50000000000000^6247 ≤ 19885407193977^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199751611 400000000 19885407193977 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2500649771/10000000000 : ℝ)^8295 ≤ (126999525671/800000000000 : ℝ)^6247 := by
    have hnat : (2500649771 : ℕ)^8295*800000000000^6247 ≤ 126999525671^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500649771 10000000000 126999525671 800000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677665527/1250000000 : ℝ), (199751611/400000000 : ℝ), (-2500649771/10000000000 : ℝ)] ![(44354244884847/100000000000000 : ℝ), (19885407193977/50000000000000 : ℝ), (126999525671/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677665527/1250000000 : ℝ)|^8295 ≤ (44354244884847/100000000000000 : ℝ)^6247
        have hw : |(677665527/1250000000 : ℝ)|=(677665527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199751611/400000000 : ℝ)|^8295 ≤ (19885407193977/50000000000000 : ℝ)^6247
        have hw : |(199751611/400000000 : ℝ)|=(199751611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2500649771/10000000000 : ℝ)|^8295 ≤ (126999525671/800000000000 : ℝ)^6247
        have hw : |(-2500649771/10000000000 : ℝ)|=(2500649771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4320808079/10000000000 : ℝ)*x 0 + (366947649/1000000000 : ℝ)*x 1 + (2543890869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320808079/10000000000 : ℝ)^8295 ≤ (32816295940501/100000000000000 : ℝ)^6247 := by
    have hnat : (4320808079 : ℕ)^8295*100000000000000^6247 ≤ 32816295940501^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320808079 10000000000 32816295940501 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366947649/1000000000 : ℝ)^8295 ≤ (13207939586291/50000000000000 : ℝ)^6247 := by
    have hnat : (366947649 : ℕ)^8295*50000000000000^6247 ≤ 13207939586291^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366947649 1000000000 13207939586291 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2543890869/5000000000 : ℝ)^8295 ≤ (40767824865353/100000000000000 : ℝ)^6247 := by
    have hnat : (2543890869 : ℕ)^8295*100000000000000^6247 ≤ 40767824865353^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543890869 5000000000 40767824865353 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320808079/10000000000 : ℝ), (366947649/1000000000 : ℝ), (2543890869/5000000000 : ℝ)] ![(32816295940501/100000000000000 : ℝ), (13207939586291/50000000000000 : ℝ), (40767824865353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320808079/10000000000 : ℝ)|^8295 ≤ (32816295940501/100000000000000 : ℝ)^6247
        have hw : |(4320808079/10000000000 : ℝ)|=(4320808079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(366947649/1000000000 : ℝ)|^8295 ≤ (13207939586291/50000000000000 : ℝ)^6247
        have hw : |(366947649/1000000000 : ℝ)|=(366947649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2543890869/5000000000 : ℝ)|^8295 ≤ (40767824865353/100000000000000 : ℝ)^6247
        have hw : |(2543890869/5000000000 : ℝ)|=(2543890869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112950129/10000000000 : ℝ)*x 0 + (5003753079/10000000000 : ℝ)*x 1 + (5702168117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112950129/10000000000 : ℝ)^8295 ≤ (12692954356679/100000000000000 : ℝ)^6247 := by
    have hnat : (2112950129 : ℕ)^8295*100000000000000^6247 ≤ 12692954356679^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112950129 10000000000 12692954356679 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003753079/10000000000 : ℝ)^8295 ≤ (7975241032383/20000000000000 : ℝ)^6247 := by
    have hnat : (5003753079 : ℕ)^8295*20000000000000^6247 ≤ 7975241032383^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003753079 10000000000 7975241032383 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5702168117/10000000000 : ℝ)^8295 ≤ (2371542023477/5000000000000 : ℝ)^6247 := by
    have hnat : (5702168117 : ℕ)^8295*5000000000000^6247 ≤ 2371542023477^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5702168117 10000000000 2371542023477 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112950129/10000000000 : ℝ), (5003753079/10000000000 : ℝ), (5702168117/10000000000 : ℝ)] ![(12692954356679/100000000000000 : ℝ), (7975241032383/20000000000000 : ℝ), (2371542023477/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112950129/10000000000 : ℝ)|^8295 ≤ (12692954356679/100000000000000 : ℝ)^6247
        have hw : |(-2112950129/10000000000 : ℝ)|=(2112950129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003753079/10000000000 : ℝ)|^8295 ≤ (7975241032383/20000000000000 : ℝ)^6247
        have hw : |(5003753079/10000000000 : ℝ)|=(5003753079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5702168117/10000000000 : ℝ)|^8295 ≤ (2371542023477/5000000000000 : ℝ)^6247
        have hw : |(5702168117/10000000000 : ℝ)|=(5702168117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237476189/10000000000 : ℝ)*x 0 + (-224034097/1250000000 : ℝ)*x 1 + (285108397/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237476189/10000000000 : ℝ)^8295 ≤ (2118408856971/5000000000000 : ℝ)^6247 := by
    have hnat : (5237476189 : ℕ)^8295*5000000000000^6247 ≤ 2118408856971^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237476189 10000000000 2118408856971 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224034097/1250000000 : ℝ)^8295 ≤ (2550246082377/25000000000000 : ℝ)^6247 := by
    have hnat : (224034097 : ℕ)^8295*25000000000000^6247 ≤ 2550246082377^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224034097 1250000000 2550246082377 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285108397/500000000 : ℝ)^8295 ≤ (1897233540583/4000000000000 : ℝ)^6247 := by
    have hnat : (285108397 : ℕ)^8295*4000000000000^6247 ≤ 1897233540583^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285108397 500000000 1897233540583 4000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237476189/10000000000 : ℝ), (-224034097/1250000000 : ℝ), (285108397/500000000 : ℝ)] ![(2118408856971/5000000000000 : ℝ), (2550246082377/25000000000000 : ℝ), (1897233540583/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237476189/10000000000 : ℝ)|^8295 ≤ (2118408856971/5000000000000 : ℝ)^6247
        have hw : |(5237476189/10000000000 : ℝ)|=(5237476189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224034097/1250000000 : ℝ)|^8295 ≤ (2550246082377/25000000000000 : ℝ)^6247
        have hw : |(-224034097/1250000000 : ℝ)|=(224034097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285108397/500000000 : ℝ)|^8295 ≤ (1897233540583/4000000000000 : ℝ)^6247
        have hw : |(285108397/500000000 : ℝ)|=(285108397/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309369053/2500000000 : ℝ)*x 0 + (712771009/1250000000 : ℝ)*x 1 + (-35845451/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309369053/2500000000 : ℝ)^8295 ≤ (42368177386473/100000000000000 : ℝ)^6247 := by
    have hnat : (1309369053 : ℕ)^8295*100000000000000^6247 ≤ 42368177386473^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309369053 2500000000 42368177386473 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712771009/1250000000 : ℝ)^8295 ≤ (9486167994503/20000000000000 : ℝ)^6247 := by
    have hnat : (712771009 : ℕ)^8295*20000000000000^6247 ≤ 9486167994503^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712771009 1250000000 9486167994503 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35845451/200000000 : ℝ)^8295 ≤ (5100491310747/50000000000000 : ℝ)^6247 := by
    have hnat : (35845451 : ℕ)^8295*50000000000000^6247 ≤ 5100491310747^6247*200000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35845451 200000000 5100491310747 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309369053/2500000000 : ℝ), (712771009/1250000000 : ℝ), (-35845451/200000000 : ℝ)] ![(42368177386473/100000000000000 : ℝ), (9486167994503/20000000000000 : ℝ), (5100491310747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309369053/2500000000 : ℝ)|^8295 ≤ (42368177386473/100000000000000 : ℝ)^6247
        have hw : |(1309369053/2500000000 : ℝ)|=(1309369053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(712771009/1250000000 : ℝ)|^8295 ≤ (9486167994503/20000000000000 : ℝ)^6247
        have hw : |(712771009/1250000000 : ℝ)|=(712771009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35845451/200000000 : ℝ)|^8295 ≤ (5100491310747/50000000000000 : ℝ)^6247
        have hw : |(-35845451/200000000 : ℝ)|=(35845451/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s1_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (540313937/1250000000 : ℝ)*x 0 + (50681191/100000000 : ℝ)*x 1 + (147581343/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540313937/1250000000 : ℝ)^8295 ≤ (8208368939111/25000000000000 : ℝ)^6247 := by
    have hnat : (540313937 : ℕ)^8295*25000000000000^6247 ≤ 8208368939111^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540313937 1250000000 8208368939111 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50681191/100000000 : ℝ)^8295 ≤ (40558750740211/100000000000000 : ℝ)^6247 := by
    have hnat : (50681191 : ℕ)^8295*100000000000000^6247 ≤ 40558750740211^6247*100000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50681191 100000000 40558750740211 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147581343/400000000 : ℝ)^8295 ≤ (26607773494237/100000000000000 : ℝ)^6247 := by
    have hnat : (147581343 : ℕ)^8295*100000000000000^6247 ≤ 26607773494237^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147581343 400000000 26607773494237 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540313937/1250000000 : ℝ), (50681191/100000000 : ℝ), (147581343/400000000 : ℝ)] ![(8208368939111/25000000000000 : ℝ), (40558750740211/100000000000000 : ℝ), (26607773494237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540313937/1250000000 : ℝ)|^8295 ≤ (8208368939111/25000000000000 : ℝ)^6247
        have hw : |(540313937/1250000000 : ℝ)|=(540313937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50681191/100000000 : ℝ)|^8295 ≤ (40558750740211/100000000000000 : ℝ)^6247
        have hw : |(50681191/100000000 : ℝ)|=(50681191/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147581343/400000000 : ℝ)|^8295 ≤ (26607773494237/100000000000000 : ℝ)^6247
        have hw : |(147581343/400000000 : ℝ)|=(147581343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5423/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20621/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (31/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (31/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (31/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (31/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (31/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (31/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (31/12500 : ℝ) ^ (4147/1024 : ℝ) ≤ (1402840217/50000000000000000000 : ℝ) := by
    have hpowers : (31/12500 : ℝ)^4147 ≤ (1402840217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (31 : ℕ)^4147*50000000000000000000^1024 ≤ 1402840217^1024*12500^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31 12500 1402840217 50000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31/12500 : ℝ)) (X := (1402840217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27969/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (287157178823997341/50000000000000000000 : ℝ) := by
    have hpowers : (27969/100000 : ℝ)^4147 ≤ (287157178823997341/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27969 : ℕ)^4147*50000000000000000000^1024 ≤ 287157178823997341^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27969 100000 287157178823997341 50000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27969/100000 : ℝ)) (X := (287157178823997341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000001402840217/25000000000000000000 : ℝ) ≤ (10000000000138559/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (25000000001402840217/25000000000000000000 : ℝ)^1024 ≤ (10000000000138559/10000000000000000 : ℝ)^4147 := by
      have hnat : (25000000001402840217 : ℕ)^1024*10000000000000000^4147 ≤ 10000000000138559^4147*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000001402840217 25000000000000000000 10000000000138559 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000138559/10000000000000000 : ℝ)) (X := (25000000001402840217/25000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25143578590113418779/25000000000000000000 : ℝ) ≤ (250353768019213/250000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (25143578590113418779/25000000000000000000 : ℝ)^1024 ≤ (250353768019213/250000000000000 : ℝ)^4147 := by
      have hnat : (25143578590113418779 : ℕ)^1024*250000000000000^4147 ≤ 250353768019213^4147*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25143578590113418779 25000000000000000000 250353768019213 250000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250353768019213/250000000000000 : ℝ)) (X := (25143578590113418779/25000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25287157178823997341/25000000000000000000 : ℝ) ≤ (10028301441398481/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (25287157178823997341/25000000000000000000 : ℝ)^1024 ≤ (10028301441398481/10000000000000000 : ℝ)^4147 := by
      have hnat : (25287157178823997341 : ℕ)^1024*10000000000000000^4147 ≤ 10028301441398481^4147*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25287157178823997341 25000000000000000000 10028301441398481 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028301441398481/10000000000000000 : ℝ)) (X := (25287157178823997341/25000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1402840217/50000000000000000000 : ℝ) ≤ ((277202981246408533383/277210000000000000000 : ℝ)+2*(14150720629961/2772100000000000 : ℝ)*(31/12500 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (277202981246408533383/277210000000000000000 : ℝ)+2*(14150720629961/2772100000000000 : ℝ)*(31/12500 : ℝ)=(10000000000138559/10000000000000000 : ℝ) by norm_num, show 1+2*(1402840217/50000000000000000000 : ℝ)=(25000000001402840217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(287157178823997341/50000000000000000000 : ℝ)+(1402840217/50000000000000000000 : ℝ) ≤ ((277202981246408533383/277210000000000000000 : ℝ)+(14150720629961/2772100000000000 : ℝ)*((27969/100000 : ℝ)+(31/12500 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (277202981246408533383/277210000000000000000 : ℝ)+(14150720629961/2772100000000000 : ℝ)*((27969/100000 : ℝ)+(31/12500 : ℝ))=(250353768019213/250000000000000 : ℝ) by norm_num, show 1+(287157178823997341/50000000000000000000 : ℝ)+(1402840217/50000000000000000000 : ℝ)=(25143578590113418779/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(287157178823997341/50000000000000000000 : ℝ) ≤ ((277202981246408533383/277210000000000000000 : ℝ)+2*(14150720629961/2772100000000000 : ℝ)*(27969/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (277202981246408533383/277210000000000000000 : ℝ)+2*(14150720629961/2772100000000000 : ℝ)*(27969/100000 : ℝ)=(10028301441398481/10000000000000000 : ℝ) by norm_num, show 1+2*(287157178823997341/50000000000000000000 : ℝ)=(25287157178823997341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (277202981246408533383/277210000000000000000 : ℝ)*(X 1 0+X 2 0)+(14150720629961/2772100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (31/12500 : ℝ)) (hi := (27969/100000 : ℝ)) (c := (277202981246408533383/277210000000000000000 : ℝ)) (alpha := (14150720629961/2772100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (277202981246408533383/277210000000000000000 : ℝ)*(X 0 1+X 2 1)+(14150720629961/2772100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (31/12500 : ℝ)) (hi := (27969/100000 : ℝ)) (c := (277202981246408533383/277210000000000000000 : ℝ)) (alpha := (14150720629961/2772100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (277202981246408533383/277210000000000000000 : ℝ)*(X 0 2+X 1 2)+(14150720629961/2772100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (31/12500 : ℝ)) (hi := (27969/100000 : ℝ)) (c := (277202981246408533383/277210000000000000000 : ℝ)) (alpha := (14150720629961/2772100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056043267/5000000000 : ℝ)*X 0 0+(285616489/500000000 : ℝ)*X 0 1+(624223909/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421323099/10000000000 : ℝ)*X 1 0+(-1250324921/5000000000 : ℝ)*X 1 1+(2496895683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677665527/1250000000 : ℝ)*X 2 0+(199751611/400000000 : ℝ)*X 2 1+(-2500649771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320808079/10000000000 : ℝ)*X 0 0+(366947649/1000000000 : ℝ)*X 0 1+(2543890869/5000000000 : ℝ)*X 0 2+(4320808079/10000000000 : ℝ)*X 1 0+(366947649/1000000000 : ℝ)*X 1 1+(2543890869/5000000000 : ℝ)*X 1 2+(4320808079/10000000000 : ℝ)*X 2 0+(366947649/1000000000 : ℝ)*X 2 1+(2543890869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2112950129/10000000000 : ℝ)*X 0 0+(5003753079/10000000000 : ℝ)*X 0 1+(5702168117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5237476189/10000000000 : ℝ)*X 1 0+(-224034097/1250000000 : ℝ)*X 1 1+(285108397/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1309369053/2500000000 : ℝ)*X 2 0+(712771009/1250000000 : ℝ)*X 2 1+(-35845451/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540313937/1250000000 : ℝ)*X 0 0+(50681191/100000000 : ℝ)*X 0 1+(147581343/400000000 : ℝ)*X 0 2+(540313937/1250000000 : ℝ)*X 1 0+(50681191/100000000 : ℝ)*X 1 1+(147581343/400000000 : ℝ)*X 1 2+(540313937/1250000000 : ℝ)*X 2 0+(50681191/100000000 : ℝ)*X 2 1+(147581343/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (481602864472312401110571/138605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2761883/1562500000000 : ℝ)*(base1) + (289806143/50000000000000 : ℝ)*(base19) + (866359269/100000000000000 : ℝ)*(base23) + (1160017/25000000000000 : ℝ)*(upper3) + (21280849/20000000000000 : ℝ)*(upper5) + (262098294303529/25000000000000 : ℝ)*(major0) + (262098294303529/25000000000000 : ℝ)*(major1) + (262098294303529/25000000000000 : ℝ)*(major2) + (695857606915001/50000000000000 : ℝ)*(sp0) + (1391717426746437/100000000000000 : ℝ)*(sp1) + (695858569999727/50000000000000 : ℝ)*(sp2) + (352533755741899/50000000000000 : ℝ)*(sp3) + (2969289233/100000000000000 : ℝ)*(sp4) + (544003769/100000000000000 : ℝ)*(sp7) + (705068232248079/100000000000000 : ℝ)*(f.failure) + (1391718006358723/100000000000000 : ℝ)*(f.sum) + (443759869775171/138605000000000000000000000000 : ℝ)*base65 + (21965056328063641393/6930250000000000000000000000000000 : ℝ)*base68 + (14583716794872108607/6930250000000000000000000000000000 : ℝ)*base69 + (3718964105415858607/6930250000000000000000000000000000 : ℝ)*base71 + (200472002811023/69302500000000000000000000000 : ℝ)*base73 + (1484318268572141393/6930250000000000000000000000000000 : ℝ)*base76 + (16191157647964391393/6930250000000000000000000000000000 : ℝ)*base78 + (1991765334775608607/6930250000000000000000000000000000 : ℝ)*base79 + (1211171162220151/138605000000000000000000000000 : ℝ)*base81 + (23656981/10000000000000000000000 : ℝ)*base90 + (23656981/10000000000000000000000 : ℝ)*base92 + (23656981/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91649967406391351513480335389/13860500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78521337/100000000000000 : ℝ)*(base1) + (295711477/20000000000000 : ℝ)*(base19) + (150066787/10000000000000 : ℝ)*(base23) + (2958887/2000000000000 : ℝ)*(upper3) + (149147693/100000000000000 : ℝ)*(upper5) + (1078597440221239/100000000000000 : ℝ)*(major0) + (1078597440221239/100000000000000 : ℝ)*(major1) + (1078597440221239/100000000000000 : ℝ)*(major2) + (1473077723/25000000000000 : ℝ)*(sp1) + (6343036597/100000000000000 : ℝ)*(sp2) + (1431813453161069/100000000000000 : ℝ)*(sp4) + (22371968808929/1562500000000 : ℝ)*(sp5) + (286361106187053/20000000000000 : ℝ)*(sp6) + (362690603435481/50000000000000 : ℝ)*(sp7) + (7253812853923/1000000000000 : ℝ)*(f.failure) + (357953343659933/25000000000000 : ℝ)*(f.sum) + (36629388412103/17325625000000000000000000000 : ℝ)*base65 + (63142270809834021537/27721000000000000000000000000000000 : ℝ)*base67 + (51138230323422021537/27721000000000000000000000000000000 : ℝ)*base69 + (80898234955118978463/27721000000000000000000000000000000 : ℝ)*base72 + (638721240267279/138605000000000000000000000000 : ℝ)*base73 + (38407309239696978463/27721000000000000000000000000000000 : ℝ)*base76 + (14656228350441021537/27721000000000000000000000000000000 : ℝ)*base77 + (141928906531150021537/27721000000000000000000000000000000 : ℝ)*base79 + (233828109929657/69302500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (866703/100000000000000000000 : ℝ)*base89 + (866703/100000000000000000000 : ℝ)*base91 + (866703/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1102_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1102_s2_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-433499067/2000000000 : ℝ)*x 0 + (5518590281/10000000000 : ℝ)*x 1 + (1288084767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433499067/2000000000 : ℝ)^8295 ≤ (2625974145267/20000000000000 : ℝ)^6247 := by
    have hnat : (433499067 : ℕ)^8295*20000000000000^6247 ≤ 2625974145267^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433499067 2000000000 2625974145267 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518590281/10000000000 : ℝ)^8295 ≤ (45414001932547/100000000000000 : ℝ)^6247 := by
    have hnat : (5518590281 : ℕ)^8295*100000000000000^6247 ≤ 45414001932547^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518590281 10000000000 45414001932547 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288084767/2500000000 : ℝ)^8295 ≤ (20728063662423/50000000000000 : ℝ)^6247 := by
    have hnat : (1288084767 : ℕ)^8295*50000000000000^6247 ≤ 20728063662423^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288084767 2500000000 20728063662423 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433499067/2000000000 : ℝ), (5518590281/10000000000 : ℝ), (1288084767/2500000000 : ℝ)] ![(2625974145267/20000000000000 : ℝ), (45414001932547/100000000000000 : ℝ), (20728063662423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433499067/2000000000 : ℝ)|^8295 ≤ (2625974145267/20000000000000 : ℝ)^6247
        have hw : |(-433499067/2000000000 : ℝ)|=(433499067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518590281/10000000000 : ℝ)|^8295 ≤ (45414001932547/100000000000000 : ℝ)^6247
        have hw : |(5518590281/10000000000 : ℝ)|=(5518590281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288084767/2500000000 : ℝ)|^8295 ≤ (20728063662423/50000000000000 : ℝ)^6247
        have hw : |(1288084767/2500000000 : ℝ)|=(1288084767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075120549/2000000000 : ℝ)*x 0 + (-2358213951/10000000000 : ℝ)*x 1 + (322021263/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075120549/2000000000 : ℝ)^8295 ≤ (43858232008237/100000000000000 : ℝ)^6247 := by
    have hnat : (1075120549 : ℕ)^8295*100000000000000^6247 ≤ 43858232008237^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075120549 2000000000 43858232008237 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2358213951/10000000000 : ℝ)^8295 ≤ (14685628480307/100000000000000 : ℝ)^6247 := by
    have hnat : (2358213951 : ℕ)^8295*100000000000000^6247 ≤ 14685628480307^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358213951 10000000000 14685628480307 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322021263/625000000 : ℝ)^8295 ≤ (20728069752237/50000000000000 : ℝ)^6247 := by
    have hnat : (322021263 : ℕ)^8295*50000000000000^6247 ≤ 20728069752237^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322021263 625000000 20728069752237 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075120549/2000000000 : ℝ), (-2358213951/10000000000 : ℝ), (322021263/625000000 : ℝ)] ![(43858232008237/100000000000000 : ℝ), (14685628480307/100000000000000 : ℝ), (20728069752237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075120549/2000000000 : ℝ)|^8295 ≤ (43858232008237/100000000000000 : ℝ)^6247
        have hw : |(1075120549/2000000000 : ℝ)|=(1075120549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2358213951/10000000000 : ℝ)|^8295 ≤ (14685628480307/100000000000000 : ℝ)^6247
        have hw : |(-2358213951/10000000000 : ℝ)|=(2358213951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322021263/625000000 : ℝ)|^8295 ≤ (20728069752237/50000000000000 : ℝ)^6247
        have hw : |(322021263/625000000 : ℝ)|=(322021263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375602701/10000000000 : ℝ)*x 0 + (2576170129/5000000000 : ℝ)*x 1 + (-294776743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375602701/10000000000 : ℝ)^8295 ≤ (43858231531563/100000000000000 : ℝ)^6247 := by
    have hnat : (5375602701 : ℕ)^8295*100000000000000^6247 ≤ 43858231531563^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375602701 10000000000 43858231531563 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576170129/5000000000 : ℝ)^8295 ≤ (10364035009667/25000000000000 : ℝ)^6247 := by
    have hnat : (2576170129 : ℕ)^8295*25000000000000^6247 ≤ 10364035009667^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576170129 5000000000 10364035009667 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294776743/1250000000 : ℝ)^8295 ≤ (1835703552803/12500000000000 : ℝ)^6247 := by
    have hnat : (294776743 : ℕ)^8295*12500000000000^6247 ≤ 1835703552803^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294776743 1250000000 1835703552803 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375602701/10000000000 : ℝ), (2576170129/5000000000 : ℝ), (-294776743/1250000000 : ℝ)] ![(43858231531563/100000000000000 : ℝ), (10364035009667/25000000000000 : ℝ), (1835703552803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375602701/10000000000 : ℝ)|^8295 ≤ (43858231531563/100000000000000 : ℝ)^6247
        have hw : |(5375602701/10000000000 : ℝ)|=(5375602701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576170129/5000000000 : ℝ)|^8295 ≤ (10364035009667/25000000000000 : ℝ)^6247
        have hw : |(2576170129/5000000000 : ℝ)|=(2576170129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-294776743/1250000000 : ℝ)|^8295 ≤ (1835703552803/12500000000000 : ℝ)^6247
        have hw : |(-294776743/1250000000 : ℝ)|=(294776743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87174293/200000000 : ℝ)*x 0 + (401223893/1000000000 : ℝ)*x 1 + (1183792897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87174293/200000000 : ℝ)^8295 ≤ (16599563356967/50000000000000 : ℝ)^6247 := by
    have hnat : (87174293 : ℕ)^8295*50000000000000^6247 ≤ 16599563356967^6247*200000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87174293 200000000 16599563356967 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401223893/1000000000 : ℝ)^8295 ≤ (29741451376517/100000000000000 : ℝ)^6247 := by
    have hnat : (401223893 : ℕ)^8295*100000000000000^6247 ≤ 29741451376517^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401223893 1000000000 29741451376517 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183792897/2500000000 : ℝ)^8295 ≤ (2316213869039/6250000000000 : ℝ)^6247 := by
    have hnat : (1183792897 : ℕ)^8295*6250000000000^6247 ≤ 2316213869039^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183792897 2500000000 2316213869039 6250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87174293/200000000 : ℝ), (401223893/1000000000 : ℝ), (1183792897/2500000000 : ℝ)] ![(16599563356967/50000000000000 : ℝ), (29741451376517/100000000000000 : ℝ), (2316213869039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87174293/200000000 : ℝ)|^8295 ≤ (16599563356967/50000000000000 : ℝ)^6247
        have hw : |(87174293/200000000 : ℝ)|=(87174293/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401223893/1000000000 : ℝ)|^8295 ≤ (29741451376517/100000000000000 : ℝ)^6247
        have hw : |(401223893/1000000000 : ℝ)|=(401223893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183792897/2500000000 : ℝ)|^8295 ≤ (2316213869039/6250000000000 : ℝ)^6247
        have hw : |(1183792897/2500000000 : ℝ)|=(1183792897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167609373/10000000000 : ℝ)*x 0 + (5154936687/10000000000 : ℝ)*x 1 + (551596613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167609373/10000000000 : ℝ)^8295 ≤ (25646070319/195312500000 : ℝ)^6247 := by
    have hnat : (2167609373 : ℕ)^8295*195312500000^6247 ≤ 25646070319^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167609373 10000000000 25646070319 195312500000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5154936687/10000000000 : ℝ)^8295 ≤ (41483882279101/100000000000000 : ℝ)^6247 := by
    have hnat : (5154936687 : ℕ)^8295*100000000000000^6247 ≤ 41483882279101^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154936687 10000000000 41483882279101 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551596613/1000000000 : ℝ)^8295 ≤ (45385329702501/100000000000000 : ℝ)^6247 := by
    have hnat : (551596613 : ℕ)^8295*100000000000000^6247 ≤ 45385329702501^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551596613 1000000000 45385329702501 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167609373/10000000000 : ℝ), (5154936687/10000000000 : ℝ), (551596613/1000000000 : ℝ)] ![(25646070319/195312500000 : ℝ), (41483882279101/100000000000000 : ℝ), (45385329702501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167609373/10000000000 : ℝ)|^8295 ≤ (25646070319/195312500000 : ℝ)^6247
        have hw : |(-2167609373/10000000000 : ℝ)|=(2167609373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5154936687/10000000000 : ℝ)|^8295 ≤ (41483882279101/100000000000000 : ℝ)^6247
        have hw : |(5154936687/10000000000 : ℝ)|=(5154936687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551596613/1000000000 : ℝ)|^8295 ≤ (45385329702501/100000000000000 : ℝ)^6247
        have hw : |(551596613/1000000000 : ℝ)|=(551596613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641463007/5000000000 : ℝ)*x 0 + (-498646869/2500000000 : ℝ)*x 1 + (5515966217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641463007/5000000000 : ℝ)^8295 ≤ (42857066907231/100000000000000 : ℝ)^6247 := by
    have hnat : (2641463007 : ℕ)^8295*100000000000000^6247 ≤ 42857066907231^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641463007 5000000000 42857066907231 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498646869/2500000000 : ℝ)^8295 ≤ (5878801217537/50000000000000 : ℝ)^6247 := by
    have hnat : (498646869 : ℕ)^8295*50000000000000^6247 ≤ 5878801217537^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498646869 2500000000 5878801217537 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515966217/10000000000 : ℝ)^8295 ≤ (22692665326507/50000000000000 : ℝ)^6247 := by
    have hnat : (5515966217 : ℕ)^8295*50000000000000^6247 ≤ 22692665326507^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515966217 10000000000 22692665326507 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641463007/5000000000 : ℝ), (-498646869/2500000000 : ℝ), (5515966217/10000000000 : ℝ)] ![(42857066907231/100000000000000 : ℝ), (5878801217537/50000000000000 : ℝ), (22692665326507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641463007/5000000000 : ℝ)|^8295 ≤ (42857066907231/100000000000000 : ℝ)^6247
        have hw : |(2641463007/5000000000 : ℝ)|=(2641463007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498646869/2500000000 : ℝ)|^8295 ≤ (5878801217537/50000000000000 : ℝ)^6247
        have hw : |(-498646869/2500000000 : ℝ)|=(498646869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515966217/10000000000 : ℝ)|^8295 ≤ (22692665326507/50000000000000 : ℝ)^6247
        have hw : |(5515966217/10000000000 : ℝ)|=(5515966217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282926169/10000000000 : ℝ)*x 0 + (5515966151/10000000000 : ℝ)*x 1 + (-1994587353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282926169/10000000000 : ℝ)^8295 ≤ (21428534288439/50000000000000 : ℝ)^6247 := by
    have hnat : (5282926169 : ℕ)^8295*50000000000000^6247 ≤ 21428534288439^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282926169 10000000000 21428534288439 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515966151/10000000000 : ℝ)^8295 ≤ (1418291560373/3125000000000 : ℝ)^6247 := by
    have hnat : (5515966151 : ℕ)^8295*3125000000000^6247 ≤ 1418291560373^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515966151 10000000000 1418291560373 3125000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994587353/10000000000 : ℝ)^8295 ≤ (11757601472319/100000000000000 : ℝ)^6247 := by
    have hnat : (1994587353 : ℕ)^8295*100000000000000^6247 ≤ 11757601472319^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994587353 10000000000 11757601472319 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282926169/10000000000 : ℝ), (5515966151/10000000000 : ℝ), (-1994587353/10000000000 : ℝ)] ![(21428534288439/50000000000000 : ℝ), (1418291560373/3125000000000 : ℝ), (11757601472319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282926169/10000000000 : ℝ)|^8295 ≤ (21428534288439/50000000000000 : ℝ)^6247
        have hw : |(5282926169/10000000000 : ℝ)|=(5282926169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515966151/10000000000 : ℝ)|^8295 ≤ (1418291560373/3125000000000 : ℝ)^6247
        have hw : |(5515966151/10000000000 : ℝ)|=(5515966151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1994587353/10000000000 : ℝ)|^8295 ≤ (11757601472319/100000000000000 : ℝ)^6247
        have hw : |(-1994587353/10000000000 : ℝ)|=(1994587353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s2_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358941061/10000000000 : ℝ)*x 0 + (4730045089/10000000000 : ℝ)*x 1 + (2008708429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358941061/10000000000 : ℝ)^8295 ≤ (16600708301193/50000000000000 : ℝ)^6247 := by
    have hnat : (4358941061 : ℕ)^8295*50000000000000^6247 ≤ 16600708301193^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358941061 10000000000 16600708301193 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4730045089/10000000000 : ℝ)^8295 ≤ (4625769465109/12500000000000 : ℝ)^6247 := by
    have hnat : (4730045089 : ℕ)^8295*12500000000000^6247 ≤ 4625769465109^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730045089 10000000000 4625769465109 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008708429/5000000000 : ℝ)^8295 ≤ (29792427651611/100000000000000 : ℝ)^6247 := by
    have hnat : (2008708429 : ℕ)^8295*100000000000000^6247 ≤ 29792427651611^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008708429 5000000000 29792427651611 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358941061/10000000000 : ℝ), (4730045089/10000000000 : ℝ), (2008708429/5000000000 : ℝ)] ![(16600708301193/50000000000000 : ℝ), (4625769465109/12500000000000 : ℝ), (29792427651611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358941061/10000000000 : ℝ)|^8295 ≤ (16600708301193/50000000000000 : ℝ)^6247
        have hw : |(4358941061/10000000000 : ℝ)|=(4358941061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4730045089/10000000000 : ℝ)|^8295 ≤ (4625769465109/12500000000000 : ℝ)^6247
        have hw : |(4730045089/10000000000 : ℝ)|=(4730045089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008708429/5000000000 : ℝ)|^8295 ≤ (29792427651611/100000000000000 : ℝ)^6247
        have hw : |(2008708429/5000000000 : ℝ)|=(2008708429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1777/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (133/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5423/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (149605518088957/20000000000000000000 : ℝ) := by
    have hpowers : (5423/100000 : ℝ)^4147 ≤ (149605518088957/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5423 : ℕ)^4147*20000000000000000000^1024 ≤ 149605518088957^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5423 100000 149605518088957 20000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5423/100000 : ℝ)) (X := (149605518088957/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20621/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (33428608162932633/20000000000000000000 : ℝ) := by
    have hpowers : (20621/100000 : ℝ)^4147 ≤ (33428608162932633/20000000000000000000 : ℝ)^1024 := by
      have hnat : (20621 : ℕ)^4147*20000000000000000000^1024 ≤ 33428608162932633^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20621 100000 33428608162932633 20000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20621/100000 : ℝ)) (X := (33428608162932633/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000149605518088957/10000000000000000000 : ℝ) ≤ (10000036941207511/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (10000149605518088957/10000000000000000000 : ℝ)^1024 ≤ (10000036941207511/10000000000000000 : ℝ)^4147 := by
      have hnat : (10000149605518088957 : ℕ)^1024*10000000000000000^4147 ≤ 10000036941207511^4147*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000149605518088957 10000000000000000000 10000036941207511 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036941207511/10000000000000000 : ℝ)) (X := (10000149605518088957/10000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2003357821368102159/2000000000000000000 : ℝ) ≤ (5002071520101057/5000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (2003357821368102159/2000000000000000000 : ℝ)^1024 ≤ (5002071520101057/5000000000000000 : ℝ)^4147 := by
      have hnat : (2003357821368102159 : ℕ)^1024*5000000000000000^4147 ≤ 5002071520101057^4147*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2003357821368102159 2000000000000000000 5002071520101057 5000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002071520101057/5000000000000000 : ℝ)) (X := (2003357821368102159/2000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10033428608162932633/10000000000000000000 : ℝ) ≤ (10008249139196717/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (10033428608162932633/10000000000000000000 : ℝ)^1024 ≤ (10008249139196717/10000000000000000 : ℝ)^4147 := by
      have hnat : (10033428608162932633 : ℕ)^1024*10000000000000000^4147 ≤ 10008249139196717^4147*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10033428608162932633 10000000000000000000 10008249139196717 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008249139196717/10000000000000000 : ℝ)) (X := (10033428608162932633/10000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(149605518088957/20000000000000000000 : ℝ) ≤ ((223435333357023953/223500000000000000 : ℝ)+2*(4106098994603/1519800000000000 : ℝ)*(5423/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (223435333357023953/223500000000000000 : ℝ)+2*(4106098994603/1519800000000000 : ℝ)*(5423/100000 : ℝ)=(10000036941207511/10000000000000000 : ℝ) by norm_num, show 1+2*(149605518088957/20000000000000000000 : ℝ)=(10000149605518088957/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33428608162932633/20000000000000000000 : ℝ)+(149605518088957/20000000000000000000 : ℝ) ≤ ((223435333357023953/223500000000000000 : ℝ)+(4106098994603/1519800000000000 : ℝ)*((20621/100000 : ℝ)+(5423/100000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (223435333357023953/223500000000000000 : ℝ)+(4106098994603/1519800000000000 : ℝ)*((20621/100000 : ℝ)+(5423/100000 : ℝ))=(5002071520101057/5000000000000000 : ℝ) by norm_num, show 1+(33428608162932633/20000000000000000000 : ℝ)+(149605518088957/20000000000000000000 : ℝ)=(2003357821368102159/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33428608162932633/20000000000000000000 : ℝ) ≤ ((223435333357023953/223500000000000000 : ℝ)+2*(4106098994603/1519800000000000 : ℝ)*(20621/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (223435333357023953/223500000000000000 : ℝ)+2*(4106098994603/1519800000000000 : ℝ)*(20621/100000 : ℝ)=(10008249139196717/10000000000000000 : ℝ) by norm_num, show 1+2*(33428608162932633/20000000000000000000 : ℝ)=(10033428608162932633/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (223435333357023953/223500000000000000 : ℝ)*(X 1 0+X 2 0)+(4106098994603/1519800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (5423/100000 : ℝ)) (hi := (20621/100000 : ℝ)) (c := (223435333357023953/223500000000000000 : ℝ)) (alpha := (4106098994603/1519800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (223435333357023953/223500000000000000 : ℝ)*(X 0 1+X 2 1)+(4106098994603/1519800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (5423/100000 : ℝ)) (hi := (20621/100000 : ℝ)) (c := (223435333357023953/223500000000000000 : ℝ)) (alpha := (4106098994603/1519800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (223435333357023953/223500000000000000 : ℝ)*(X 0 2+X 1 2)+(4106098994603/1519800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (5423/100000 : ℝ)) (hi := (20621/100000 : ℝ)) (c := (223435333357023953/223500000000000000 : ℝ)) (alpha := (4106098994603/1519800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-433499067/2000000000 : ℝ)*X 0 0+(5518590281/10000000000 : ℝ)*X 0 1+(1288084767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075120549/2000000000 : ℝ)*X 1 0+(-2358213951/10000000000 : ℝ)*X 1 1+(322021263/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375602701/10000000000 : ℝ)*X 2 0+(2576170129/5000000000 : ℝ)*X 2 1+(-294776743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87174293/200000000 : ℝ)*X 0 0+(401223893/1000000000 : ℝ)*X 0 1+(1183792897/2500000000 : ℝ)*X 0 2+(87174293/200000000 : ℝ)*X 1 0+(401223893/1000000000 : ℝ)*X 1 1+(1183792897/2500000000 : ℝ)*X 1 2+(87174293/200000000 : ℝ)*X 2 0+(401223893/1000000000 : ℝ)*X 2 1+(1183792897/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167609373/10000000000 : ℝ)*X 0 0+(5154936687/10000000000 : ℝ)*X 0 1+(551596613/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641463007/5000000000 : ℝ)*X 1 0+(-498646869/2500000000 : ℝ)*X 1 1+(5515966217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5282926169/10000000000 : ℝ)*X 2 0+(5515966151/10000000000 : ℝ)*X 2 1+(-1994587353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358941061/10000000000 : ℝ)*X 0 0+(4730045089/10000000000 : ℝ)*X 0 1+(2008708429/5000000000 : ℝ)*X 0 2+(4358941061/10000000000 : ℝ)*X 1 0+(4730045089/10000000000 : ℝ)*X 1 1+(2008708429/5000000000 : ℝ)*X 1 2+(4358941061/10000000000 : ℝ)*X 2 0+(4730045089/10000000000 : ℝ)*X 2 1+(2008708429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12592765885997947703941341/1266500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332668781/25000000000000 : ℝ)*(base19) + (1097157899/100000000000000 : ℝ)*(base23) + (24435829/10000000000000 : ℝ)*(upper3) + (113515797/100000000000000 : ℝ)*(upper4) + (40735591/50000000000000 : ℝ)*(upper5) + (41136784309047/2000000000000 : ℝ)*(major0) + (41136784309047/2000000000000 : ℝ)*(major1) + (41136784309047/2000000000000 : ℝ)*(major2) + (682596853447037/25000000000000 : ℝ)*(sp0) + (1365202831451301/50000000000000 : ℝ)*(sp1) + (1365202948209913/50000000000000 : ℝ)*(sp2) + (172907760226573/12500000000000 : ℝ)*(sp3) + (9789894789/50000000000000 : ℝ)*(sp4) + (4512041099/50000000000000 : ℝ)*(sp7) + (691635552947391/50000000000000 : ℝ)*(f.failure) + (1365203496788863/50000000000000 : ℝ)*(f.sum) + (6408772806603/2533000000000000000000000000 : ℝ)*base65 + (24476533482861351/2533000000000000000000000000000 : ℝ)*base68 + (12660742158973351/2533000000000000000000000000000 : ℝ)*base70 + (11140723530677351/2533000000000000000000000000000 : ℝ)*base72 + (1581871209137/506600000000000000000000000 : ℝ)*base74 + (34651392035369351/2533000000000000000000000000000 : ℝ)*base76 + (13412083719365351/2533000000000000000000000000000 : ℝ)*base78 + (22579107343183351/2533000000000000000000000000000 : ℝ)*base80 + (1548950724321/2533000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2333349/5000000000000000000000 : ℝ)*base90 + (2333349/5000000000000000000000 : ℝ)*base92 + (2333349/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181643379946383003896049/25330000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1428840081/100000000000000 : ℝ)*(base19) + (329944593/20000000000000 : ℝ)*(base23) + (38909649/20000000000000 : ℝ)*(upper3) + (12046947/25000000000000 : ℝ)*(lower4) + (34659593/25000000000000 : ℝ)*(upper5) + (2086556561362977/100000000000000 : ℝ)*(major0) + (2086556561362977/100000000000000 : ℝ)*(major1) + (2086556561362977/100000000000000 : ℝ)*(major2) + (646606969/5000000000000 : ℝ)*(sp1) + (15691254041/100000000000000 : ℝ)*(sp2) + (43279002929089/1562500000000 : ℝ)*(sp4) + (692460456620559/25000000000000 : ℝ)*(sp5) + (2769838846484691/100000000000000 : ℝ)*(sp6) + (2740735734821/195312500000 : ℝ)*(sp7) + (2740735734821/195312500000 : ℝ)*(f.failure) + (43279002929089/1562500000000 : ℝ)*(f.sum) + (66461010600743/25330000000000000000000000000 : ℝ)*base66 + (806235042778474959/126650000000000000000000000000000 : ℝ)*base67 + (631634084252074959/126650000000000000000000000000000 : ℝ)*base69 + (225450768325074959/126650000000000000000000000000000 : ℝ)*base71 + (37176386822417/25330000000000000000000000000 : ℝ)*base73 + (248894439271725041/126650000000000000000000000000000 : ℝ)*base76 + (293137682066325041/126650000000000000000000000000000 : ℝ)*base78 + (1565607362112075041/126650000000000000000000000000000 : ℝ)*base80 + (65355992141007/25330000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (377137/39062500000000000000 : ℝ)*base89 + (377137/39062500000000000000 : ℝ)*base91 + (377137/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1102_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (133/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1102_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (133/800 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1102_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1102_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1102_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1777/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (133/800 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
