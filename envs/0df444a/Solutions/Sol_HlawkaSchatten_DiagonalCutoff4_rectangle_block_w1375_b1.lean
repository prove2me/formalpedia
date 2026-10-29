-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1375_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:29.945358+00:00
-- url     : https://prove2.me/submissions/a60c4455-accf-4a72-8f0f-4a8fae1fa029

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
theorem support_rectangle_w1375_s3_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007175573/5000000000 : ℝ)*x 0 + (5423135001/10000000000 : ℝ)*x 1 + (261719483/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007175573/5000000000 : ℝ)^4335 ≤ (767014557929/6250000000000 : ℝ)^3311 := by
    have hnat : (1007175573 : ℕ)^4335*6250000000000^3311 ≤ 767014557929^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007175573 5000000000 767014557929 6250000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423135001/10000000000 : ℝ)^4335 ≤ (22440445878497/50000000000000 : ℝ)^3311 := by
    have hnat : (5423135001 : ℕ)^4335*50000000000000^3311 ≤ 22440445878497^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423135001 10000000000 22440445878497 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261719483/500000000 : ℝ)^4335 ≤ (21423437650481/50000000000000 : ℝ)^3311 := by
    have hnat : (261719483 : ℕ)^4335*50000000000000^3311 ≤ 21423437650481^3311*500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261719483 500000000 21423437650481 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007175573/5000000000 : ℝ), (5423135001/10000000000 : ℝ), (261719483/500000000 : ℝ)] ![(767014557929/6250000000000 : ℝ), (22440445878497/50000000000000 : ℝ), (21423437650481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007175573/5000000000 : ℝ)|^4335 ≤ (767014557929/6250000000000 : ℝ)^3311
        have hw : |(-1007175573/5000000000 : ℝ)|=(1007175573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423135001/10000000000 : ℝ)|^4335 ≤ (22440445878497/50000000000000 : ℝ)^3311
        have hw : |(5423135001/10000000000 : ℝ)|=(5423135001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261719483/500000000 : ℝ)|^4335 ≤ (21423437650481/50000000000000 : ℝ)^3311
        have hw : |(261719483/500000000 : ℝ)|=(261719483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334469521/625000000 : ℝ)*x 0 + (-2110737357/10000000000 : ℝ)*x 1 + (5234389737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334469521/625000000 : ℝ)^4335 ≤ (4410642836679/10000000000000 : ℝ)^3311 := by
    have hnat : (334469521 : ℕ)^4335*10000000000000^3311 ≤ 4410642836679^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334469521 625000000 4410642836679 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110737357/10000000000 : ℝ)^4335 ≤ (6523347746961/50000000000000 : ℝ)^3311 := by
    have hnat : (2110737357 : ℕ)^4335*50000000000000^3311 ≤ 6523347746961^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110737357 10000000000 6523347746961 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234389737/10000000000 : ℝ)^4335 ≤ (42846876126189/100000000000000 : ℝ)^3311 := by
    have hnat : (5234389737 : ℕ)^4335*100000000000000^3311 ≤ 42846876126189^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234389737 10000000000 42846876126189 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334469521/625000000 : ℝ), (-2110737357/10000000000 : ℝ), (5234389737/10000000000 : ℝ)] ![(4410642836679/10000000000000 : ℝ), (6523347746961/50000000000000 : ℝ), (42846876126189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334469521/625000000 : ℝ)|^4335 ≤ (4410642836679/10000000000000 : ℝ)^3311
        have hw : |(334469521/625000000 : ℝ)|=(334469521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110737357/10000000000 : ℝ)|^4335 ≤ (6523347746961/50000000000000 : ℝ)^3311
        have hw : |(-2110737357/10000000000 : ℝ)|=(2110737357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234389737/10000000000 : ℝ)|^4335 ≤ (42846876126189/100000000000000 : ℝ)^3311
        have hw : |(5234389737/10000000000 : ℝ)|=(5234389737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351512327/10000000000 : ℝ)*x 0 + (1046877933/2000000000 : ℝ)*x 1 + (-263842183/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351512327/10000000000 : ℝ)^4335 ≤ (44106428269673/100000000000000 : ℝ)^3311 := by
    have hnat : (5351512327 : ℕ)^4335*100000000000000^3311 ≤ 44106428269673^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351512327 10000000000 44106428269673 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046877933/2000000000 : ℝ)^4335 ≤ (10711718838637/25000000000000 : ℝ)^3311 := by
    have hnat : (1046877933 : ℕ)^4335*25000000000000^3311 ≤ 10711718838637^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046877933 2000000000 10711718838637 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263842183/1250000000 : ℝ)^4335 ≤ (6523348179923/50000000000000 : ℝ)^3311 := by
    have hnat : (263842183 : ℕ)^4335*50000000000000^3311 ≤ 6523348179923^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263842183 1250000000 6523348179923 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351512327/10000000000 : ℝ), (1046877933/2000000000 : ℝ), (-263842183/1250000000 : ℝ)] ![(44106428269673/100000000000000 : ℝ), (10711718838637/25000000000000 : ℝ), (6523348179923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351512327/10000000000 : ℝ)|^4335 ≤ (44106428269673/100000000000000 : ℝ)^3311
        have hw : |(5351512327/10000000000 : ℝ)|=(5351512327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046877933/2000000000 : ℝ)|^4335 ≤ (10711718838637/25000000000000 : ℝ)^3311
        have hw : |(1046877933/2000000000 : ℝ)|=(1046877933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263842183/1250000000 : ℝ)|^4335 ≤ (6523348179923/50000000000000 : ℝ)^3311
        have hw : |(-263842183/1250000000 : ℝ)|=(263842183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158591547/5000000000 : ℝ)*x 0 + (164853029/400000000 : ℝ)*x 1 + (565197559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158591547/5000000000 : ℝ)^4335 ≤ (8323733183071/25000000000000 : ℝ)^3311 := by
    have hnat : (2158591547 : ℕ)^4335*25000000000000^3311 ≤ 8323733183071^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158591547 5000000000 8323733183071 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164853029/400000000 : ℝ)^4335 ≤ (3133131312627/10000000000000 : ℝ)^3311 := by
    have hnat : (164853029 : ℕ)^4335*10000000000000^3311 ≤ 3133131312627^3311*400000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164853029 400000000 3133131312627 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565197559/1250000000 : ℝ)^4335 ≤ (35373754118847/100000000000000 : ℝ)^3311 := by
    have hnat : (565197559 : ℕ)^4335*100000000000000^3311 ≤ 35373754118847^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565197559 1250000000 35373754118847 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158591547/5000000000 : ℝ), (164853029/400000000 : ℝ), (565197559/1250000000 : ℝ)] ![(8323733183071/25000000000000 : ℝ), (3133131312627/10000000000000 : ℝ), (35373754118847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158591547/5000000000 : ℝ)|^4335 ≤ (8323733183071/25000000000000 : ℝ)^3311
        have hw : |(2158591547/5000000000 : ℝ)|=(2158591547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164853029/400000000 : ℝ)|^4335 ≤ (3133131312627/10000000000000 : ℝ)^3311
        have hw : |(164853029/400000000 : ℝ)|=(164853029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565197559/1250000000 : ℝ)|^4335 ≤ (35373754118847/100000000000000 : ℝ)^3311
        have hw : |(565197559/1250000000 : ℝ)|=(565197559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007184603/5000000000 : ℝ)*x 0 + (5235162103/10000000000 : ℝ)*x 1 + (1084471529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007184603/5000000000 : ℝ)^4335 ≤ (12272376984631/100000000000000 : ℝ)^3311 := by
    have hnat : (1007184603 : ℕ)^4335*100000000000000^3311 ≤ 12272376984631^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007184603 5000000000 12272376984631 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235162103/10000000000 : ℝ)^4335 ≤ (42855153948237/100000000000000 : ℝ)^3311 := by
    have hnat : (5235162103 : ℕ)^4335*100000000000000^3311 ≤ 42855153948237^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235162103 10000000000 42855153948237 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084471529/2000000000 : ℝ)^4335 ≤ (8974493811481/20000000000000 : ℝ)^3311 := by
    have hnat : (1084471529 : ℕ)^4335*20000000000000^3311 ≤ 8974493811481^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084471529 2000000000 8974493811481 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007184603/5000000000 : ℝ), (5235162103/10000000000 : ℝ), (1084471529/2000000000 : ℝ)] ![(12272376984631/100000000000000 : ℝ), (42855153948237/100000000000000 : ℝ), (8974493811481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007184603/5000000000 : ℝ)|^4335 ≤ (12272376984631/100000000000000 : ℝ)^3311
        have hw : |(-1007184603/5000000000 : ℝ)|=(1007184603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235162103/10000000000 : ℝ)|^4335 ≤ (42855153948237/100000000000000 : ℝ)^3311
        have hw : |(5235162103/10000000000 : ℝ)|=(5235162103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084471529/2000000000 : ℝ)|^4335 ≤ (8974493811481/20000000000000 : ℝ)^3311
        have hw : |(1084471529/2000000000 : ℝ)|=(1084471529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651357809/5000000000 : ℝ)*x 0 + (-1922768879/10000000000 : ℝ)*x 1 + (1355589607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651357809/5000000000 : ℝ)^4335 ≤ (10895153694263/25000000000000 : ℝ)^3311 := by
    have hnat : (2651357809 : ℕ)^4335*25000000000000^3311 ≤ 10895153694263^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651357809 5000000000 10895153694263 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922768879/10000000000 : ℝ)^4335 ≤ (11546907670451/100000000000000 : ℝ)^3311 := by
    have hnat : (1922768879 : ℕ)^4335*100000000000000^3311 ≤ 11546907670451^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922768879 10000000000 11546907670451 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355589607/2500000000 : ℝ)^4335 ≤ (4487247754107/10000000000000 : ℝ)^3311 := by
    have hnat : (1355589607 : ℕ)^4335*10000000000000^3311 ≤ 4487247754107^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355589607 2500000000 4487247754107 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651357809/5000000000 : ℝ), (-1922768879/10000000000 : ℝ), (1355589607/2500000000 : ℝ)] ![(10895153694263/25000000000000 : ℝ), (11546907670451/100000000000000 : ℝ), (4487247754107/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651357809/5000000000 : ℝ)|^4335 ≤ (10895153694263/25000000000000 : ℝ)^3311
        have hw : |(2651357809/5000000000 : ℝ)|=(2651357809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922768879/10000000000 : ℝ)|^4335 ≤ (11546907670451/100000000000000 : ℝ)^3311
        have hw : |(-1922768879/10000000000 : ℝ)|=(1922768879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355589607/2500000000 : ℝ)|^4335 ≤ (4487247754107/10000000000000 : ℝ)^3311
        have hw : |(1355589607/2500000000 : ℝ)|=(1355589607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165709909/312500000 : ℝ)*x 0 + (2711178667/5000000000 : ℝ)*x 1 + (-15382147/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165709909/312500000 : ℝ)^4335 ≤ (21790315297357/50000000000000 : ℝ)^3311 := by
    have hnat : (165709909 : ℕ)^4335*50000000000000^3311 ≤ 21790315297357^3311*312500000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165709909 312500000 21790315297357 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711178667/5000000000 : ℝ)^4335 ≤ (1402264552743/3125000000000 : ℝ)^3311 := by
    have hnat : (2711178667 : ℕ)^4335*3125000000000^3311 ≤ 1402264552743^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711178667 5000000000 1402264552743 3125000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15382147/80000000 : ℝ)^4335 ≤ (11546903707679/100000000000000 : ℝ)^3311 := by
    have hnat : (15382147 : ℕ)^4335*100000000000000^3311 ≤ 11546903707679^3311*80000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15382147 80000000 11546903707679 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165709909/312500000 : ℝ), (2711178667/5000000000 : ℝ), (-15382147/80000000 : ℝ)] ![(21790315297357/50000000000000 : ℝ), (1402264552743/3125000000000 : ℝ), (11546903707679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165709909/312500000 : ℝ)|^4335 ≤ (21790315297357/50000000000000 : ℝ)^3311
        have hw : |(165709909/312500000 : ℝ)|=(165709909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711178667/5000000000 : ℝ)|^4335 ≤ (1402264552743/3125000000000 : ℝ)^3311
        have hw : |(2711178667/5000000000 : ℝ)|=(2711178667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15382147/80000000 : ℝ)|^4335 ≤ (11546903707679/100000000000000 : ℝ)^3311
        have hw : |(-15382147/80000000 : ℝ)|=(15382147/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s3_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317222097/10000000000 : ℝ)*x 0 + (4519941731/10000000000 : ℝ)*x 1 + (4122972359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317222097/10000000000 : ℝ)^4335 ≤ (33295326559943/100000000000000 : ℝ)^3311 := by
    have hnat : (4317222097 : ℕ)^4335*100000000000000^3311 ≤ 33295326559943^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317222097 10000000000 33295326559943 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519941731/10000000000 : ℝ)^4335 ≤ (35356969681533/100000000000000 : ℝ)^3311 := by
    have hnat : (4519941731 : ℕ)^4335*100000000000000^3311 ≤ 35356969681533^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519941731 10000000000 35356969681533 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4122972359/10000000000 : ℝ)^4335 ≤ (15673851875093/50000000000000 : ℝ)^3311 := by
    have hnat : (4122972359 : ℕ)^4335*50000000000000^3311 ≤ 15673851875093^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122972359 10000000000 15673851875093 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317222097/10000000000 : ℝ), (4519941731/10000000000 : ℝ), (4122972359/10000000000 : ℝ)] ![(33295326559943/100000000000000 : ℝ), (35356969681533/100000000000000 : ℝ), (15673851875093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317222097/10000000000 : ℝ)|^4335 ≤ (33295326559943/100000000000000 : ℝ)^3311
        have hw : |(4317222097/10000000000 : ℝ)|=(4317222097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519941731/10000000000 : ℝ)|^4335 ≤ (35356969681533/100000000000000 : ℝ)^3311
        have hw : |(4519941731/10000000000 : ℝ)|=(4519941731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4122972359/10000000000 : ℝ)|^4335 ≤ (15673851875093/50000000000000 : ℝ)^3311
        have hw : |(4122972359/10000000000 : ℝ)|=(4122972359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5493/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14981/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (503/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (503/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (503/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (503/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (503/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (503/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (503/5000 : ℝ) ^ (2167/512 : ℝ) ≤ (187682550707979/3125000000000000000 : ℝ) := by
    have hpowers : (503/5000 : ℝ)^2167 ≤ (187682550707979/3125000000000000000 : ℝ)^512 := by
      have hnat : (503 : ℕ)^2167*3125000000000000000^512 ≤ 187682550707979^512*5000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        503 5000 187682550707979 3125000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (503/5000 : ℝ)) (X := (187682550707979/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15979/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (21284129628051141/50000000000000000000 : ℝ) := by
    have hpowers : (15979/100000 : ℝ)^2167 ≤ (21284129628051141/50000000000000000000 : ℝ)^512 := by
      have hnat : (15979 : ℕ)^2167*50000000000000000000^512 ≤ 21284129628051141^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15979 100000 21284129628051141 50000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15979/100000 : ℝ)) (X := (21284129628051141/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562687682550707979/1562500000000000000 : ℝ) ≤ (10000283788636461/10000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (1562687682550707979/1562500000000000000 : ℝ)^512 ≤ (10000283788636461/10000000000000000 : ℝ)^2167 := by
      have hnat : (1562687682550707979 : ℕ)^512*10000000000000000^2167 ≤ 10000283788636461^2167*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562687682550707979 1562500000000000000 10000283788636461 10000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283788636461/10000000000000000 : ℝ)) (X := (1562687682550707979/1562500000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004857410087875761/10000000000000000000 : ℝ) ≤ (2000229490797529/2000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (10004857410087875761/10000000000000000000 : ℝ)^512 ≤ (2000229490797529/2000000000000000 : ℝ)^2167 := by
      have hnat : (10004857410087875761 : ℕ)^512*2000000000000000^2167 ≤ 2000229490797529^2167*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004857410087875761 10000000000000000000 2000229490797529 2000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000229490797529/2000000000000000 : ℝ)) (X := (10004857410087875761/10000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021284129628051141/25000000000000000000 : ℝ) ≤ (10002011119338829/10000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (25021284129628051141/25000000000000000000 : ℝ)^512 ≤ (10002011119338829/10000000000000000 : ℝ)^2167 := by
      have hnat : (25021284129628051141 : ℕ)^512*10000000000000000^2167 ≤ 10002011119338829^2167*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021284129628051141 25000000000000000000 10002011119338829 10000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002011119338829/10000000000000000 : ℝ)) (X := (25021284129628051141/25000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(187682550707979/3125000000000000000 : ℝ) ≤ ((59174302798073390579/59190000000000000000 : ℝ)+2*(53979084449/36993750000000 : ℝ)*(503/5000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (59174302798073390579/59190000000000000000 : ℝ)+2*(53979084449/36993750000000 : ℝ)*(503/5000 : ℝ)=(10000283788636461/10000000000000000 : ℝ) by norm_num, show 1+2*(187682550707979/3125000000000000000 : ℝ)=(1562687682550707979/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21284129628051141/50000000000000000000 : ℝ)+(187682550707979/3125000000000000000 : ℝ) ≤ ((59174302798073390579/59190000000000000000 : ℝ)+(53979084449/36993750000000 : ℝ)*((15979/100000 : ℝ)+(503/5000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (59174302798073390579/59190000000000000000 : ℝ)+(53979084449/36993750000000 : ℝ)*((15979/100000 : ℝ)+(503/5000 : ℝ))=(2000229490797529/2000000000000000 : ℝ) by norm_num, show 1+(21284129628051141/50000000000000000000 : ℝ)+(187682550707979/3125000000000000000 : ℝ)=(10004857410087875761/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21284129628051141/50000000000000000000 : ℝ) ≤ ((59174302798073390579/59190000000000000000 : ℝ)+2*(53979084449/36993750000000 : ℝ)*(15979/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (59174302798073390579/59190000000000000000 : ℝ)+2*(53979084449/36993750000000 : ℝ)*(15979/100000 : ℝ)=(10002011119338829/10000000000000000 : ℝ) by norm_num, show 1+2*(21284129628051141/50000000000000000000 : ℝ)=(25021284129628051141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59174302798073390579/59190000000000000000 : ℝ)*(X 1 0+X 2 0)+(53979084449/36993750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (503/5000 : ℝ)) (hi := (15979/100000 : ℝ)) (c := (59174302798073390579/59190000000000000000 : ℝ)) (alpha := (53979084449/36993750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59174302798073390579/59190000000000000000 : ℝ)*(X 0 1+X 2 1)+(53979084449/36993750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (503/5000 : ℝ)) (hi := (15979/100000 : ℝ)) (c := (59174302798073390579/59190000000000000000 : ℝ)) (alpha := (53979084449/36993750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59174302798073390579/59190000000000000000 : ℝ)*(X 0 2+X 1 2)+(53979084449/36993750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (503/5000 : ℝ)) (hi := (15979/100000 : ℝ)) (c := (59174302798073390579/59190000000000000000 : ℝ)) (alpha := (53979084449/36993750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1007175573/5000000000 : ℝ)*X 0 0+(5423135001/10000000000 : ℝ)*X 0 1+(261719483/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334469521/625000000 : ℝ)*X 1 0+(-2110737357/10000000000 : ℝ)*X 1 1+(5234389737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351512327/10000000000 : ℝ)*X 2 0+(1046877933/2000000000 : ℝ)*X 2 1+(-263842183/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158591547/5000000000 : ℝ)*X 0 0+(164853029/400000000 : ℝ)*X 0 1+(565197559/1250000000 : ℝ)*X 0 2+(2158591547/5000000000 : ℝ)*X 1 0+(164853029/400000000 : ℝ)*X 1 1+(565197559/1250000000 : ℝ)*X 1 2+(2158591547/5000000000 : ℝ)*X 2 0+(164853029/400000000 : ℝ)*X 2 1+(565197559/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1007184603/5000000000 : ℝ)*X 0 0+(5235162103/10000000000 : ℝ)*X 0 1+(1084471529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651357809/5000000000 : ℝ)*X 1 0+(-1922768879/10000000000 : ℝ)*X 1 1+(1355589607/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165709909/312500000 : ℝ)*X 2 0+(2711178667/5000000000 : ℝ)*X 2 1+(-15382147/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317222097/10000000000 : ℝ)*X 0 0+(4519941731/10000000000 : ℝ)*X 0 1+(4122972359/10000000000 : ℝ)*X 0 2+(4317222097/10000000000 : ℝ)*X 1 0+(4519941731/10000000000 : ℝ)*X 1 1+(4122972359/10000000000 : ℝ)*X 1 2+(4317222097/10000000000 : ℝ)*X 2 0+(4519941731/10000000000 : ℝ)*X 2 1+(4122972359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2345622262021581118896432667/493250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205365953/25000000000000 : ℝ)*(base19) + (5868263/800000000000 : ℝ)*(base23) + (42287991/100000000000000 : ℝ)*(lower2) + (187657989/100000000000000 : ℝ)*(upper3) + (1576891/20000000000000 : ℝ)*(upper5) + (1949149570354109/50000000000000 : ℝ)*(major0) + (1949149570354109/50000000000000 : ℝ)*(major1) + (1949149570354109/50000000000000 : ℝ)*(major2) + (5298162211727629/100000000000000 : ℝ)*(sp0) + (5298174403947917/100000000000000 : ℝ)*(sp1) + (2649087245939427/50000000000000 : ℝ)*(sp2) + (1249207265501359/50000000000000 : ℝ)*(sp3) + (130136841/1000000000000 : ℝ)*(sp4) + (522905451/6250000000000 : ℝ)*(sp7) + (1249211448744967/50000000000000 : ℝ)*(f.failure) + (5298175225411729/100000000000000 : ℝ)*(f.sum) + (42107950372919/14797500000000000000000000000 : ℝ)*base66 + (21406773410987639111/2959500000000000000000000000000000 : ℝ)*base67 + (37441315689040139111/2959500000000000000000000000000000 : ℝ)*base69 + (41093576999818139111/2959500000000000000000000000000000 : ℝ)*base71 + (86804636568703/29595000000000000000000000000 : ℝ)*base74 + (43941954543194639111/2959500000000000000000000000000000 : ℝ)*base75 + (712297042231139111/2959500000000000000000000000000000 : ℝ)*base77 + (16768233696718139111/2959500000000000000000000000000000 : ℝ)*base79 + (1280006623727/1849687500000000000000000000 : ℝ)*base81 + (1004233/1250000000000000000000 : ℝ)*base89 + (1004233/1250000000000000000000 : ℝ)*base91 + (1004233/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298650065063592145438631223/246625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922292793/50000000000000 : ℝ)*(base19) + (799671601/20000000000000 : ℝ)*(base23) + (12378823/2500000000000 : ℝ)*(upper3) + (19611597/10000000000000 : ℝ)*(lower4) + (28930431/10000000000000 : ℝ)*(upper5) + (982637632341237/25000000000000 : ℝ)*(major0) + (982637632341237/25000000000000 : ℝ)*(major1) + (982637632341237/25000000000000 : ℝ)*(major2) + (10207969799/25000000000000 : ℝ)*(sp1) + (73765362583/100000000000000 : ℝ)*(sp2) + (667751022655701/12500000000000 : ℝ)*(sp4) + (213678620191233/4000000000000 : ℝ)*(sp5) + (267096520876251/5000000000000 : ℝ)*(sp6) + (157443302319959/6250000000000 : ℝ)*(sp7) + (157443302319959/6250000000000 : ℝ)*(f.failure) + (667751022655701/12500000000000 : ℝ)*(f.sum) + (970553802771/154140625000000000000000000 : ℝ)*base65 + (770024366582731259/493250000000000000000000000000000 : ℝ)*base68 + (1404811254498731259/493250000000000000000000000000000 : ℝ)*base70 + (5468901043072768741/493250000000000000000000000000000 : ℝ)*base71 + (32780117828939/9865000000000000000000000000 : ℝ)*base73 + (9182167948897268741/493250000000000000000000000000000 : ℝ)*base75 + (904093998485981259/493250000000000000000000000000000 : ℝ)*base78 + (1471232389763481259/493250000000000000000000000000000 : ℝ)*base80 + (556177927129/2466250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (881559/156250000000000000000 : ℝ)*base90 + (881559/156250000000000000000 : ℝ)*base92 + (881559/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1375_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1375_s4_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2015567743/10000000000 : ℝ)*x 0 + (2706513653/5000000000 : ℝ)*x 1 + (5243697623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015567743/10000000000 : ℝ)^4335 ≤ (6140969076121/50000000000000 : ℝ)^3311 := by
    have hnat : (2015567743 : ℕ)^4335*50000000000000^3311 ≤ 6140969076121^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015567743 10000000000 6140969076121 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706513653/5000000000 : ℝ)^4335 ≤ (8954280683431/20000000000000 : ℝ)^3311 := by
    have hnat : (2706513653 : ℕ)^4335*20000000000000^3311 ≤ 8954280683431^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706513653 5000000000 8954280683431 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243697623/10000000000 : ℝ)^4335 ≤ (42946658410119/100000000000000 : ℝ)^3311 := by
    have hnat : (5243697623 : ℕ)^4335*100000000000000^3311 ≤ 42946658410119^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243697623 10000000000 42946658410119 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2015567743/10000000000 : ℝ), (2706513653/5000000000 : ℝ), (5243697623/10000000000 : ℝ)] ![(6140969076121/50000000000000 : ℝ), (8954280683431/20000000000000 : ℝ), (42946658410119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2015567743/10000000000 : ℝ)|^4335 ≤ (6140969076121/50000000000000 : ℝ)^3311
        have hw : |(-2015567743/10000000000 : ℝ)|=(2015567743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706513653/5000000000 : ℝ)|^4335 ≤ (8954280683431/20000000000000 : ℝ)^3311
        have hw : |(2706513653/5000000000 : ℝ)|=(2706513653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243697623/10000000000 : ℝ)|^4335 ≤ (42946658410119/100000000000000 : ℝ)^3311
        have hw : |(5243697623/10000000000 : ℝ)|=(5243697623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337230801/2500000000 : ℝ)*x 0 + (-2101853111/10000000000 : ℝ)*x 1 + (2621849077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337230801/2500000000 : ℝ)^4335 ≤ (5509811443289/12500000000000 : ℝ)^3311 := by
    have hnat : (1337230801 : ℕ)^4335*12500000000000^3311 ≤ 5509811443289^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337230801 2500000000 5509811443289 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101853111/10000000000 : ℝ)^4335 ≤ (12974844333207/100000000000000 : ℝ)^3311 := by
    have hnat : (2101853111 : ℕ)^4335*100000000000000^3311 ≤ 12974844333207^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101853111 10000000000 12974844333207 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621849077/5000000000 : ℝ)^4335 ≤ (21473332052051/50000000000000 : ℝ)^3311 := by
    have hnat : (2621849077 : ℕ)^4335*50000000000000^3311 ≤ 21473332052051^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621849077 5000000000 21473332052051 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337230801/2500000000 : ℝ), (-2101853111/10000000000 : ℝ), (2621849077/5000000000 : ℝ)] ![(5509811443289/12500000000000 : ℝ), (12974844333207/100000000000000 : ℝ), (21473332052051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337230801/2500000000 : ℝ)|^4335 ≤ (5509811443289/12500000000000 : ℝ)^3311
        have hw : |(1337230801/2500000000 : ℝ)|=(1337230801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101853111/10000000000 : ℝ)|^4335 ≤ (12974844333207/100000000000000 : ℝ)^3311
        have hw : |(-2101853111/10000000000 : ℝ)|=(2101853111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621849077/5000000000 : ℝ)|^4335 ≤ (21473332052051/50000000000000 : ℝ)^3311
        have hw : |(2621849077/5000000000 : ℝ)|=(2621849077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674461657/5000000000 : ℝ)*x 0 + (5243697409/10000000000 : ℝ)*x 1 + (-2101853953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674461657/5000000000 : ℝ)^4335 ≤ (22039246366563/50000000000000 : ℝ)^3311 := by
    have hnat : (2674461657 : ℕ)^4335*50000000000000^3311 ≤ 22039246366563^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674461657 5000000000 22039246366563 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243697409/10000000000 : ℝ)^4335 ≤ (42946656115369/100000000000000 : ℝ)^3311 := by
    have hnat : (5243697409 : ℕ)^4335*100000000000000^3311 ≤ 42946656115369^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243697409 10000000000 42946656115369 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101853953/10000000000 : ℝ)^4335 ≤ (6487425569211/50000000000000 : ℝ)^3311 := by
    have hnat : (2101853953 : ℕ)^4335*50000000000000^3311 ≤ 6487425569211^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101853953 10000000000 6487425569211 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674461657/5000000000 : ℝ), (5243697409/10000000000 : ℝ), (-2101853953/10000000000 : ℝ)] ![(22039246366563/50000000000000 : ℝ), (42946656115369/100000000000000 : ℝ), (6487425569211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674461657/5000000000 : ℝ)|^4335 ≤ (22039246366563/50000000000000 : ℝ)^3311
        have hw : |(2674461657/5000000000 : ℝ)|=(2674461657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243697409/10000000000 : ℝ)|^4335 ≤ (42946656115369/100000000000000 : ℝ)^3311
        have hw : |(5243697409/10000000000 : ℝ)|=(5243697409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101853953/10000000000 : ℝ)|^4335 ≤ (6487425569211/50000000000000 : ℝ)^3311
        have hw : |(-2101853953/10000000000 : ℝ)|=(2101853953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317925357/10000000000 : ℝ)*x 0 + (4141820251/10000000000 : ℝ)*x 1 + (4500903417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317925357/10000000000 : ℝ)^4335 ≤ (6660485564807/20000000000000 : ℝ)^3311 := by
    have hnat : (4317925357 : ℕ)^4335*20000000000000^3311 ≤ 6660485564807^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317925357 10000000000 6660485564807 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4141820251/10000000000 : ℝ)^4335 ≤ (31535460082007/100000000000000 : ℝ)^3311 := by
    have hnat : (4141820251 : ℕ)^4335*100000000000000^3311 ≤ 31535460082007^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141820251 10000000000 31535460082007 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500903417/10000000000 : ℝ)^4335 ≤ (35162112073637/100000000000000 : ℝ)^3311 := by
    have hnat : (4500903417 : ℕ)^4335*100000000000000^3311 ≤ 35162112073637^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500903417 10000000000 35162112073637 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317925357/10000000000 : ℝ), (4141820251/10000000000 : ℝ), (4500903417/10000000000 : ℝ)] ![(6660485564807/20000000000000 : ℝ), (31535460082007/100000000000000 : ℝ), (35162112073637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317925357/10000000000 : ℝ)|^4335 ≤ (6660485564807/20000000000000 : ℝ)^3311
        have hw : |(4317925357/10000000000 : ℝ)|=(4317925357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4141820251/10000000000 : ℝ)|^4335 ≤ (31535460082007/100000000000000 : ℝ)^3311
        have hw : |(4141820251/10000000000 : ℝ)|=(4141820251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500903417/10000000000 : ℝ)|^4335 ≤ (35162112073637/100000000000000 : ℝ)^3311
        have hw : |(4500903417/10000000000 : ℝ)|=(4500903417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2015580159/10000000000 : ℝ)*x 0 + (2622159811/5000000000 : ℝ)*x 1 + (2706201111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015580159/10000000000 : ℝ)^4335 ≤ (2456407441683/20000000000000 : ℝ)^3311 := by
    have hnat : (2015580159 : ℕ)^4335*20000000000000^3311 ≤ 2456407441683^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015580159 10000000000 2456407441683 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622159811/5000000000 : ℝ)^4335 ≤ (2147666415497/5000000000000 : ℝ)^3311 := by
    have hnat : (2622159811 : ℕ)^4335*5000000000000^3311 ≤ 2147666415497^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622159811 5000000000 2147666415497 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706201111/5000000000 : ℝ)^4335 ≤ (1398894827229/3125000000000 : ℝ)^3311 := by
    have hnat : (2706201111 : ℕ)^4335*3125000000000^3311 ≤ 1398894827229^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706201111 5000000000 1398894827229 3125000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2015580159/10000000000 : ℝ), (2622159811/5000000000 : ℝ), (2706201111/5000000000 : ℝ)] ![(2456407441683/20000000000000 : ℝ), (2147666415497/5000000000000 : ℝ), (1398894827229/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2015580159/10000000000 : ℝ)|^4335 ≤ (2456407441683/20000000000000 : ℝ)^3311
        have hw : |(-2015580159/10000000000 : ℝ)|=(2015580159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622159811/5000000000 : ℝ)|^4335 ≤ (2147666415497/5000000000000 : ℝ)^3311
        have hw : |(2622159811/5000000000 : ℝ)|=(2622159811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706201111/5000000000 : ℝ)|^4335 ≤ (1398894827229/3125000000000 : ℝ)^3311
        have hw : |(2706201111/5000000000 : ℝ)|=(2706201111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305146691/10000000000 : ℝ)*x 0 + (-1933148839/10000000000 : ℝ)*x 1 + (1353100559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305146691/10000000000 : ℝ)^4335 ≤ (8721355147947/20000000000000 : ℝ)^3311 := by
    have hnat : (5305146691 : ℕ)^4335*20000000000000^3311 ≤ 8721355147947^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305146691 10000000000 8721355147947 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933148839/10000000000 : ℝ)^4335 ≤ (1162858963151/10000000000000 : ℝ)^3311 := by
    have hnat : (1933148839 : ℕ)^4335*10000000000000^3311 ≤ 1162858963151^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933148839 10000000000 1162858963151 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353100559/2500000000 : ℝ)^4335 ≤ (44764634622929/100000000000000 : ℝ)^3311 := by
    have hnat : (1353100559 : ℕ)^4335*100000000000000^3311 ≤ 44764634622929^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353100559 2500000000 44764634622929 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305146691/10000000000 : ℝ), (-1933148839/10000000000 : ℝ), (1353100559/2500000000 : ℝ)] ![(8721355147947/20000000000000 : ℝ), (1162858963151/10000000000000 : ℝ), (44764634622929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305146691/10000000000 : ℝ)|^4335 ≤ (8721355147947/20000000000000 : ℝ)^3311
        have hw : |(5305146691/10000000000 : ℝ)|=(5305146691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933148839/10000000000 : ℝ)|^4335 ≤ (1162858963151/10000000000000 : ℝ)^3311
        have hw : |(-1933148839/10000000000 : ℝ)|=(1933148839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353100559/2500000000 : ℝ)|^4335 ≤ (44764634622929/100000000000000 : ℝ)^3311
        have hw : |(1353100559/2500000000 : ℝ)|=(1353100559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652573357/5000000000 : ℝ)*x 0 + (5412402213/10000000000 : ℝ)*x 1 + (-966574419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652573357/5000000000 : ℝ)^4335 ≤ (43606775987257/100000000000000 : ℝ)^3311 := by
    have hnat : (2652573357 : ℕ)^4335*100000000000000^3311 ≤ 43606775987257^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652573357 5000000000 43606775987257 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412402213/10000000000 : ℝ)^4335 ≤ (4476463437387/10000000000000 : ℝ)^3311 := by
    have hnat : (5412402213 : ℕ)^4335*10000000000000^3311 ≤ 4476463437387^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412402213 10000000000 4476463437387 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966574419/5000000000 : ℝ)^4335 ≤ (5814294811817/50000000000000 : ℝ)^3311 := by
    have hnat : (966574419 : ℕ)^4335*50000000000000^3311 ≤ 5814294811817^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966574419 5000000000 5814294811817 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652573357/5000000000 : ℝ), (5412402213/10000000000 : ℝ), (-966574419/5000000000 : ℝ)] ![(43606775987257/100000000000000 : ℝ), (4476463437387/10000000000000 : ℝ), (5814294811817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652573357/5000000000 : ℝ)|^4335 ≤ (43606775987257/100000000000000 : ℝ)^3311
        have hw : |(2652573357/5000000000 : ℝ)|=(2652573357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412402213/10000000000 : ℝ)|^4335 ≤ (4476463437387/10000000000000 : ℝ)^3311
        have hw : |(5412402213/10000000000 : ℝ)|=(5412402213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966574419/5000000000 : ℝ)|^4335 ≤ (5814294811817/50000000000000 : ℝ)^3311
        have hw : |(-966574419/5000000000 : ℝ)|=(966574419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s4_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317951577/10000000000 : ℝ)*x 0 + (2249792163/5000000000 : ℝ)*x 1 + (4143147013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317951577/10000000000 : ℝ)^4335 ≤ (33302692590991/100000000000000 : ℝ)^3311 := by
    have hnat : (4317951577 : ℕ)^4335*100000000000000^3311 ≤ 33302692590991^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317951577 10000000000 33302692590991 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249792163/5000000000 : ℝ)^4335 ≤ (4393577571639/12500000000000 : ℝ)^3311 := by
    have hnat : (2249792163 : ℕ)^4335*12500000000000^3311 ≤ 4393577571639^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249792163 5000000000 4393577571639 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143147013/10000000000 : ℝ)^4335 ≤ (15774343404359/50000000000000 : ℝ)^3311 := by
    have hnat : (4143147013 : ℕ)^4335*50000000000000^3311 ≤ 15774343404359^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143147013 10000000000 15774343404359 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317951577/10000000000 : ℝ), (2249792163/5000000000 : ℝ), (4143147013/10000000000 : ℝ)] ![(33302692590991/100000000000000 : ℝ), (4393577571639/12500000000000 : ℝ), (15774343404359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317951577/10000000000 : ℝ)|^4335 ≤ (33302692590991/100000000000000 : ℝ)^3311
        have hw : |(4317951577/10000000000 : ℝ)|=(4317951577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249792163/5000000000 : ℝ)|^4335 ≤ (4393577571639/12500000000000 : ℝ)^3311
        have hw : |(2249792163/5000000000 : ℝ)|=(2249792163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143147013/10000000000 : ℝ)|^4335 ≤ (15774343404359/50000000000000 : ℝ)^3311
        have hw : |(4143147013/10000000000 : ℝ)|=(4143147013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2237/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5493/50000 : ℝ) ^ (2167/512 : ℝ) ≤ (4359116974715013/50000000000000000000 : ℝ) := by
    have hpowers : (5493/50000 : ℝ)^2167 ≤ (4359116974715013/50000000000000000000 : ℝ)^512 := by
      have hnat : (5493 : ℕ)^2167*50000000000000000000^512 ≤ 4359116974715013^512*50000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5493 50000 4359116974715013 50000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5493/50000 : ℝ)) (X := (4359116974715013/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14981/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (4049961333701191/12500000000000000000 : ℝ) := by
    have hpowers : (14981/100000 : ℝ)^2167 ≤ (4049961333701191/12500000000000000000 : ℝ)^512 := by
      have hnat : (14981 : ℕ)^2167*12500000000000000000^512 ≤ 4049961333701191^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14981 100000 4049961333701191 12500000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14981/100000 : ℝ)) (X := (4049961333701191/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004359116974715013/25000000000000000000 : ℝ) ≤ (1250051493292579/1250000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (25004359116974715013/25000000000000000000 : ℝ)^512 ≤ (1250051493292579/1250000000000000 : ℝ)^2167 := by
      have hnat : (25004359116974715013 : ℕ)^512*1250000000000000^2167 ≤ 1250051493292579^2167*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004359116974715013 25000000000000000000 1250051493292579 1250000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250051493292579/1250000000000000 : ℝ)) (X := (25004359116974715013/25000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020558962309519777/50000000000000000000 : ℝ) ≤ (5000485673111937/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50020558962309519777/50000000000000000000 : ℝ)^512 ≤ (5000485673111937/5000000000000000 : ℝ)^2167 := by
      have hnat : (50020558962309519777 : ℕ)^512*5000000000000000^2167 ≤ 5000485673111937^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020558962309519777 50000000000000000000 5000485673111937 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000485673111937/5000000000000000 : ℝ)) (X := (50020558962309519777/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254049961333701191/6250000000000000000 : ℝ) ≤ (2500382686526779/2500000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (6254049961333701191/6250000000000000000 : ℝ)^512 ≤ (2500382686526779/2500000000000000 : ℝ)^2167 := by
      have hnat : (6254049961333701191 : ℕ)^512*2500000000000000^2167 ≤ 2500382686526779^2167*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254049961333701191 6250000000000000000 2500382686526779 2500000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500382686526779/2500000000000000 : ℝ)) (X := (6254049961333701191/6250000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4359116974715013/50000000000000000000 : ℝ) ≤ ((624052415490566119/624218750000000000 : ℝ)+2*(279699941621/199750000000000 : ℝ)*(5493/50000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (624052415490566119/624218750000000000 : ℝ)+2*(279699941621/199750000000000 : ℝ)*(5493/50000 : ℝ)=(1250051493292579/1250000000000000 : ℝ) by norm_num, show 1+2*(4359116974715013/50000000000000000000 : ℝ)=(25004359116974715013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4049961333701191/12500000000000000000 : ℝ)+(4359116974715013/50000000000000000000 : ℝ) ≤ ((624052415490566119/624218750000000000 : ℝ)+(279699941621/199750000000000 : ℝ)*((14981/100000 : ℝ)+(5493/50000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (624052415490566119/624218750000000000 : ℝ)+(279699941621/199750000000000 : ℝ)*((14981/100000 : ℝ)+(5493/50000 : ℝ))=(5000485673111937/5000000000000000 : ℝ) by norm_num, show 1+(4049961333701191/12500000000000000000 : ℝ)+(4359116974715013/50000000000000000000 : ℝ)=(50020558962309519777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4049961333701191/12500000000000000000 : ℝ) ≤ ((624052415490566119/624218750000000000 : ℝ)+2*(279699941621/199750000000000 : ℝ)*(14981/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (624052415490566119/624218750000000000 : ℝ)+2*(279699941621/199750000000000 : ℝ)*(14981/100000 : ℝ)=(2500382686526779/2500000000000000 : ℝ) by norm_num, show 1+2*(4049961333701191/12500000000000000000 : ℝ)=(6254049961333701191/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (624052415490566119/624218750000000000 : ℝ)*(X 1 0+X 2 0)+(279699941621/199750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (14981/100000 : ℝ)) (c := (624052415490566119/624218750000000000 : ℝ)) (alpha := (279699941621/199750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (624052415490566119/624218750000000000 : ℝ)*(X 0 1+X 2 1)+(279699941621/199750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (14981/100000 : ℝ)) (c := (624052415490566119/624218750000000000 : ℝ)) (alpha := (279699941621/199750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (624052415490566119/624218750000000000 : ℝ)*(X 0 2+X 1 2)+(279699941621/199750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (14981/100000 : ℝ)) (c := (624052415490566119/624218750000000000 : ℝ)) (alpha := (279699941621/199750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2015567743/10000000000 : ℝ)*X 0 0+(2706513653/5000000000 : ℝ)*X 0 1+(5243697623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337230801/2500000000 : ℝ)*X 1 0+(-2101853111/10000000000 : ℝ)*X 1 1+(2621849077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674461657/5000000000 : ℝ)*X 2 0+(5243697409/10000000000 : ℝ)*X 2 1+(-2101853953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317925357/10000000000 : ℝ)*X 0 0+(4141820251/10000000000 : ℝ)*X 0 1+(4500903417/10000000000 : ℝ)*X 0 2+(4317925357/10000000000 : ℝ)*X 1 0+(4141820251/10000000000 : ℝ)*X 1 1+(4500903417/10000000000 : ℝ)*X 1 2+(4317925357/10000000000 : ℝ)*X 2 0+(4141820251/10000000000 : ℝ)*X 2 1+(4500903417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2015580159/10000000000 : ℝ)*X 0 0+(2622159811/5000000000 : ℝ)*X 0 1+(2706201111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305146691/10000000000 : ℝ)*X 1 0+(-1933148839/10000000000 : ℝ)*X 1 1+(1353100559/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652573357/5000000000 : ℝ)*X 2 0+(5412402213/10000000000 : ℝ)*X 2 1+(-966574419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317951577/10000000000 : ℝ)*X 0 0+(2249792163/5000000000 : ℝ)*X 0 1+(4143147013/10000000000 : ℝ)*X 0 2+(4317951577/10000000000 : ℝ)*X 1 0+(2249792163/5000000000 : ℝ)*X 1 1+(4143147013/10000000000 : ℝ)*X 1 2+(4317951577/10000000000 : ℝ)*X 2 0+(2249792163/5000000000 : ℝ)*X 2 1+(4143147013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1881875735381072647401/1175000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43904743/10000000000000 : ℝ)*(base19) + (103857761/20000000000000 : ℝ)*(base23) + (43065729/10000000000000 : ℝ)*(upper3) + (22781271/50000000000000 : ℝ)*(lower4) + (4345280273856639/100000000000000 : ℝ)*(major0) + (4345280273856639/100000000000000 : ℝ)*(major1) + (4345280273856639/100000000000000 : ℝ)*(major2) + (5905661608153613/100000000000000 : ℝ)*(sp0) + (2952833304035663/50000000000000 : ℝ)*(sp1) + (5905651084790171/100000000000000 : ℝ)*(sp2) + (1392439411463057/50000000000000 : ℝ)*(sp3) + (679870643/12500000000000 : ℝ)*(sp4) + (15443039781/100000000000000 : ℝ)*(sp6) + (3656070463/25000000000000 : ℝ)*(sp7) + (556978689441593/20000000000000 : ℝ)*(f.failure) + (5905667047118757/100000000000000 : ℝ)*(f.sum) + (1977833567511/1175000000000000000000000000 : ℝ)*base66 + (1279018302702947/229492187500000000000000000000 : ℝ)*base68 + (59078292026294027/3671875000000000000000000000000 : ℝ)*base70 + (5154472530798299/1835937500000000000000000000000 : ℝ)*base71 + (1001325508143/587500000000000000000000000 : ℝ)*base74 + (34767465086892049/1835937500000000000000000000000 : ℝ)*base75 + (23256527771076701/1835937500000000000000000000000 : ℝ)*base78 + (12445371669704549/1835937500000000000000000000000 : ℝ)*base79 + (4189123908061/1175000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1334793/500000000000000000000 : ℝ)*base90 + (1334793/500000000000000000000 : ℝ)*base92 + (1334793/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194940373888786698743259/19975000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1623119623/100000000000000 : ℝ)*(base19) + (1805232453/100000000000000 : ℝ)*(base23) + (20079263/10000000000000 : ℝ)*(upper3) + (69884931/100000000000000 : ℝ)*(lower4) + (197779327/100000000000000 : ℝ)*(upper5) + (1094374609698721/25000000000000 : ℝ)*(major0) + (1094374609698721/25000000000000 : ℝ)*(major1) + (1094374609698721/25000000000000 : ℝ)*(major2) + (4091176957/12500000000000 : ℝ)*(sp1) + (17854610177/50000000000000 : ℝ)*(sp2) + (743681807318961/12500000000000 : ℝ)*(sp4) + (5949420106016409/100000000000000 : ℝ)*(sp5) + (5949416944098881/100000000000000 : ℝ)*(sp6) + (2739787200909/97656250000 : ℝ)*(sp7) + (2739787200909/97656250000 : ℝ)*(f.failure) + (743681807318961/12500000000000 : ℝ)*(f.sum) + (3667636462817/1248437500000000000000000000 : ℝ)*base66 + (28963035582878269/3901367187500000000000000000000 : ℝ)*base68 + (21839105515534519/3901367187500000000000000000000 : ℝ)*base70 + (205465583871057071/62421875000000000000000000000000 : ℝ)*base71 + (23443219419847/19975000000000000000000000000 : ℝ)*base74 + (22550728117783799/15605468750000000000000000000000 : ℝ)*base75 + (189552199152479277/31210937500000000000000000000000 : ℝ)*base78 + (446985482400744571/62421875000000000000000000000000 : ℝ)*base79 + (512768885127/312109375000000000000000000 : ℝ)*base81 + (60661/9765625000000000000 : ℝ)*base90 + (60661/9765625000000000000 : ℝ)*base92 + (60661/9765625000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1375_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1375_s5_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2015764973/10000000000 : ℝ)*x 0 + (67641183/125000000 : ℝ)*x 1 + (2622650249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015764973/10000000000 : ℝ)^4335 ≤ (6141755848271/50000000000000 : ℝ)^3311 := by
    have hnat : (2015764973 : ℕ)^4335*50000000000000^3311 ≤ 6141755848271^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015764973 10000000000 6141755848271 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67641183/125000000 : ℝ)^4335 ≤ (11188160304237/25000000000000 : ℝ)^3311 := by
    have hnat : (67641183 : ℕ)^4335*25000000000000^3311 ≤ 11188160304237^3311*125000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67641183 125000000 11188160304237 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622650249/5000000000 : ℝ)^4335 ≤ (1718553882519/4000000000000 : ℝ)^3311 := by
    have hnat : (2622650249 : ℕ)^4335*4000000000000^3311 ≤ 1718553882519^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622650249 5000000000 1718553882519 4000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2015764973/10000000000 : ℝ), (67641183/125000000 : ℝ), (2622650249/5000000000 : ℝ)] ![(6141755848271/50000000000000 : ℝ), (11188160304237/25000000000000 : ℝ), (1718553882519/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2015764973/10000000000 : ℝ)|^4335 ≤ (6141755848271/50000000000000 : ℝ)^3311
        have hw : |(-2015764973/10000000000 : ℝ)|=(2015764973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67641183/125000000 : ℝ)|^4335 ≤ (11188160304237/25000000000000 : ℝ)^3311
        have hw : |(67641183/125000000 : ℝ)|=(67641183/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622650249/5000000000 : ℝ)|^4335 ≤ (1718553882519/4000000000000 : ℝ)^3311
        have hw : |(2622650249/5000000000 : ℝ)|=(2622650249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348479003/10000000000 : ℝ)*x 0 + (-210031993/1000000000 : ℝ)*x 1 + (1049060093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348479003/10000000000 : ℝ)^4335 ≤ (4407369902297/10000000000000 : ℝ)^3311 := by
    have hnat : (5348479003 : ℕ)^4335*10000000000000^3311 ≤ 4407369902297^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348479003 10000000000 4407369902297 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210031993/1000000000 : ℝ)^4335 ≤ (1620306781527/12500000000000 : ℝ)^3311 := by
    have hnat : (210031993 : ℕ)^4335*12500000000000^3311 ≤ 1620306781527^3311*1000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210031993 1000000000 1620306781527 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049060093/2000000000 : ℝ)^4335 ≤ (21481923354539/50000000000000 : ℝ)^3311 := by
    have hnat : (1049060093 : ℕ)^4335*50000000000000^3311 ≤ 21481923354539^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049060093 2000000000 21481923354539 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348479003/10000000000 : ℝ), (-210031993/1000000000 : ℝ), (1049060093/2000000000 : ℝ)] ![(4407369902297/10000000000000 : ℝ), (1620306781527/12500000000000 : ℝ), (21481923354539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348479003/10000000000 : ℝ)|^4335 ≤ (4407369902297/10000000000000 : ℝ)^3311
        have hw : |(5348479003/10000000000 : ℝ)|=(5348479003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210031993/1000000000 : ℝ)|^4335 ≤ (1620306781527/12500000000000 : ℝ)^3311
        have hw : |(-210031993/1000000000 : ℝ)|=(210031993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049060093/2000000000 : ℝ)|^4335 ≤ (21481923354539/50000000000000 : ℝ)^3311
        have hw : |(1049060093/2000000000 : ℝ)|=(1049060093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348479049/10000000000 : ℝ)*x 0 + (5245300497/10000000000 : ℝ)*x 1 + (-2100319827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348479049/10000000000 : ℝ)^4335 ≤ (22036849759631/50000000000000 : ℝ)^3311 := by
    have hnat : (5348479049 : ℕ)^4335*50000000000000^3311 ≤ 22036849759631^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348479049 10000000000 22036849759631 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245300497/10000000000 : ℝ)^4335 ≤ (42963847052251/100000000000000 : ℝ)^3311 := by
    have hnat : (5245300497 : ℕ)^4335*100000000000000^3311 ≤ 42963847052251^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245300497 10000000000 42963847052251 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100319827/10000000000 : ℝ)^4335 ≤ (12962453419937/100000000000000 : ℝ)^3311 := by
    have hnat : (2100319827 : ℕ)^4335*100000000000000^3311 ≤ 12962453419937^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100319827 10000000000 12962453419937 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348479049/10000000000 : ℝ), (5245300497/10000000000 : ℝ), (-2100319827/10000000000 : ℝ)] ![(22036849759631/50000000000000 : ℝ), (42963847052251/100000000000000 : ℝ), (12962453419937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348479049/10000000000 : ℝ)|^4335 ≤ (22036849759631/50000000000000 : ℝ)^3311
        have hw : |(5348479049/10000000000 : ℝ)|=(5348479049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245300497/10000000000 : ℝ)|^4335 ≤ (42963847052251/100000000000000 : ℝ)^3311
        have hw : |(5245300497/10000000000 : ℝ)|=(5245300497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100319827/10000000000 : ℝ)|^4335 ≤ (12962453419937/100000000000000 : ℝ)^3311
        have hw : |(-2100319827/10000000000 : ℝ)|=(2100319827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079510917/2500000000 : ℝ)*x 0 + (1036335977/2500000000 : ℝ)*x 1 + (1124337881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079510917/2500000000 : ℝ)^4335 ≤ (33303622520701/100000000000000 : ℝ)^3311 := by
    have hnat : (1079510917 : ℕ)^4335*100000000000000^3311 ≤ 33303622520701^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079510917 2500000000 33303622520701 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036335977/2500000000 : ℝ)^4335 ≤ (15785295463319/50000000000000 : ℝ)^3311 := by
    have hnat : (1036335977 : ℕ)^4335*50000000000000^3311 ≤ 15785295463319^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036335977 2500000000 15785295463319 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124337881/2500000000 : ℝ)^4335 ≤ (1405031461459/4000000000000 : ℝ)^3311 := by
    have hnat : (1124337881 : ℕ)^4335*4000000000000^3311 ≤ 1405031461459^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124337881 2500000000 1405031461459 4000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079510917/2500000000 : ℝ), (1036335977/2500000000 : ℝ), (1124337881/2500000000 : ℝ)] ![(33303622520701/100000000000000 : ℝ), (15785295463319/50000000000000 : ℝ), (1405031461459/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079510917/2500000000 : ℝ)|^4335 ≤ (33303622520701/100000000000000 : ℝ)^3311
        have hw : |(1079510917/2500000000 : ℝ)|=(1079510917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036335977/2500000000 : ℝ)|^4335 ≤ (15785295463319/50000000000000 : ℝ)^3311
        have hw : |(1036335977/2500000000 : ℝ)|=(1036335977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124337881/2500000000 : ℝ)|^4335 ≤ (1405031461459/4000000000000 : ℝ)^3311
        have hw : |(1124337881/2500000000 : ℝ)|=(1124337881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7874129/39062500 : ℝ)*x 0 + (5245898459/10000000000 : ℝ)*x 1 + (5410693513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7874129/39062500 : ℝ)^4335 ≤ (12283607843613/100000000000000 : ℝ)^3311 := by
    have hnat : (7874129 : ℕ)^4335*100000000000000^3311 ≤ 12283607843613^3311*39062500^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7874129 39062500 12283607843613 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245898459/10000000000 : ℝ)^4335 ≤ (42970259796959/100000000000000 : ℝ)^3311 := by
    have hnat : (5245898459 : ℕ)^4335*100000000000000^3311 ≤ 42970259796959^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245898459 10000000000 42970259796959 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410693513/10000000000 : ℝ)^4335 ≤ (8949226467627/20000000000000 : ℝ)^3311 := by
    have hnat : (5410693513 : ℕ)^4335*20000000000000^3311 ≤ 8949226467627^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410693513 10000000000 8949226467627 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7874129/39062500 : ℝ), (5245898459/10000000000 : ℝ), (5410693513/10000000000 : ℝ)] ![(12283607843613/100000000000000 : ℝ), (42970259796959/100000000000000 : ℝ), (8949226467627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7874129/39062500 : ℝ)|^4335 ≤ (12283607843613/100000000000000 : ℝ)^3311
        have hw : |(-7874129/39062500 : ℝ)|=(7874129/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245898459/10000000000 : ℝ)|^4335 ≤ (42970259796959/100000000000000 : ℝ)^3311
        have hw : |(5245898459/10000000000 : ℝ)|=(5245898459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410693513/10000000000 : ℝ)|^4335 ≤ (8949226467627/20000000000000 : ℝ)^3311
        have hw : |(5410693513/10000000000 : ℝ)|=(5410693513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165798891/312500000 : ℝ)*x 0 + (-386985383/2000000000 : ℝ)*x 1 + (1352673379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165798891/312500000 : ℝ)^4335 ≤ (43611272316931/100000000000000 : ℝ)^3311 := by
    have hnat : (165798891 : ℕ)^4335*100000000000000^3311 ≤ 43611272316931^3311*312500000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165798891 312500000 43611272316931 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386985383/2000000000 : ℝ)^4335 ≤ (5821297648439/50000000000000 : ℝ)^3311 := by
    have hnat : (386985383 : ℕ)^4335*50000000000000^3311 ≤ 5821297648439^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386985383 2000000000 5821297648439 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352673379/2500000000 : ℝ)^4335 ≤ (22373066185309/50000000000000 : ℝ)^3311 := by
    have hnat : (1352673379 : ℕ)^4335*50000000000000^3311 ≤ 22373066185309^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352673379 2500000000 22373066185309 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165798891/312500000 : ℝ), (-386985383/2000000000 : ℝ), (1352673379/2500000000 : ℝ)] ![(43611272316931/100000000000000 : ℝ), (5821297648439/50000000000000 : ℝ), (22373066185309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165798891/312500000 : ℝ)|^4335 ≤ (43611272316931/100000000000000 : ℝ)^3311
        have hw : |(165798891/312500000 : ℝ)|=(165798891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386985383/2000000000 : ℝ)|^4335 ≤ (5821297648439/50000000000000 : ℝ)^3311
        have hw : |(-386985383/2000000000 : ℝ)|=(386985383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352673379/2500000000 : ℝ)|^4335 ≤ (22373066185309/50000000000000 : ℝ)^3311
        have hw : |(1352673379/2500000000 : ℝ)|=(1352673379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165798891/312500000 : ℝ)*x 0 + (2705346757/5000000000 : ℝ)*x 1 + (-967463459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165798891/312500000 : ℝ)^4335 ≤ (43611272316931/100000000000000 : ℝ)^3311 := by
    have hnat : (165798891 : ℕ)^4335*100000000000000^3311 ≤ 43611272316931^3311*312500000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165798891 312500000 43611272316931 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705346757/5000000000 : ℝ)^4335 ≤ (22373066174481/50000000000000 : ℝ)^3311 := by
    have hnat : (2705346757 : ℕ)^4335*50000000000000^3311 ≤ 22373066174481^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705346757 5000000000 22373066174481 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967463459/5000000000 : ℝ)^4335 ≤ (181915551883/1562500000000 : ℝ)^3311 := by
    have hnat : (967463459 : ℕ)^4335*1562500000000^3311 ≤ 181915551883^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967463459 5000000000 181915551883 1562500000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165798891/312500000 : ℝ), (2705346757/5000000000 : ℝ), (-967463459/5000000000 : ℝ)] ![(43611272316931/100000000000000 : ℝ), (22373066174481/50000000000000 : ℝ), (181915551883/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165798891/312500000 : ℝ)|^4335 ≤ (43611272316931/100000000000000 : ℝ)^3311
        have hw : |(165798891/312500000 : ℝ)|=(165798891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705346757/5000000000 : ℝ)|^4335 ≤ (22373066174481/50000000000000 : ℝ)^3311
        have hw : |(2705346757/5000000000 : ℝ)|=(2705346757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-967463459/5000000000 : ℝ)|^4335 ≤ (181915551883/1562500000000 : ℝ)^3311
        have hw : |(-967463459/5000000000 : ℝ)|=(967463459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s5_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079517339/2500000000 : ℝ)*x 0 + (2248041841/5000000000 : ℝ)*x 1 + (4146617983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079517339/2500000000 : ℝ)^4335 ≤ (16651940958883/50000000000000 : ℝ)^3311 := by
    have hnat : (1079517339 : ℕ)^4335*50000000000000^3311 ≤ 16651940958883^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079517339 2500000000 16651940958883 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248041841/5000000000 : ℝ)^4335 ≤ (4389102793467/12500000000000 : ℝ)^3311 := by
    have hnat : (2248041841 : ℕ)^4335*12500000000000^3311 ≤ 4389102793467^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248041841 5000000000 4389102793467 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146617983/10000000000 : ℝ)^4335 ≤ (3158329572271/10000000000000 : ℝ)^3311 := by
    have hnat : (4146617983 : ℕ)^4335*10000000000000^3311 ≤ 3158329572271^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146617983 10000000000 3158329572271 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079517339/2500000000 : ℝ), (2248041841/5000000000 : ℝ), (4146617983/10000000000 : ℝ)] ![(16651940958883/50000000000000 : ℝ), (4389102793467/12500000000000 : ℝ), (3158329572271/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079517339/2500000000 : ℝ)|^4335 ≤ (16651940958883/50000000000000 : ℝ)^3311
        have hw : |(1079517339/2500000000 : ℝ)|=(1079517339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248041841/5000000000 : ℝ)|^4335 ≤ (4389102793467/12500000000000 : ℝ)^3311
        have hw : |(2248041841/5000000000 : ℝ)|=(2248041841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146617983/10000000000 : ℝ)|^4335 ≤ (3158329572271/10000000000000 : ℝ)^3311
        have hw : |(4146617983/10000000000 : ℝ)|=(4146617983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2237/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2237/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2237/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2237/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2237/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2237/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2237/20000 : ℝ) ^ (2167/512 : ℝ) ≤ (9406458555594749/100000000000000000000 : ℝ) := by
    have hpowers : (2237/20000 : ℝ)^2167 ≤ (9406458555594749/100000000000000000000 : ℝ)^512 := by
      have hnat : (2237 : ℕ)^2167*100000000000000000000^512 ≤ 9406458555594749^512*20000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2237 20000 9406458555594749 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2237/20000 : ℝ)) (X := (9406458555594749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (2167/512 : ℝ) ≤ (190698754205121/625000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^2167 ≤ (190698754205121/625000000000000000 : ℝ)^512 := by
      have hnat : (1477 : ℕ)^2167*625000000000000000^512 ≤ 190698754205121^512*10000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 190698754205121 625000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (190698754205121/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009406458555594749/50000000000000000000 : ℝ) ≤ (2000088892677997/2000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50009406458555594749/50000000000000000000 : ℝ)^512 ≤ (2000088892677997/2000000000000000 : ℝ)^2167 := by
      have hnat : (50009406458555594749 : ℕ)^512*2000000000000000^2167 ≤ 2000088892677997^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009406458555594749 50000000000000000000 2000088892677997 2000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088892677997/2000000000000000 : ℝ)) (X := (50009406458555594749/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039918259228414109/100000000000000000000 : ℝ) ≤ (5000471505168331/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (100039918259228414109/100000000000000000000 : ℝ)^512 ≤ (5000471505168331/5000000000000000 : ℝ)^2167 := by
      have hnat : (100039918259228414109 : ℕ)^512*5000000000000000^2167 ≤ 5000471505168331^2167*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039918259228414109 100000000000000000000 5000471505168331 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000471505168331/5000000000000000 : ℝ)) (X := (100039918259228414109/100000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (312690698754205121/312500000000000000 : ℝ) ≤ (10001441557283339/10000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (312690698754205121/312500000000000000 : ℝ)^512 ≤ (10001441557283339/10000000000000000 : ℝ)^2167 := by
      have hnat : (312690698754205121 : ℕ)^512*10000000000000000^2167 ≤ 10001441557283339^2167*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312690698754205121 312500000000000000 10001441557283339 10000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001441557283339/10000000000000000 : ℝ)) (X := (312690698754205121/312500000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9406458555594749/100000000000000000000 : ℝ) ≤ ((2389362727070395449/2390000000000000000 : ℝ)+2*(166182315559/119500000000000 : ℝ)*(2237/20000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (2389362727070395449/2390000000000000000 : ℝ)+2*(166182315559/119500000000000 : ℝ)*(2237/20000 : ℝ)=(2000088892677997/2000000000000000 : ℝ) by norm_num, show 1+2*(9406458555594749/100000000000000000000 : ℝ)=(50009406458555594749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(190698754205121/625000000000000000 : ℝ)+(9406458555594749/100000000000000000000 : ℝ) ≤ ((2389362727070395449/2390000000000000000 : ℝ)+(166182315559/119500000000000 : ℝ)*((1477/10000 : ℝ)+(2237/20000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (2389362727070395449/2390000000000000000 : ℝ)+(166182315559/119500000000000 : ℝ)*((1477/10000 : ℝ)+(2237/20000 : ℝ))=(5000471505168331/5000000000000000 : ℝ) by norm_num, show 1+(190698754205121/625000000000000000 : ℝ)+(9406458555594749/100000000000000000000 : ℝ)=(100039918259228414109/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(190698754205121/625000000000000000 : ℝ) ≤ ((2389362727070395449/2390000000000000000 : ℝ)+2*(166182315559/119500000000000 : ℝ)*(1477/10000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (2389362727070395449/2390000000000000000 : ℝ)+2*(166182315559/119500000000000 : ℝ)*(1477/10000 : ℝ)=(10001441557283339/10000000000000000 : ℝ) by norm_num, show 1+2*(190698754205121/625000000000000000 : ℝ)=(312690698754205121/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2389362727070395449/2390000000000000000 : ℝ)*(X 1 0+X 2 0)+(166182315559/119500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (2389362727070395449/2390000000000000000 : ℝ)) (alpha := (166182315559/119500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2389362727070395449/2390000000000000000 : ℝ)*(X 0 1+X 2 1)+(166182315559/119500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (2389362727070395449/2390000000000000000 : ℝ)) (alpha := (166182315559/119500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2389362727070395449/2390000000000000000 : ℝ)*(X 0 2+X 1 2)+(166182315559/119500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (2389362727070395449/2390000000000000000 : ℝ)) (alpha := (166182315559/119500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2015764973/10000000000 : ℝ)*X 0 0+(67641183/125000000 : ℝ)*X 0 1+(2622650249/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348479003/10000000000 : ℝ)*X 1 0+(-210031993/1000000000 : ℝ)*X 1 1+(1049060093/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348479049/10000000000 : ℝ)*X 2 0+(5245300497/10000000000 : ℝ)*X 2 1+(-2100319827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079510917/2500000000 : ℝ)*X 0 0+(1036335977/2500000000 : ℝ)*X 0 1+(1124337881/2500000000 : ℝ)*X 0 2+(1079510917/2500000000 : ℝ)*X 1 0+(1036335977/2500000000 : ℝ)*X 1 1+(1124337881/2500000000 : ℝ)*X 1 2+(1079510917/2500000000 : ℝ)*X 2 0+(1036335977/2500000000 : ℝ)*X 2 1+(1124337881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7874129/39062500 : ℝ)*X 0 0+(5245898459/10000000000 : ℝ)*X 0 1+(5410693513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165798891/312500000 : ℝ)*X 1 0+(-386985383/2000000000 : ℝ)*X 1 1+(1352673379/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165798891/312500000 : ℝ)*X 2 0+(2705346757/5000000000 : ℝ)*X 2 1+(-967463459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079517339/2500000000 : ℝ)*X 0 0+(2248041841/5000000000 : ℝ)*X 0 1+(4146617983/10000000000 : ℝ)*X 0 2+(1079517339/2500000000 : ℝ)*X 1 0+(2248041841/5000000000 : ℝ)*X 1 1+(4146617983/10000000000 : ℝ)*X 1 2+(1079517339/2500000000 : ℝ)*X 2 0+(2248041841/5000000000 : ℝ)*X 2 1+(4146617983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (554219744226868003735364619/119500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (160725247/25000000000000 : ℝ)*(base19) + (701413177/100000000000000 : ℝ)*(base23) + (4136393/50000000000000 : ℝ)*(upper4) + (18347451/50000000000000 : ℝ)*(upper5) + (4432602703306741/100000000000000 : ℝ)*(major0) + (4432602703306741/100000000000000 : ℝ)*(major1) + (4432602703306741/100000000000000 : ℝ)*(major2) + (150608168758563/2500000000000 : ℝ)*(sp0) + (6024343387480217/100000000000000 : ℝ)*(sp1) + (6024346091651381/100000000000000 : ℝ)*(sp2) + (710213284305157/25000000000000 : ℝ)*(sp3) + (10021361019/50000000000000 : ℝ)*(sp4) + (2762683353/100000000000000 : ℝ)*(sp5) + (665216777/12500000000000 : ℝ)*(sp7) + (710214614738711/25000000000000 : ℝ)*(f.failure) + (3012173396532279/50000000000000 : ℝ)*(f.sum) + (18379896253419/5975000000000000000000000000 : ℝ)*base65 + (1326066159539801709/239000000000000000000000000000000 : ℝ)*base67 + (2040358749375801709/239000000000000000000000000000000 : ℝ)*base69 + (1509381308388801709/239000000000000000000000000000000 : ℝ)*base71 + (7131067082747/2987500000000000000000000000 : ℝ)*base73 + (5254591931214801709/239000000000000000000000000000000 : ℝ)*base75 + (2508863944990801709/239000000000000000000000000000000 : ℝ)*base77 + (2195929576054801709/239000000000000000000000000000000 : ℝ)*base79 + (1558851328261/1493750000000000000000000000 : ℝ)*base81 + (2785111/625000000000000000000 : ℝ)*base90 + (2785111/625000000000000000000 : ℝ)*base92 + (2785111/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128733708885018591318467409/59750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (377130027/100000000000000 : ℝ)*(base19) + (50549709/12500000000000 : ℝ)*(base23) + (45376849/100000000000000 : ℝ)*(upper3) + (3173979/25000000000000 : ℝ)*(lower4) + (4500679/10000000000000 : ℝ)*(upper5) + (4464827070744653/100000000000000 : ℝ)*(major0) + (4464827070744653/100000000000000 : ℝ)*(major1) + (4464827070744653/100000000000000 : ℝ)*(major2) + (7831049651/100000000000000 : ℝ)*(sp1) + (8243747149/100000000000000 : ℝ)*(sp2) + (1517035747251713/25000000000000 : ℝ)*(sp4) + (3034067390413587/50000000000000 : ℝ)*(sp5) + (6068134340862031/100000000000000 : ℝ)*(sp6) + (286151108066447/10000000000000 : ℝ)*(sp7) + (286151108066447/10000000000000 : ℝ)*(f.failure) + (1517035747251713/25000000000000 : ℝ)*(f.sum) + (11687298954173/5975000000000000000000000000 : ℝ)*base66 + (4774078028420824197/239000000000000000000000000000000 : ℝ)*base67 + (4683808809178824197/239000000000000000000000000000000 : ℝ)*base69 + (1889302916453824197/239000000000000000000000000000000 : ℝ)*base71 + (22080216203527/5975000000000000000000000000 : ℝ)*base73 + (783995051918175803/239000000000000000000000000000000 : ℝ)*base76 + (3648773562905824197/239000000000000000000000000000000 : ℝ)*base77 + (5910437246779824197/239000000000000000000000000000000 : ℝ)*base79 + (7861739560063/1493750000000000000000000000 : ℝ)*base81 + (2569247/250000000000000000000 : ℝ)*base90 + (2569247/250000000000000000000 : ℝ)*base92 + (2569247/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1375_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1375_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1375_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1375_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1375_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1375_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
