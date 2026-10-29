-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:53.847871+00:00
-- url     : https://prove2.me/submissions/43fb85d6-9daf-4f1c-bf3e-7ac5e7926443

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
theorem support_rectangle_w1380_s3_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010183909/10000000000 : ℝ)*x 0 + (542255699/1000000000 : ℝ)*x 1 + (2617408833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010183909/10000000000 : ℝ)^1085 ≤ (6124081685957/50000000000000 : ℝ)^829 := by
    have hnat : (2010183909 : ℕ)^1085*50000000000000^829 ≤ 6124081685957^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010183909 10000000000 6124081685957 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542255699/1000000000 : ℝ)^1085 ≤ (22443719083603/50000000000000 : ℝ)^829 := by
    have hnat : (542255699 : ℕ)^1085*50000000000000^829 ≤ 22443719083603^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542255699 1000000000 22443719083603 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617408833/5000000000 : ℝ)^1085 ≤ (2143219922473/5000000000000 : ℝ)^829 := by
    have hnat : (2617408833 : ℕ)^1085*5000000000000^829 ≤ 2143219922473^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617408833 5000000000 2143219922473 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010183909/10000000000 : ℝ), (542255699/1000000000 : ℝ), (2617408833/5000000000 : ℝ)] ![(6124081685957/50000000000000 : ℝ), (22443719083603/50000000000000 : ℝ), (2143219922473/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010183909/10000000000 : ℝ)|^1085 ≤ (6124081685957/50000000000000 : ℝ)^829
        have hw : |(-2010183909/10000000000 : ℝ)|=(2010183909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542255699/1000000000 : ℝ)|^1085 ≤ (22443719083603/50000000000000 : ℝ)^829
        have hw : |(542255699/1000000000 : ℝ)|=(542255699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617408833/5000000000 : ℝ)|^1085 ≤ (2143219922473/5000000000000 : ℝ)^829
        have hw : |(2617408833/5000000000 : ℝ)|=(2617408833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (535133751/1000000000 : ℝ)*x 0 + (-2106045491/10000000000 : ℝ)*x 1 + (1046963651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535133751/1000000000 : ℝ)^1085 ≤ (22058701634301/50000000000000 : ℝ)^829 := by
    have hnat : (535133751 : ℕ)^1085*50000000000000^829 ≤ 22058701634301^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535133751 1000000000 22058701634301 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106045491/10000000000 : ℝ)^1085 ≤ (813636997447/6250000000000 : ℝ)^829 := by
    have hnat : (2106045491 : ℕ)^1085*6250000000000^829 ≤ 813636997447^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106045491 10000000000 813636997447 6250000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046963651/2000000000 : ℝ)^1085 ≤ (10716101190433/25000000000000 : ℝ)^829 := by
    have hnat : (1046963651 : ℕ)^1085*25000000000000^829 ≤ 10716101190433^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046963651 2000000000 10716101190433 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535133751/1000000000 : ℝ), (-2106045491/10000000000 : ℝ), (1046963651/2000000000 : ℝ)] ![(22058701634301/50000000000000 : ℝ), (813636997447/6250000000000 : ℝ), (10716101190433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535133751/1000000000 : ℝ)|^1085 ≤ (22058701634301/50000000000000 : ℝ)^829
        have hw : |(535133751/1000000000 : ℝ)|=(535133751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106045491/10000000000 : ℝ)|^1085 ≤ (813636997447/6250000000000 : ℝ)^829
        have hw : |(-2106045491/10000000000 : ℝ)|=(2106045491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046963651/2000000000 : ℝ)|^1085 ≤ (10716101190433/25000000000000 : ℝ)^829
        have hw : |(1046963651/2000000000 : ℝ)|=(1046963651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5351337469/10000000000 : ℝ)*x 0 + (2617409197/5000000000 : ℝ)*x 1 + (-2106045361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351337469/10000000000 : ℝ)^1085 ≤ (44117402826211/100000000000000 : ℝ)^829 := by
    have hnat : (5351337469 : ℕ)^1085*100000000000000^829 ≤ 44117402826211^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351337469 10000000000 44117402826211 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617409197/5000000000 : ℝ)^1085 ≤ (8572881250277/20000000000000 : ℝ)^829 := by
    have hnat : (2617409197 : ℕ)^1085*20000000000000^829 ≤ 8572881250277^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617409197 5000000000 8572881250277 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106045361/10000000000 : ℝ)^1085 ≤ (3254547726857/25000000000000 : ℝ)^829 := by
    have hnat : (2106045361 : ℕ)^1085*25000000000000^829 ≤ 3254547726857^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106045361 10000000000 3254547726857 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351337469/10000000000 : ℝ), (2617409197/5000000000 : ℝ), (-2106045361/10000000000 : ℝ)] ![(44117402826211/100000000000000 : ℝ), (8572881250277/20000000000000 : ℝ), (3254547726857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351337469/10000000000 : ℝ)|^1085 ≤ (44117402826211/100000000000000 : ℝ)^829
        have hw : |(5351337469/10000000000 : ℝ)|=(5351337469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617409197/5000000000 : ℝ)|^1085 ≤ (8572881250277/20000000000000 : ℝ)^829
        have hw : |(2617409197/5000000000 : ℝ)|=(2617409197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106045361/10000000000 : ℝ)|^1085 ≤ (3254547726857/25000000000000 : ℝ)^829
        have hw : |(-2106045361/10000000000 : ℝ)|=(2106045361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1078981151/2500000000 : ℝ)*x 0 + (4120726733/10000000000 : ℝ)*x 1 + (4519586333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078981151/2500000000 : ℝ)^1085 ≤ (8323817498451/25000000000000 : ℝ)^829 := by
    have hnat : (1078981151 : ℕ)^1085*25000000000000^829 ≤ 8323817498451^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078981151 2500000000 8323817498451 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4120726733/10000000000 : ℝ)^1085 ≤ (31338304775841/100000000000000 : ℝ)^829 := by
    have hnat : (4120726733 : ℕ)^1085*100000000000000^829 ≤ 31338304775841^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120726733 10000000000 31338304775841 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519586333/10000000000 : ℝ)^1085 ≤ (17683212604263/50000000000000 : ℝ)^829 := by
    have hnat : (4519586333 : ℕ)^1085*50000000000000^829 ≤ 17683212604263^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519586333 10000000000 17683212604263 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078981151/2500000000 : ℝ), (4120726733/10000000000 : ℝ), (4519586333/10000000000 : ℝ)] ![(8323817498451/25000000000000 : ℝ), (31338304775841/100000000000000 : ℝ), (17683212604263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078981151/2500000000 : ℝ)|^1085 ≤ (8323817498451/25000000000000 : ℝ)^829
        have hw : |(1078981151/2500000000 : ℝ)|=(1078981151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4120726733/10000000000 : ℝ)|^1085 ≤ (31338304775841/100000000000000 : ℝ)^829
        have hw : |(4120726733/10000000000 : ℝ)|=(4120726733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519586333/10000000000 : ℝ)|^1085 ≤ (17683212604263/50000000000000 : ℝ)^829
        have hw : |(4519586333/10000000000 : ℝ)|=(4519586333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005100777/5000000000 : ℝ)*x 0 + (2617792199/5000000000 : ℝ)*x 1 + (2710892767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005100777/5000000000 : ℝ)^1085 ≤ (12248304084401/100000000000000 : ℝ)^829 := by
    have hnat : (1005100777 : ℕ)^1085*100000000000000^829 ≤ 12248304084401^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005100777 5000000000 12248304084401 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617792199/5000000000 : ℝ)^1085 ≤ (42872615648219/100000000000000 : ℝ)^829 := by
    have hnat : (2617792199 : ℕ)^1085*100000000000000^829 ≤ 42872615648219^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617792199 5000000000 42872615648219 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710892767/5000000000 : ℝ)^1085 ≤ (2243954013021/5000000000000 : ℝ)^829 := by
    have hnat : (2710892767 : ℕ)^1085*5000000000000^829 ≤ 2243954013021^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710892767 5000000000 2243954013021 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005100777/5000000000 : ℝ), (2617792199/5000000000 : ℝ), (2710892767/5000000000 : ℝ)] ![(12248304084401/100000000000000 : ℝ), (42872615648219/100000000000000 : ℝ), (2243954013021/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005100777/5000000000 : ℝ)|^1085 ≤ (12248304084401/100000000000000 : ℝ)^829
        have hw : |(-1005100777/5000000000 : ℝ)|=(1005100777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617792199/5000000000 : ℝ)|^1085 ≤ (42872615648219/100000000000000 : ℝ)^829
        have hw : |(2617792199/5000000000 : ℝ)|=(2617792199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710892767/5000000000 : ℝ)|^1085 ≤ (2243954013021/5000000000000 : ℝ)^829
        have hw : |(2710892767/5000000000 : ℝ)|=(2710892767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302775537/10000000000 : ℝ)*x 0 + (-1919078041/10000000000 : ℝ)*x 1 + (169430797/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302775537/10000000000 : ℝ)^1085 ≤ (21797076833759/50000000000000 : ℝ)^829 := by
    have hnat : (5302775537 : ℕ)^1085*50000000000000^829 ≤ 21797076833759^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302775537 10000000000 21797076833759 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1919078041/10000000000 : ℝ)^1085 ≤ (11526766379177/100000000000000 : ℝ)^829 := by
    have hnat : (1919078041 : ℕ)^1085*100000000000000^829 ≤ 11526766379177^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919078041 10000000000 11526766379177 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169430797/312500000 : ℝ)^1085 ≤ (44879079935409/100000000000000 : ℝ)^829 := by
    have hnat : (169430797 : ℕ)^1085*100000000000000^829 ≤ 44879079935409^829*312500000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169430797 312500000 44879079935409 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302775537/10000000000 : ℝ), (-1919078041/10000000000 : ℝ), (169430797/312500000 : ℝ)] ![(21797076833759/50000000000000 : ℝ), (11526766379177/100000000000000 : ℝ), (44879079935409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302775537/10000000000 : ℝ)|^1085 ≤ (21797076833759/50000000000000 : ℝ)^829
        have hw : |(5302775537/10000000000 : ℝ)|=(5302775537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1919078041/10000000000 : ℝ)|^1085 ≤ (11526766379177/100000000000000 : ℝ)^829
        have hw : |(-1919078041/10000000000 : ℝ)|=(1919078041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169430797/312500000 : ℝ)|^1085 ≤ (44879079935409/100000000000000 : ℝ)^829
        have hw : |(169430797/312500000 : ℝ)|=(169430797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651387851/5000000000 : ℝ)*x 0 + (5421785367/10000000000 : ℝ)*x 1 + (-383815601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651387851/5000000000 : ℝ)^1085 ≤ (10898538860717/25000000000000 : ℝ)^829 := by
    have hnat : (2651387851 : ℕ)^1085*25000000000000^829 ≤ 10898538860717^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651387851 5000000000 10898538860717 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421785367/10000000000 : ℝ)^1085 ≤ (5609884806399/12500000000000 : ℝ)^829 := by
    have hnat : (5421785367 : ℕ)^1085*12500000000000^829 ≤ 5609884806399^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421785367 10000000000 5609884806399 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383815601/2000000000 : ℝ)^1085 ≤ (11526766096173/100000000000000 : ℝ)^829 := by
    have hnat : (383815601 : ℕ)^1085*100000000000000^829 ≤ 11526766096173^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383815601 2000000000 11526766096173 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651387851/5000000000 : ℝ), (5421785367/10000000000 : ℝ), (-383815601/2000000000 : ℝ)] ![(10898538860717/25000000000000 : ℝ), (5609884806399/12500000000000 : ℝ), (11526766096173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651387851/5000000000 : ℝ)|^1085 ≤ (10898538860717/25000000000000 : ℝ)^829
        have hw : |(2651387851/5000000000 : ℝ)|=(2651387851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421785367/10000000000 : ℝ)|^1085 ≤ (5609884806399/12500000000000 : ℝ)^829
        have hw : |(5421785367/10000000000 : ℝ)|=(5421785367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383815601/2000000000 : ℝ)|^1085 ≤ (11526766096173/100000000000000 : ℝ)^829
        have hw : |(-383815601/2000000000 : ℝ)|=(383815601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s3_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (431596119/1000000000 : ℝ)*x 0 + (4517958989/10000000000 : ℝ)*x 1 + (4122363869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431596119/1000000000 : ℝ)^1085 ≤ (1040488731123/3125000000000 : ℝ)^829 := by
    have hnat : (431596119 : ℕ)^1085*3125000000000^829 ≤ 1040488731123^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431596119 1000000000 1040488731123 3125000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517958989/10000000000 : ℝ)^1085 ≤ (35349759533661/100000000000000 : ℝ)^829 := by
    have hnat : (4517958989 : ℕ)^1085*100000000000000^829 ≤ 35349759533661^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517958989 10000000000 35349759533661 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4122363869/10000000000 : ℝ)^1085 ≤ (15677300524369/50000000000000 : ℝ)^829 := by
    have hnat : (4122363869 : ℕ)^1085*50000000000000^829 ≤ 15677300524369^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122363869 10000000000 15677300524369 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431596119/1000000000 : ℝ), (4517958989/10000000000 : ℝ), (4122363869/10000000000 : ℝ)] ![(1040488731123/3125000000000 : ℝ), (35349759533661/100000000000000 : ℝ), (15677300524369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431596119/1000000000 : ℝ)|^1085 ≤ (1040488731123/3125000000000 : ℝ)^829
        have hw : |(431596119/1000000000 : ℝ)|=(431596119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517958989/10000000000 : ℝ)|^1085 ≤ (35349759533661/100000000000000 : ℝ)^829
        have hw : |(4517958989/10000000000 : ℝ)|=(4517958989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4122363869/10000000000 : ℝ)|^1085 ≤ (15677300524369/50000000000000 : ℝ)^829
        have hw : |(4122363869/10000000000 : ℝ)|=(4122363869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11003/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14977/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1009/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1009/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1009/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1009/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1009/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1009/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1009/10000 : ℝ) ^ (4339/1024 : ℝ) ≤ (1503569052235857/25000000000000000000 : ℝ) := by
    have hpowers : (1009/10000 : ℝ)^4339 ≤ (1503569052235857/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1009 : ℕ)^4339*25000000000000000000^1024 ≤ 1503569052235857^1024*10000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009 10000 1503569052235857 25000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1009/10000 : ℝ)) (X := (1503569052235857/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15961/100000 : ℝ) ^ (4339/1024 : ℝ) ≤ (20993885305634117/50000000000000000000 : ℝ) := by
    have hpowers : (15961/100000 : ℝ)^4339 ≤ (20993885305634117/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15961 : ℕ)^4339*50000000000000000000^1024 ≤ 20993885305634117^1024*100000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15961 100000 20993885305634117 50000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15961/100000 : ℝ)) (X := (20993885305634117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501503569052235857/12500000000000000000 : ℝ) ≤ (2500070964921351/2500000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (12501503569052235857/12500000000000000000 : ℝ)^1024 ≤ (2500070964921351/2500000000000000 : ℝ)^4339 := by
      have hnat : (12501503569052235857 : ℕ)^1024*2500000000000000^4339 ≤ 2500070964921351^4339*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501503569052235857 12500000000000000000 2500070964921351 2500000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070964921351/2500000000000000 : ℝ)) (X := (12501503569052235857/12500000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024001023410105831/50000000000000000000 : ℝ) ≤ (2500283159052759/2500000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50024001023410105831/50000000000000000000 : ℝ)^1024 ≤ (2500283159052759/2500000000000000 : ℝ)^4339 := by
      have hnat : (50024001023410105831 : ℕ)^1024*2500000000000000^4339 ≤ 2500283159052759^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024001023410105831 50000000000000000000 2500283159052759 2500000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500283159052759/2500000000000000 : ℝ)) (X := (50024001023410105831/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020993885305634117/25000000000000000000 : ℝ) ≤ (2500495353184167/2500000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (25020993885305634117/25000000000000000000 : ℝ)^1024 ≤ (2500495353184167/2500000000000000 : ℝ)^4339 := by
      have hnat : (25020993885305634117 : ℕ)^1024*2500000000000000^4339 ≤ 2500495353184167^4339*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020993885305634117 25000000000000000000 2500495353184167 2500000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500495353184167/2500000000000000 : ℝ)) (X := (25020993885305634117/25000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1503569052235857/25000000000000000000 : ℝ) ≤ ((4891211519160479427/4892500000000000000 : ℝ)+2*(4420711071/3057812500000 : ℝ)*(1009/10000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (4891211519160479427/4892500000000000000 : ℝ)+2*(4420711071/3057812500000 : ℝ)*(1009/10000 : ℝ)=(2500070964921351/2500000000000000 : ℝ) by norm_num, show 1+2*(1503569052235857/25000000000000000000 : ℝ)=(12501503569052235857/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20993885305634117/50000000000000000000 : ℝ)+(1503569052235857/25000000000000000000 : ℝ) ≤ ((4891211519160479427/4892500000000000000 : ℝ)+(4420711071/3057812500000 : ℝ)*((15961/100000 : ℝ)+(1009/10000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (4891211519160479427/4892500000000000000 : ℝ)+(4420711071/3057812500000 : ℝ)*((15961/100000 : ℝ)+(1009/10000 : ℝ))=(2500283159052759/2500000000000000 : ℝ) by norm_num, show 1+(20993885305634117/50000000000000000000 : ℝ)+(1503569052235857/25000000000000000000 : ℝ)=(50024001023410105831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20993885305634117/50000000000000000000 : ℝ) ≤ ((4891211519160479427/4892500000000000000 : ℝ)+2*(4420711071/3057812500000 : ℝ)*(15961/100000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (4891211519160479427/4892500000000000000 : ℝ)+2*(4420711071/3057812500000 : ℝ)*(15961/100000 : ℝ)=(2500495353184167/2500000000000000 : ℝ) by norm_num, show 1+2*(20993885305634117/50000000000000000000 : ℝ)=(25020993885305634117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4891211519160479427/4892500000000000000 : ℝ)*(X 1 0+X 2 0)+(4420711071/3057812500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (1009/10000 : ℝ)) (hi := (15961/100000 : ℝ)) (c := (4891211519160479427/4892500000000000000 : ℝ)) (alpha := (4420711071/3057812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4891211519160479427/4892500000000000000 : ℝ)*(X 0 1+X 2 1)+(4420711071/3057812500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (1009/10000 : ℝ)) (hi := (15961/100000 : ℝ)) (c := (4891211519160479427/4892500000000000000 : ℝ)) (alpha := (4420711071/3057812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4891211519160479427/4892500000000000000 : ℝ)*(X 0 2+X 1 2)+(4420711071/3057812500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (1009/10000 : ℝ)) (hi := (15961/100000 : ℝ)) (c := (4891211519160479427/4892500000000000000 : ℝ)) (alpha := (4420711071/3057812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2010183909/10000000000 : ℝ)*X 0 0+(542255699/1000000000 : ℝ)*X 0 1+(2617408833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535133751/1000000000 : ℝ)*X 1 0+(-2106045491/10000000000 : ℝ)*X 1 1+(1046963651/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351337469/10000000000 : ℝ)*X 2 0+(2617409197/5000000000 : ℝ)*X 2 1+(-2106045361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078981151/2500000000 : ℝ)*X 0 0+(4120726733/10000000000 : ℝ)*X 0 1+(4519586333/10000000000 : ℝ)*X 0 2+(1078981151/2500000000 : ℝ)*X 1 0+(4120726733/10000000000 : ℝ)*X 1 1+(4519586333/10000000000 : ℝ)*X 1 2+(1078981151/2500000000 : ℝ)*X 2 0+(4120726733/10000000000 : ℝ)*X 2 1+(4519586333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1005100777/5000000000 : ℝ)*X 0 0+(2617792199/5000000000 : ℝ)*X 0 1+(2710892767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302775537/10000000000 : ℝ)*X 1 0+(-1919078041/10000000000 : ℝ)*X 1 1+(169430797/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651387851/5000000000 : ℝ)*X 2 0+(5421785367/10000000000 : ℝ)*X 2 1+(-383815601/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431596119/1000000000 : ℝ)*X 0 0+(4517958989/10000000000 : ℝ)*X 0 1+(4122363869/10000000000 : ℝ)*X 0 2+(431596119/1000000000 : ℝ)*X 1 0+(4517958989/10000000000 : ℝ)*X 1 1+(4122363869/10000000000 : ℝ)*X 1 2+(431596119/1000000000 : ℝ)*X 2 0+(4517958989/10000000000 : ℝ)*X 2 1+(4122363869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1209808711573886761000083843/122312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1304915303/100000000000000 : ℝ)*(base19) + (23800727/3125000000000 : ℝ)*(base23) + (268894821/100000000000000 : ℝ)*(lower2) + (284175721/100000000000000 : ℝ)*(upper3) + (1710031/4000000000000 : ℝ)*(upper5) + (1958441965533001/50000000000000 : ℝ)*(major0) + (1958441965533001/50000000000000 : ℝ)*(major1) + (1958441965533001/50000000000000 : ℝ)*(major2) + (2663286070059393/50000000000000 : ℝ)*(sp0) + (1331651418549977/25000000000000 : ℝ)*(sp1) + (1331651554372987/25000000000000 : ℝ)*(sp2) + (1253575859827731/50000000000000 : ℝ)*(sp3) + (1393559857/4000000000000 : ℝ)*(sp4) + (4416828513/50000000000000 : ℝ)*(sp7) + (313395069164061/12500000000000 : ℝ)*(f.failure) + (5326606979115211/100000000000000 : ℝ)*(f.sum) + (1331590833769/1223125000000000000000000000 : ℝ)*base66 + (1445769650117579573/244625000000000000000000000000000 : ℝ)*base68 + (874575220456579573/244625000000000000000000000000000 : ℝ)*base70 + (2012980027495829573/244625000000000000000000000000000 : ℝ)*base72 + (3549234132383/2446250000000000000000000000 : ℝ)*base74 + (14407944218829573/244625000000000000000000000000000 : ℝ)*base76 + (3876839188886329573/244625000000000000000000000000000 : ℝ)*base78 + (656829616924329573/244625000000000000000000000000000 : ℝ)*base80 + (7195714290417/2446250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6102523/625000000000000000000 : ℝ)*base89 + (6102523/625000000000000000000 : ℝ)*base91 + (6102523/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (595963844698956677006833509/122312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433755483/50000000000000 : ℝ)*(base19) + (536981573/50000000000000 : ℝ)*(base23) + (29212497/25000000000000 : ℝ)*(upper3) + (4500869/50000000000000 : ℝ)*(lower4) + (12769437/12500000000000 : ℝ)*(upper5) + (3949187485231589/100000000000000 : ℝ)*(major0) + (3949187485231589/100000000000000 : ℝ)*(major1) + (3949187485231589/100000000000000 : ℝ)*(major2) + (14131005817/100000000000000 : ℝ)*(sp1) + (4143399857/25000000000000 : ℝ)*(sp2) + (5370537053633081/100000000000000 : ℝ)*(sp4) + (2685261027558149/50000000000000 : ℝ)*(sp5) + (1342629851517627/25000000000000 : ℝ)*(sp6) + (19748732456363/781250000000 : ℝ)*(sp7) + (19748732456363/781250000000 : ℝ)*(f.failure) + (5370537053633081/100000000000000 : ℝ)*(f.sum) + (11450861928953/4892500000000000000000000000 : ℝ)*base65 + (1333835901965919503/489250000000000000000000000000000 : ℝ)*base67 + (875991049422080497/489250000000000000000000000000000 : ℝ)*base70 + (1968338734772580497/489250000000000000000000000000000 : ℝ)*base72 + (6725756345581/9785000000000000000000000000 : ℝ)*base73 + (3402323090737330497/489250000000000000000000000000000 : ℝ)*base76 + (3489840994263580497/489250000000000000000000000000000 : ℝ)*base78 + (440509866111580497/489250000000000000000000000000000 : ℝ)*base80 + (1075177666173/305781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10477/4882812500000000000 : ℝ)*base90 + (10477/4882812500000000000 : ℝ)*base92 + (10477/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1380_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11003/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14977/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1380_s4_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011368227/10000000000 : ℝ)*x 0 + (5412698733/10000000000 : ℝ)*x 1 + (5243897197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011368227/10000000000 : ℝ)^1085 ≤ (6128804362699/50000000000000 : ℝ)^829 := by
    have hnat : (2011368227 : ℕ)^1085*50000000000000^829 ≤ 6128804362699^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011368227 10000000000 6128804362699 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412698733/10000000000 : ℝ)^1085 ≤ (559758275819/1250000000000 : ℝ)^829 := by
    have hnat : (5412698733 : ℕ)^1085*1250000000000^829 ≤ 559758275819^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412698733 10000000000 559758275819 1250000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243897197/10000000000 : ℝ)^1085 ≤ (671277018641/1562500000000 : ℝ)^829 := by
    have hnat : (5243897197 : ℕ)^1085*1562500000000^829 ≤ 671277018641^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243897197 10000000000 671277018641 1562500000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011368227/10000000000 : ℝ), (5412698733/10000000000 : ℝ), (5243897197/10000000000 : ℝ)] ![(6128804362699/50000000000000 : ℝ), (559758275819/1250000000000 : ℝ), (671277018641/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011368227/10000000000 : ℝ)|^1085 ≤ (6128804362699/50000000000000 : ℝ)^829
        have hw : |(-2011368227/10000000000 : ℝ)|=(2011368227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412698733/10000000000 : ℝ)|^1085 ≤ (559758275819/1250000000000 : ℝ)^829
        have hw : |(5412698733/10000000000 : ℝ)|=(5412698733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243897197/10000000000 : ℝ)|^1085 ≤ (671277018641/1562500000000 : ℝ)^829
        have hw : |(5243897197/10000000000 : ℝ)|=(5243897197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668601323/1250000000 : ℝ)*x 0 + (-131086221/625000000 : ℝ)*x 1 + (2621948773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668601323/1250000000 : ℝ)^1085 ≤ (44090139639687/100000000000000 : ℝ)^829 := by
    have hnat : (668601323 : ℕ)^1085*100000000000000^829 ≤ 44090139639687^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668601323 1250000000 44090139639687 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131086221/625000000 : ℝ)^1085 ≤ (6474063708591/50000000000000 : ℝ)^829 := by
    have hnat : (131086221 : ℕ)^1085*50000000000000^829 ≤ 6474063708591^829*625000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131086221 625000000 6474063708591 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621948773/5000000000 : ℝ)^1085 ≤ (8592346587047/20000000000000 : ℝ)^829 := by
    have hnat : (2621948773 : ℕ)^1085*20000000000000^829 ≤ 8592346587047^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621948773 5000000000 8592346587047 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668601323/1250000000 : ℝ), (-131086221/625000000 : ℝ), (2621948773/5000000000 : ℝ)] ![(44090139639687/100000000000000 : ℝ), (6474063708591/50000000000000 : ℝ), (8592346587047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668601323/1250000000 : ℝ)|^1085 ≤ (44090139639687/100000000000000 : ℝ)^829
        have hw : |(668601323/1250000000 : ℝ)|=(668601323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131086221/625000000 : ℝ)|^1085 ≤ (6474063708591/50000000000000 : ℝ)^829
        have hw : |(-131086221/625000000 : ℝ)|=(131086221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621948773/5000000000 : ℝ)|^1085 ≤ (8592346587047/20000000000000 : ℝ)^829
        have hw : |(2621948773/5000000000 : ℝ)|=(2621948773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069762141/2000000000 : ℝ)*x 0 + (1310974263/2500000000 : ℝ)*x 1 + (-209738003/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069762141/2000000000 : ℝ)^1085 ≤ (44090140945091/100000000000000 : ℝ)^829 := by
    have hnat : (1069762141 : ℕ)^1085*100000000000000^829 ≤ 44090140945091^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069762141 2000000000 44090140945091 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310974263/2500000000 : ℝ)^1085 ≤ (21480863819119/50000000000000 : ℝ)^829 := by
    have hnat : (1310974263 : ℕ)^1085*50000000000000^829 ≤ 21480863819119^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310974263 2500000000 21480863819119 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209738003/1000000000 : ℝ)^1085 ≤ (2589626281729/20000000000000 : ℝ)^829 := by
    have hnat : (209738003 : ℕ)^1085*20000000000000^829 ≤ 2589626281729^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209738003 1000000000 2589626281729 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069762141/2000000000 : ℝ), (1310974263/2500000000 : ℝ), (-209738003/1000000000 : ℝ)] ![(44090140945091/100000000000000 : ℝ), (21480863819119/50000000000000 : ℝ), (2589626281729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069762141/2000000000 : ℝ)|^1085 ≤ (44090140945091/100000000000000 : ℝ)^829
        have hw : |(1069762141/2000000000 : ℝ)|=(1069762141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310974263/2500000000 : ℝ)|^1085 ≤ (21480863819119/50000000000000 : ℝ)^829
        have hw : |(1310974263/2500000000 : ℝ)|=(1310974263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209738003/1000000000 : ℝ)|^1085 ≤ (2589626281729/20000000000000 : ℝ)^829
        have hw : |(-209738003/1000000000 : ℝ)|=(209738003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134895203/312500000 : ℝ)*x 0 + (1035188319/2500000000 : ℝ)*x 1 + (4499382839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134895203/312500000 : ℝ)^1085 ≤ (266420471869/800000000000 : ℝ)^829 := by
    have hnat : (134895203 : ℕ)^1085*800000000000^829 ≤ 266420471869^829*312500000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134895203 312500000 266420471869 800000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035188319/2500000000 : ℝ)^1085 ≤ (15768894437629/50000000000000 : ℝ)^829 := by
    have hnat : (1035188319 : ℕ)^1085*50000000000000^829 ≤ 15768894437629^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035188319 2500000000 15768894437629 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499382839/10000000000 : ℝ)^1085 ≤ (17579826063687/50000000000000 : ℝ)^829 := by
    have hnat : (4499382839 : ℕ)^1085*50000000000000^829 ≤ 17579826063687^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499382839 10000000000 17579826063687 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134895203/312500000 : ℝ), (1035188319/2500000000 : ℝ), (4499382839/10000000000 : ℝ)] ![(266420471869/800000000000 : ℝ), (15768894437629/50000000000000 : ℝ), (17579826063687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134895203/312500000 : ℝ)|^1085 ≤ (266420471869/800000000000 : ℝ)^829
        have hw : |(134895203/312500000 : ℝ)|=(134895203/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035188319/2500000000 : ℝ)|^1085 ≤ (15768894437629/50000000000000 : ℝ)^829
        have hw : |(1035188319/2500000000 : ℝ)|=(1035188319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499382839/10000000000 : ℝ)|^1085 ≤ (17579826063687/50000000000000 : ℝ)^829
        have hw : |(4499382839/10000000000 : ℝ)|=(4499382839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011380167/10000000000 : ℝ)*x 0 + (1048903257/2000000000 : ℝ)*x 1 + (1082415371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011380167/10000000000 : ℝ)^1085 ≤ (12257703959853/100000000000000 : ℝ)^829 := by
    have hnat : (2011380167 : ℕ)^1085*100000000000000^829 ≤ 12257703959853^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011380167 10000000000 12257703959853 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048903257/2000000000 : ℝ)^1085 ≤ (42968367588081/100000000000000 : ℝ)^829 := by
    have hnat : (1048903257 : ℕ)^1085*100000000000000^829 ≤ 42968367588081^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048903257 2000000000 42968367588081 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082415371/2000000000 : ℝ)^1085 ≤ (2798370527121/6250000000000 : ℝ)^829 := by
    have hnat : (1082415371 : ℕ)^1085*6250000000000^829 ≤ 2798370527121^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082415371 2000000000 2798370527121 6250000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011380167/10000000000 : ℝ), (1048903257/2000000000 : ℝ), (1082415371/2000000000 : ℝ)] ![(12257703959853/100000000000000 : ℝ), (42968367588081/100000000000000 : ℝ), (2798370527121/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011380167/10000000000 : ℝ)|^1085 ≤ (12257703959853/100000000000000 : ℝ)^829
        have hw : |(-2011380167/10000000000 : ℝ)|=(2011380167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048903257/2000000000 : ℝ)|^1085 ≤ (42968367588081/100000000000000 : ℝ)^829
        have hw : |(1048903257/2000000000 : ℝ)|=(1048903257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082415371/2000000000 : ℝ)|^1085 ≤ (2798370527121/6250000000000 : ℝ)^829
        have hw : |(1082415371/2000000000 : ℝ)|=(1082415371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663143491/1250000000 : ℝ)*x 0 + (-1929201229/10000000000 : ℝ)*x 1 + (2706037419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663143491/1250000000 : ℝ)^1085 ≤ (43619681649111/100000000000000 : ℝ)^829 := by
    have hnat : (663143491 : ℕ)^1085*100000000000000^829 ≤ 43619681649111^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663143491 1250000000 43619681649111 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929201229/10000000000 : ℝ)^1085 ≤ (5803205872953/50000000000000 : ℝ)^829 := by
    have hnat : (1929201229 : ℕ)^1085*50000000000000^829 ≤ 5803205872953^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929201229 10000000000 5803205872953 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706037419/5000000000 : ℝ)^1085 ≤ (22386953297227/50000000000000 : ℝ)^829 := by
    have hnat : (2706037419 : ℕ)^1085*50000000000000^829 ≤ 22386953297227^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706037419 5000000000 22386953297227 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663143491/1250000000 : ℝ), (-1929201229/10000000000 : ℝ), (2706037419/5000000000 : ℝ)] ![(43619681649111/100000000000000 : ℝ), (5803205872953/50000000000000 : ℝ), (22386953297227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663143491/1250000000 : ℝ)|^1085 ≤ (43619681649111/100000000000000 : ℝ)^829
        have hw : |(663143491/1250000000 : ℝ)|=(663143491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929201229/10000000000 : ℝ)|^1085 ≤ (5803205872953/50000000000000 : ℝ)^829
        have hw : |(-1929201229/10000000000 : ℝ)|=(1929201229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706037419/5000000000 : ℝ)|^1085 ≤ (22386953297227/50000000000000 : ℝ)^829
        have hw : |(2706037419/5000000000 : ℝ)|=(2706037419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212205881/400000000 : ℝ)*x 0 + (1353018843/2500000000 : ℝ)*x 1 + (-30143777/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212205881/400000000 : ℝ)^1085 ≤ (43619671931759/100000000000000 : ℝ)^829 := by
    have hnat : (212205881 : ℕ)^1085*100000000000000^829 ≤ 43619671931759^829*400000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212205881 400000000 43619671931759 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353018843/2500000000 : ℝ)^1085 ≤ (44773912376449/100000000000000 : ℝ)^829 := by
    have hnat : (1353018843 : ℕ)^1085*100000000000000^829 ≤ 44773912376449^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353018843 2500000000 44773912376449 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30143777/156250000 : ℝ)^1085 ≤ (5803207837517/50000000000000 : ℝ)^829 := by
    have hnat : (30143777 : ℕ)^1085*50000000000000^829 ≤ 5803207837517^829*156250000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30143777 156250000 5803207837517 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212205881/400000000 : ℝ), (1353018843/2500000000 : ℝ), (-30143777/156250000 : ℝ)] ![(43619671931759/100000000000000 : ℝ), (44773912376449/100000000000000 : ℝ), (5803207837517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212205881/400000000 : ℝ)|^1085 ≤ (43619671931759/100000000000000 : ℝ)^829
        have hw : |(212205881/400000000 : ℝ)|=(212205881/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353018843/2500000000 : ℝ)|^1085 ≤ (44773912376449/100000000000000 : ℝ)^829
        have hw : |(1353018843/2500000000 : ℝ)|=(1353018843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30143777/156250000 : ℝ)|^1085 ≤ (5803207837517/50000000000000 : ℝ)^829
        have hw : |(-30143777/156250000 : ℝ)|=(30143777/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s4_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2158336619/5000000000 : ℝ)*x 0 + (4498065923/10000000000 : ℝ)*x 1 + (828415439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158336619/5000000000 : ℝ)^1085 ≤ (6660565801309/20000000000000 : ℝ)^829 := by
    have hnat : (2158336619 : ℕ)^1085*20000000000000^829 ≤ 6660565801309^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158336619 5000000000 6660565801309 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498065923/10000000000 : ℝ)^1085 ≤ (35146184060151/100000000000000 : ℝ)^829 := by
    have hnat : (4498065923 : ℕ)^1085*100000000000000^829 ≤ 35146184060151^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498065923 10000000000 35146184060151 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828415439/2000000000 : ℝ)^1085 ≤ (15775493465339/50000000000000 : ℝ)^829 := by
    have hnat : (828415439 : ℕ)^1085*50000000000000^829 ≤ 15775493465339^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828415439 2000000000 15775493465339 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158336619/5000000000 : ℝ), (4498065923/10000000000 : ℝ), (828415439/2000000000 : ℝ)] ![(6660565801309/20000000000000 : ℝ), (35146184060151/100000000000000 : ℝ), (15775493465339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158336619/5000000000 : ℝ)|^1085 ≤ (6660565801309/20000000000000 : ℝ)^829
        have hw : |(2158336619/5000000000 : ℝ)|=(2158336619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498065923/10000000000 : ℝ)|^1085 ≤ (35146184060151/100000000000000 : ℝ)^829
        have hw : |(4498065923/10000000000 : ℝ)|=(4498065923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828415439/2000000000 : ℝ)|^1085 ≤ (15775493465339/50000000000000 : ℝ)^829
        have hw : |(828415439/2000000000 : ℝ)|=(828415439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11003/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11197/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11003/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11003/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11003/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11003/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11003/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11003/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11003/100000 : ℝ) ^ (4339/1024 : ℝ) ≤ (8681415571974717/100000000000000000000 : ℝ) := by
    have hpowers : (11003/100000 : ℝ)^4339 ≤ (8681415571974717/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11003 : ℕ)^4339*100000000000000000000^1024 ≤ 8681415571974717^1024*100000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11003 100000 8681415571974717 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11003/100000 : ℝ)) (X := (8681415571974717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14977/100000 : ℝ) ^ (4339/1024 : ℝ) ≤ (16032223936464819/50000000000000000000 : ℝ) := by
    have hpowers : (14977/100000 : ℝ)^4339 ≤ (16032223936464819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14977 : ℕ)^4339*50000000000000000000^1024 ≤ 16032223936464819^1024*100000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14977 100000 16032223936464819 50000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14977/100000 : ℝ)) (X := (16032223936464819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008681415571974717/50000000000000000000 : ℝ) ≤ (10000409734039281/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50008681415571974717/50000000000000000000 : ℝ)^1024 ≤ (10000409734039281/10000000000000000 : ℝ)^4339 := by
      have hnat : (50008681415571974717 : ℕ)^1024*10000000000000000^4339 ≤ 10000409734039281^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008681415571974717 50000000000000000000 10000409734039281 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000409734039281/10000000000000000 : ℝ)) (X := (50008681415571974717/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008149172688980871/20000000000000000000 : ℝ) ≤ (1000096144898467/1000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (20008149172688980871/20000000000000000000 : ℝ)^1024 ≤ (1000096144898467/1000000000000000 : ℝ)^4339 := by
      have hnat : (20008149172688980871 : ℕ)^1024*1000000000000000^4339 ≤ 1000096144898467^4339*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008149172688980871 20000000000000000000 1000096144898467 1000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000096144898467/1000000000000000 : ℝ)) (X := (20008149172688980871/20000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016032223936464819/25000000000000000000 : ℝ) ≤ (10001513163930059/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (25016032223936464819/25000000000000000000 : ℝ)^1024 ≤ (10001513163930059/10000000000000000 : ℝ)^4339 := by
      have hnat : (25016032223936464819 : ℕ)^1024*10000000000000000^4339 ≤ 10001513163930059^4339*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016032223936464819 25000000000000000000 10001513163930059 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001513163930059/10000000000000000 : ℝ)) (X := (25016032223936464819/25000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8681415571974717/100000000000000000000 : ℝ) ≤ ((993237181099596809/993500000000000000 : ℝ)+2*(551714945389/397400000000000 : ℝ)*(11003/100000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (993237181099596809/993500000000000000 : ℝ)+2*(551714945389/397400000000000 : ℝ)*(11003/100000 : ℝ)=(10000409734039281/10000000000000000 : ℝ) by norm_num, show 1+2*(8681415571974717/100000000000000000000 : ℝ)=(50008681415571974717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16032223936464819/50000000000000000000 : ℝ)+(8681415571974717/100000000000000000000 : ℝ) ≤ ((993237181099596809/993500000000000000 : ℝ)+(551714945389/397400000000000 : ℝ)*((14977/100000 : ℝ)+(11003/100000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (993237181099596809/993500000000000000 : ℝ)+(551714945389/397400000000000 : ℝ)*((14977/100000 : ℝ)+(11003/100000 : ℝ))=(1000096144898467/1000000000000000 : ℝ) by norm_num, show 1+(16032223936464819/50000000000000000000 : ℝ)+(8681415571974717/100000000000000000000 : ℝ)=(20008149172688980871/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16032223936464819/50000000000000000000 : ℝ) ≤ ((993237181099596809/993500000000000000 : ℝ)+2*(551714945389/397400000000000 : ℝ)*(14977/100000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (993237181099596809/993500000000000000 : ℝ)+2*(551714945389/397400000000000 : ℝ)*(14977/100000 : ℝ)=(10001513163930059/10000000000000000 : ℝ) by norm_num, show 1+2*(16032223936464819/50000000000000000000 : ℝ)=(25016032223936464819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (993237181099596809/993500000000000000 : ℝ)*(X 1 0+X 2 0)+(551714945389/397400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (11003/100000 : ℝ)) (hi := (14977/100000 : ℝ)) (c := (993237181099596809/993500000000000000 : ℝ)) (alpha := (551714945389/397400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (993237181099596809/993500000000000000 : ℝ)*(X 0 1+X 2 1)+(551714945389/397400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (11003/100000 : ℝ)) (hi := (14977/100000 : ℝ)) (c := (993237181099596809/993500000000000000 : ℝ)) (alpha := (551714945389/397400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (993237181099596809/993500000000000000 : ℝ)*(X 0 2+X 1 2)+(551714945389/397400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (11003/100000 : ℝ)) (hi := (14977/100000 : ℝ)) (c := (993237181099596809/993500000000000000 : ℝ)) (alpha := (551714945389/397400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2011368227/10000000000 : ℝ)*X 0 0+(5412698733/10000000000 : ℝ)*X 0 1+(5243897197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668601323/1250000000 : ℝ)*X 1 0+(-131086221/625000000 : ℝ)*X 1 1+(2621948773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069762141/2000000000 : ℝ)*X 2 0+(1310974263/2500000000 : ℝ)*X 2 1+(-209738003/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134895203/312500000 : ℝ)*X 0 0+(1035188319/2500000000 : ℝ)*X 0 1+(4499382839/10000000000 : ℝ)*X 0 2+(134895203/312500000 : ℝ)*X 1 0+(1035188319/2500000000 : ℝ)*X 1 1+(4499382839/10000000000 : ℝ)*X 1 2+(134895203/312500000 : ℝ)*X 2 0+(1035188319/2500000000 : ℝ)*X 2 1+(4499382839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2011380167/10000000000 : ℝ)*X 0 0+(1048903257/2000000000 : ℝ)*X 0 1+(1082415371/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663143491/1250000000 : ℝ)*X 1 0+(-1929201229/10000000000 : ℝ)*X 1 1+(2706037419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212205881/400000000 : ℝ)*X 2 0+(1353018843/2500000000 : ℝ)*X 2 1+(-30143777/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158336619/5000000000 : ℝ)*X 0 0+(4498065923/10000000000 : ℝ)*X 0 1+(828415439/2000000000 : ℝ)*X 0 2+(2158336619/5000000000 : ℝ)*X 1 0+(4498065923/10000000000 : ℝ)*X 1 1+(828415439/2000000000 : ℝ)*X 1 2+(2158336619/5000000000 : ℝ)*X 2 0+(4498065923/10000000000 : ℝ)*X 2 1+(828415439/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129590636396651889216093/19870000000000000000000000000 : ℝ) := by norm_num
    linear_combination (313311997/25000000000000 : ℝ)*(base19) + (713373853/50000000000000 : ℝ)*(base23) + (12844837/100000000000000 : ℝ)*(lower2) + (551290323/100000000000000 : ℝ)*(upper3) + (8491037/25000000000000 : ℝ)*(lower4) + (4356295281433723/100000000000000 : ℝ)*(major0) + (4356295281433723/100000000000000 : ℝ)*(major1) + (4356295281433723/100000000000000 : ℝ)*(major2) + (5924151765396419/100000000000000 : ℝ)*(sp0) + (740520683453021/12500000000000 : ℝ)*(sp1) + (118483305882489/2000000000000 : ℝ)*(sp2) + (2788403899089943/100000000000000 : ℝ)*(sp3) + (14955475737/100000000000000 : ℝ)*(sp4) + (986275393/5000000000000 : ℝ)*(sp7) + (1394211812298901/50000000000000 : ℝ)*(f.failure) + (1481041680218039/25000000000000 : ℝ)*(f.sum) + (55890038448673/19870000000000000000000000000 : ℝ)*base66 + (147611473581907407/99350000000000000000000000000000 : ℝ)*base67 + (518785937250342593/99350000000000000000000000000000 : ℝ)*base70 + (864324140923092593/99350000000000000000000000000000 : ℝ)*base72 + (31163388886753/19870000000000000000000000000 : ℝ)*base74 + (265504119332157407/99350000000000000000000000000000 : ℝ)*base75 + (861420813316607407/99350000000000000000000000000000 : ℝ)*base77 + (1173068664519892593/99350000000000000000000000000000 : ℝ)*base80 + (87949372627743/19870000000000000000000000000 : ℝ)*base82 + (23323357/2500000000000000000000 : ℝ)*base90 + (23323357/2500000000000000000000 : ℝ)*base92 + (23323357/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56480967834625536199817919/12418750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (639672327/50000000000000 : ℝ)*(base19) + (1021491197/100000000000000 : ℝ)*(base23) + (2104283/3125000000000 : ℝ)*(upper3) + (41978741/10000000000000 : ℝ)*(lower4) + (1097143128615847/25000000000000 : ℝ)*(major0) + (1097143128615847/25000000000000 : ℝ)*(major1) + (1097143128615847/25000000000000 : ℝ)*(major2) + (8945061209/20000000000000 : ℝ)*(sp0) + (4046175277/100000000000000 : ℝ)*(sp1) + (6092429643/100000000000000 : ℝ)*(sp3) + (5968016174231091/100000000000000 : ℝ)*(sp4) + (2984027787008603/50000000000000 : ℝ)*(sp5) + (298402993902297/5000000000000 : ℝ)*(sp6) + (702269471339667/25000000000000 : ℝ)*(sp7) + (2809083977788311/100000000000000 : ℝ)*(f.failure) + (5968060899537137/100000000000000 : ℝ)*(f.sum) + (12507223406767/4967500000000000000000000000 : ℝ)*base66 + (130678693801439723/24837500000000000000000000000000 : ℝ)*base67 + (208170738675377223/24837500000000000000000000000000 : ℝ)*base69 + (13324161115460277/24837500000000000000000000000000 : ℝ)*base72 + (50783386449/38808593750000000000000000 : ℝ)*base74 + (128443906117122777/24837500000000000000000000000000 : ℝ)*base76 + (113179543736310277/24837500000000000000000000000000 : ℝ)*base78 + (79124457537560277/24837500000000000000000000000000 : ℝ)*base80 + (23453508463929/9935000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8479727/5000000000000000000000 : ℝ)*base90 + (8479727/5000000000000000000000 : ℝ)*base92 + (8479727/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1380_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11003/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1380_s5_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005779319/5000000000 : ℝ)*x 0 + (676377961/1250000000 : ℝ)*x 1 + (131136173/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005779319/5000000000 : ℝ)^1085 ≤ (12259127480529/100000000000000 : ℝ)^829 := by
    have hnat : (1005779319 : ℕ)^1085*100000000000000^829 ≤ 12259127480529^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005779319 5000000000 12259127480529 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676377961/1250000000 : ℝ)^1085 ≤ (699414459281/1562500000000 : ℝ)^829 := by
    have hnat : (676377961 : ℕ)^1085*1562500000000^829 ≤ 699414459281^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676377961 1250000000 699414459281 1562500000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131136173/250000000 : ℝ)^1085 ≤ (21489173556929/50000000000000 : ℝ)^829 := by
    have hnat : (131136173 : ℕ)^1085*50000000000000^829 ≤ 21489173556929^829*250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131136173 250000000 21489173556929 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005779319/5000000000 : ℝ), (676377961/1250000000 : ℝ), (131136173/250000000 : ℝ)] ![(12259127480529/100000000000000 : ℝ), (699414459281/1562500000000 : ℝ), (21489173556929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005779319/5000000000 : ℝ)|^1085 ≤ (12259127480529/100000000000000 : ℝ)^829
        have hw : |(-1005779319/5000000000 : ℝ)|=(1005779319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676377961/1250000000 : ℝ)|^1085 ≤ (699414459281/1562500000000 : ℝ)^829
        have hw : |(676377961/1250000000 : ℝ)|=(676377961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131136173/250000000 : ℝ)|^1085 ≤ (21489173556929/50000000000000 : ℝ)^829
        have hw : |(131136173/250000000 : ℝ)|=(131136173/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668547571/1250000000 : ℝ)*x 0 + (-2095897609/10000000000 : ℝ)*x 1 + (5245446683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668547571/1250000000 : ℝ)^1085 ≤ (22042750243389/50000000000000 : ℝ)^829 := by
    have hnat : (668547571 : ℕ)^1085*50000000000000^829 ≤ 22042750243389^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668547571 1250000000 22042750243389 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095897609/10000000000 : ℝ)^1085 ≤ (1293615492487/10000000000000 : ℝ)^829 := by
    have hnat : (2095897609 : ℕ)^1085*10000000000000^829 ≤ 1293615492487^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095897609 10000000000 1293615492487 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245446683/10000000000 : ℝ)^1085 ≤ (21489172286177/50000000000000 : ℝ)^829 := by
    have hnat : (5245446683 : ℕ)^1085*50000000000000^829 ≤ 21489172286177^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245446683 10000000000 21489172286177 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668547571/1250000000 : ℝ), (-2095897609/10000000000 : ℝ), (5245446683/10000000000 : ℝ)] ![(22042750243389/50000000000000 : ℝ), (1293615492487/10000000000000 : ℝ), (21489172286177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668547571/1250000000 : ℝ)|^1085 ≤ (22042750243389/50000000000000 : ℝ)^829
        have hw : |(668547571/1250000000 : ℝ)|=(668547571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095897609/10000000000 : ℝ)|^1085 ≤ (1293615492487/10000000000000 : ℝ)^829
        have hw : |(-2095897609/10000000000 : ℝ)|=(2095897609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245446683/10000000000 : ℝ)|^1085 ≤ (21489172286177/50000000000000 : ℝ)^829
        have hw : |(5245446683/10000000000 : ℝ)|=(5245446683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674190447/5000000000 : ℝ)*x 0 + (5245446183/10000000000 : ℝ)*x 1 + (-2095897837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674190447/5000000000 : ℝ)^1085 ≤ (44085504003729/100000000000000 : ℝ)^829 := by
    have hnat : (2674190447 : ℕ)^1085*100000000000000^829 ≤ 44085504003729^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674190447 5000000000 44085504003729 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245446183/10000000000 : ℝ)^1085 ≤ (10744584802633/25000000000000 : ℝ)^829 := by
    have hnat : (5245446183 : ℕ)^1085*25000000000000^829 ≤ 10744584802633^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245446183 10000000000 10744584802633 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095897837/10000000000 : ℝ)^1085 ≤ (6468078383341/50000000000000 : ℝ)^829 := by
    have hnat : (2095897837 : ℕ)^1085*50000000000000^829 ≤ 6468078383341^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095897837 10000000000 6468078383341 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674190447/5000000000 : ℝ), (5245446183/10000000000 : ℝ), (-2095897837/10000000000 : ℝ)] ![(44085504003729/100000000000000 : ℝ), (10744584802633/25000000000000 : ℝ), (6468078383341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674190447/5000000000 : ℝ)|^1085 ≤ (44085504003729/100000000000000 : ℝ)^829
        have hw : |(2674190447/5000000000 : ℝ)|=(2674190447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245446183/10000000000 : ℝ)|^1085 ≤ (10744584802633/25000000000000 : ℝ)^829
        have hw : |(5245446183/10000000000 : ℝ)|=(5245446183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095897837/10000000000 : ℝ)|^1085 ≤ (6468078383341/50000000000000 : ℝ)^829
        have hw : |(-2095897837/10000000000 : ℝ)|=(2095897837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4316761291/10000000000 : ℝ)*x 0 + (2072082223/5000000000 : ℝ)*x 1 + (449594389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316761291/10000000000 : ℝ)^1085 ≤ (33303718110793/100000000000000 : ℝ)^829 := by
    have hnat : (4316761291 : ℕ)^1085*100000000000000^829 ≤ 33303718110793^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316761291 10000000000 33303718110793 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072082223/5000000000 : ℝ)^1085 ≤ (15785898617497/50000000000000 : ℝ)^829 := by
    have hnat : (2072082223 : ℕ)^1085*50000000000000^829 ≤ 15785898617497^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072082223 5000000000 15785898617497 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449594389/1000000000 : ℝ)^1085 ≤ (8781121160803/25000000000000 : ℝ)^829 := by
    have hnat : (449594389 : ℕ)^1085*25000000000000^829 ≤ 8781121160803^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449594389 1000000000 8781121160803 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316761291/10000000000 : ℝ), (2072082223/5000000000 : ℝ), (449594389/1000000000 : ℝ)] ![(33303718110793/100000000000000 : ℝ), (15785898617497/50000000000000 : ℝ), (8781121160803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316761291/10000000000 : ℝ)|^1085 ≤ (33303718110793/100000000000000 : ℝ)^829
        have hw : |(4316761291/10000000000 : ℝ)|=(4316761291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072082223/5000000000 : ℝ)|^1085 ≤ (15785898617497/50000000000000 : ℝ)^829
        have hw : |(2072082223/5000000000 : ℝ)|=(2072082223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449594389/1000000000 : ℝ)|^1085 ≤ (8781121160803/25000000000000 : ℝ)^829
        have hw : |(449594389/1000000000 : ℝ)|=(449594389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-251446423/1250000000 : ℝ)*x 0 + (2623021459/5000000000 : ℝ)*x 1 + (5410423971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251446423/1250000000 : ℝ)^1085 ≤ (6129614573343/50000000000000 : ℝ)^829 := by
    have hnat : (251446423 : ℕ)^1085*50000000000000^829 ≤ 6129614573343^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251446423 1250000000 6129614573343 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623021459/5000000000 : ℝ)^1085 ≤ (4298473849683/10000000000000 : ℝ)^829 := by
    have hnat : (2623021459 : ℕ)^1085*10000000000000^829 ≤ 4298473849683^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623021459 5000000000 4298473849683 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410423971/10000000000 : ℝ)^1085 ≤ (44756032336011/100000000000000 : ℝ)^829 := by
    have hnat : (5410423971 : ℕ)^1085*100000000000000^829 ≤ 44756032336011^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410423971 10000000000 44756032336011 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251446423/1250000000 : ℝ), (2623021459/5000000000 : ℝ), (5410423971/10000000000 : ℝ)] ![(6129614573343/50000000000000 : ℝ), (4298473849683/10000000000000 : ℝ), (44756032336011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251446423/1250000000 : ℝ)|^1085 ≤ (6129614573343/50000000000000 : ℝ)^829
        have hw : |(-251446423/1250000000 : ℝ)|=(251446423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623021459/5000000000 : ℝ)|^1085 ≤ (4298473849683/10000000000000 : ℝ)^829
        have hw : |(2623021459/5000000000 : ℝ)|=(2623021459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410423971/10000000000 : ℝ)|^1085 ≤ (44756032336011/100000000000000 : ℝ)^829
        have hw : |(5410423971/10000000000 : ℝ)|=(5410423971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305550787/10000000000 : ℝ)*x 0 + (-1930920451/10000000000 : ℝ)*x 1 + (1082084793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305550787/10000000000 : ℝ)^1085 ≤ (43624016941201/100000000000000 : ℝ)^829 := by
    have hnat : (5305550787 : ℕ)^1085*100000000000000^829 ≤ 43624016941201^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305550787 10000000000 43624016941201 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930920451/10000000000 : ℝ)^1085 ≤ (1161995076973/10000000000000 : ℝ)^829 := by
    have hnat : (1930920451 : ℕ)^1085*10000000000000^829 ≤ 1161995076973^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930920451 10000000000 1161995076973 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082084793/2000000000 : ℝ)^1085 ≤ (44756032271051/100000000000000 : ℝ)^829 := by
    have hnat : (1082084793 : ℕ)^1085*100000000000000^829 ≤ 44756032271051^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082084793 2000000000 44756032271051 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305550787/10000000000 : ℝ), (-1930920451/10000000000 : ℝ), (1082084793/2000000000 : ℝ)] ![(43624016941201/100000000000000 : ℝ), (1161995076973/10000000000000 : ℝ), (44756032271051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305550787/10000000000 : ℝ)|^1085 ≤ (43624016941201/100000000000000 : ℝ)^829
        have hw : |(5305550787/10000000000 : ℝ)|=(5305550787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930920451/10000000000 : ℝ)|^1085 ≤ (1161995076973/10000000000000 : ℝ)^829
        have hw : |(-1930920451/10000000000 : ℝ)|=(1930920451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082084793/2000000000 : ℝ)|^1085 ≤ (44756032271051/100000000000000 : ℝ)^829
        have hw : |(1082084793/2000000000 : ℝ)|=(1082084793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326387703/2500000000 : ℝ)*x 0 + (5410423943/10000000000 : ℝ)*x 1 + (-1930920447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326387703/2500000000 : ℝ)^1085 ≤ (43624017210237/100000000000000 : ℝ)^829 := by
    have hnat : (1326387703 : ℕ)^1085*100000000000000^829 ≤ 43624017210237^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326387703 2500000000 43624017210237 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410423943/10000000000 : ℝ)^1085 ≤ (1398626001027/3125000000000 : ℝ)^829 := by
    have hnat : (5410423943 : ℕ)^1085*3125000000000^829 ≤ 1398626001027^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410423943 10000000000 1398626001027 3125000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930920447/10000000000 : ℝ)^1085 ≤ (5809975369113/50000000000000 : ℝ)^829 := by
    have hnat : (1930920447 : ℕ)^1085*50000000000000^829 ≤ 5809975369113^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930920447 10000000000 5809975369113 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326387703/2500000000 : ℝ), (5410423943/10000000000 : ℝ), (-1930920447/10000000000 : ℝ)] ![(43624017210237/100000000000000 : ℝ), (1398626001027/3125000000000 : ℝ), (5809975369113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326387703/2500000000 : ℝ)|^1085 ≤ (43624017210237/100000000000000 : ℝ)^829
        have hw : |(1326387703/2500000000 : ℝ)|=(1326387703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410423943/10000000000 : ℝ)|^1085 ≤ (1398626001027/3125000000000 : ℝ)^829
        have hw : |(5410423943/10000000000 : ℝ)|=(5410423943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930920447/10000000000 : ℝ)|^1085 ≤ (5809975369113/50000000000000 : ℝ)^829
        have hw : |(-1930920447/10000000000 : ℝ)|=(1930920447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s5_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4316786541/10000000000 : ℝ)*x 0 + (1123668993/2500000000 : ℝ)*x 1 + (2072719491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316786541/10000000000 : ℝ)^1085 ≤ (3330397307057/10000000000000 : ℝ)^829 := by
    have hnat : (4316786541 : ℕ)^1085*10000000000000^829 ≤ 3330397307057^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316786541 10000000000 3330397307057 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123668993/2500000000 : ℝ)^1085 ≤ (35111520717287/100000000000000 : ℝ)^829 := by
    have hnat : (1123668993 : ℕ)^1085*100000000000000^829 ≤ 35111520717287^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123668993 2500000000 35111520717287 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072719491/5000000000 : ℝ)^1085 ≤ (31584506202233/100000000000000 : ℝ)^829 := by
    have hnat : (2072719491 : ℕ)^1085*100000000000000^829 ≤ 31584506202233^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072719491 5000000000 31584506202233 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316786541/10000000000 : ℝ), (1123668993/2500000000 : ℝ), (2072719491/5000000000 : ℝ)] ![(3330397307057/10000000000000 : ℝ), (35111520717287/100000000000000 : ℝ), (31584506202233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316786541/10000000000 : ℝ)|^1085 ≤ (3330397307057/10000000000000 : ℝ)^829
        have hw : |(4316786541/10000000000 : ℝ)|=(4316786541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123668993/2500000000 : ℝ)|^1085 ≤ (35111520717287/100000000000000 : ℝ)^829
        have hw : |(1123668993/2500000000 : ℝ)|=(1123668993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072719491/5000000000 : ℝ)|^1085 ≤ (31584506202233/100000000000000 : ℝ)^829
        have hw : |(2072719491/5000000000 : ℝ)|=(2072719491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1123/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11197/100000 : ℝ) ^ (4339/1024 : ℝ) ≤ (1869752314102591/20000000000000000000 : ℝ) := by
    have hpowers : (11197/100000 : ℝ)^4339 ≤ (1869752314102591/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11197 : ℕ)^4339*20000000000000000000^1024 ≤ 1869752314102591^1024*100000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11197 100000 1869752314102591 20000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11197/100000 : ℝ)) (X := (1869752314102591/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (4339/1024 : ℝ) ≤ (236225457276017/781250000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^4339 ≤ (236225457276017/781250000000000000 : ℝ)^1024 := by
      have hnat : (14771 : ℕ)^4339*781250000000000000^1024 ≤ 236225457276017^1024*100000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 236225457276017 781250000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (236225457276017/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001869752314102591/10000000000000000000 : ℝ) ≤ (2000088245661821/2000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (10001869752314102591/10000000000000000000 : ℝ)^1024 ≤ (2000088245661821/2000000000000000 : ℝ)^4339 := by
      have hnat : (10001869752314102591 : ℕ)^1024*2000000000000000^4339 ≤ 2000088245661821^4339*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001869752314102591 10000000000000000000 2000088245661821 2000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088245661821/2000000000000000 : ℝ)) (X := (10001869752314102591/10000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039585620101843131/100000000000000000000 : ℝ) ≤ (2500233518937067/2500000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (100039585620101843131/100000000000000000000 : ℝ)^1024 ≤ (2500233518937067/2500000000000000 : ℝ)^4339 := by
      have hnat : (100039585620101843131 : ℕ)^1024*2500000000000000^4339 ≤ 2500233518937067^4339*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039585620101843131 100000000000000000000 2500233518937067 2500000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500233518937067/2500000000000000 : ℝ)) (X := (100039585620101843131/100000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (390861225457276017/390625000000000000 : ℝ) ≤ (10001426923187431/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (390861225457276017/390625000000000000 : ℝ)^1024 ≤ (10001426923187431/10000000000000000 : ℝ)^4339 := by
      have hnat : (390861225457276017 : ℕ)^1024*10000000000000000^4339 ≤ 10001426923187431^4339*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390861225457276017 390625000000000000 10001426923187431 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001426923187431/10000000000000000 : ℝ)) (X := (390861225457276017/390625000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1869752314102591/20000000000000000000 : ℝ) ≤ ((4466317515553015631/4467500000000000000 : ℝ)+2*(492847439163/357400000000000 : ℝ)*(11197/100000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (4466317515553015631/4467500000000000000 : ℝ)+2*(492847439163/357400000000000 : ℝ)*(11197/100000 : ℝ)=(2000088245661821/2000000000000000 : ℝ) by norm_num, show 1+2*(1869752314102591/20000000000000000000 : ℝ)=(10001869752314102591/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(236225457276017/781250000000000000 : ℝ)+(1869752314102591/20000000000000000000 : ℝ) ≤ ((4466317515553015631/4467500000000000000 : ℝ)+(492847439163/357400000000000 : ℝ)*((14771/100000 : ℝ)+(11197/100000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (4466317515553015631/4467500000000000000 : ℝ)+(492847439163/357400000000000 : ℝ)*((14771/100000 : ℝ)+(11197/100000 : ℝ))=(2500233518937067/2500000000000000 : ℝ) by norm_num, show 1+(236225457276017/781250000000000000 : ℝ)+(1869752314102591/20000000000000000000 : ℝ)=(100039585620101843131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(236225457276017/781250000000000000 : ℝ) ≤ ((4466317515553015631/4467500000000000000 : ℝ)+2*(492847439163/357400000000000 : ℝ)*(14771/100000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (4466317515553015631/4467500000000000000 : ℝ)+2*(492847439163/357400000000000 : ℝ)*(14771/100000 : ℝ)=(10001426923187431/10000000000000000 : ℝ) by norm_num, show 1+2*(236225457276017/781250000000000000 : ℝ)=(390861225457276017/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4466317515553015631/4467500000000000000 : ℝ)*(X 1 0+X 2 0)+(492847439163/357400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (4466317515553015631/4467500000000000000 : ℝ)) (alpha := (492847439163/357400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4466317515553015631/4467500000000000000 : ℝ)*(X 0 1+X 2 1)+(492847439163/357400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (4466317515553015631/4467500000000000000 : ℝ)) (alpha := (492847439163/357400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4466317515553015631/4467500000000000000 : ℝ)*(X 0 2+X 1 2)+(492847439163/357400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (4466317515553015631/4467500000000000000 : ℝ)) (alpha := (492847439163/357400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1005779319/5000000000 : ℝ)*X 0 0+(676377961/1250000000 : ℝ)*X 0 1+(131136173/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668547571/1250000000 : ℝ)*X 1 0+(-2095897609/10000000000 : ℝ)*X 1 1+(5245446683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674190447/5000000000 : ℝ)*X 2 0+(5245446183/10000000000 : ℝ)*X 2 1+(-2095897837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316761291/10000000000 : ℝ)*X 0 0+(2072082223/5000000000 : ℝ)*X 0 1+(449594389/1000000000 : ℝ)*X 0 2+(4316761291/10000000000 : ℝ)*X 1 0+(2072082223/5000000000 : ℝ)*X 1 1+(449594389/1000000000 : ℝ)*X 1 2+(4316761291/10000000000 : ℝ)*X 2 0+(2072082223/5000000000 : ℝ)*X 2 1+(449594389/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-251446423/1250000000 : ℝ)*X 0 0+(2623021459/5000000000 : ℝ)*X 0 1+(5410423971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305550787/10000000000 : ℝ)*X 1 0+(-1930920451/10000000000 : ℝ)*X 1 1+(1082084793/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326387703/2500000000 : ℝ)*X 2 0+(5410423943/10000000000 : ℝ)*X 2 1+(-1930920447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316786541/10000000000 : ℝ)*X 0 0+(1123668993/2500000000 : ℝ)*X 0 1+(2072719491/5000000000 : ℝ)*X 0 2+(4316786541/10000000000 : ℝ)*X 1 0+(1123668993/2500000000 : ℝ)*X 1 1+(2072719491/5000000000 : ℝ)*X 1 2+(4316786541/10000000000 : ℝ)*X 2 0+(1123668993/2500000000 : ℝ)*X 2 1+(2072719491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (985772176248889181221332969/111687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154183099/20000000000000 : ℝ)*(base19) + (1257096717/100000000000000 : ℝ)*(base23) + (258494773/100000000000000 : ℝ)*(lower2) + (80408629/25000000000000 : ℝ)*(lower4) + (25605223/20000000000000 : ℝ)*(lower5) + (2220561649237011/50000000000000 : ℝ)*(major0) + (2220561649237011/50000000000000 : ℝ)*(major1) + (2220561649237011/50000000000000 : ℝ)*(major2) + (754938940161751/12500000000000 : ℝ)*(sp0) + (6039524291603661/100000000000000 : ℝ)*(sp1) + (6039523805422439/100000000000000 : ℝ)*(sp2) + (1421352189803947/50000000000000 : ℝ)*(sp3) + (3385306287/25000000000000 : ℝ)*(sp4) + (16860615521/100000000000000 : ℝ)*(sp7) + (568544248044683/20000000000000 : ℝ)*(f.failure) + (1509881265629789/25000000000000 : ℝ)*(f.sum) + (4345576240509/1116875000000000000000000000 : ℝ)*base66 + (3814640573876868559/223375000000000000000000000000000 : ℝ)*base68 + (3972460337977118559/223375000000000000000000000000000 : ℝ)*base70 + (3773010612718493559/223375000000000000000000000000000 : ℝ)*base72 + (7309407242013/2233750000000000000000000000 : ℝ)*base74 + (2234117755710243559/223375000000000000000000000000000 : ℝ)*base76 + (1605473657614243559/223375000000000000000000000000000 : ℝ)*base78 + (4919394569327243559/223375000000000000000000000000000 : ℝ)*base80 + (75195342987/34902343750000000000000000 : ℝ)*base82 + (9315069/1000000000000000000000 : ℝ)*base89 + (9315069/1000000000000000000000 : ℝ)*base91 + (9315069/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316157972731060459457599791/55843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (991570023/100000000000000 : ℝ)*(base19) + (44205361/4000000000000 : ℝ)*(base23) + (110756613/100000000000000 : ℝ)*(upper3) + (3878239/10000000000000 : ℝ)*(lower4) + (15388419/12500000000000 : ℝ)*(upper5) + (2236702748615787/50000000000000 : ℝ)*(major0) + (2236702748615787/50000000000000 : ℝ)*(major1) + (2236702748615787/50000000000000 : ℝ)*(major2) + (20650233103/100000000000000 : ℝ)*(sp1) + (11055956193/50000000000000 : ℝ)*(sp2) + (6083426033817699/100000000000000 : ℝ)*(sp4) + (6083404392014573/100000000000000 : ℝ)*(sp5) + (760425352096411/12500000000000 : ℝ)*(sp6) + (22907078175437/800000000000 : ℝ)*(sp7) + (22907078175437/800000000000 : ℝ)*(f.failure) + (6083426033817699/100000000000000 : ℝ)*(f.sum) + (20291174076817/4467500000000000000000000000 : ℝ)*base66 + (356947692498629097/223375000000000000000000000000000 : ℝ)*base67 + (480915915843745903/223375000000000000000000000000000 : ℝ)*base70 + (985125583154620903/223375000000000000000000000000000 : ℝ)*base72 + (35027777105969/8935000000000000000000000000 : ℝ)*base74 + (119702137300620903/223375000000000000000000000000000 : ℝ)*base76 + (1498860716366495903/223375000000000000000000000000000 : ℝ)*base78 + (577265872498870903/223375000000000000000000000000000 : ℝ)*base80 + (43664523071139/8935000000000000000000000000 : ℝ)*base82 + (218091/40000000000000000000 : ℝ)*base89 + (218091/40000000000000000000 : ℝ)*base91 + (218091/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1380_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1380_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1380_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1380_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1380_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
