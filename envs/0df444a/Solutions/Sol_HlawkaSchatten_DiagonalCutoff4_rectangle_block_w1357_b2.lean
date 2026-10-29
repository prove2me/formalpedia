-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:53.84296+00:00
-- url     : https://prove2.me/submissions/fae0d04b-15ab-46ff-9cf7-d49aeb74fd4e

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
theorem support_rectangle_w1357_s6_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015539169/5000000000 : ℝ)*x 0 + (5411945803/10000000000 : ℝ)*x 1 + (5245047833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015539169/5000000000 : ℝ)^4317 ≤ (96659725651/781250000000 : ℝ)^3293 := by
    have hnat : (1015539169 : ℕ)^4317*781250000000^3293 ≤ 96659725651^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015539169 5000000000 96659725651 781250000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411945803/10000000000 : ℝ)^4317 ≤ (698644660159/1562500000000 : ℝ)^3293 := by
    have hnat : (5411945803 : ℕ)^4317*1562500000000^3293 ≤ 698644660159^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411945803 10000000000 698644660159 1562500000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245047833/10000000000 : ℝ)^4317 ≤ (21457148424481/50000000000000 : ℝ)^3293 := by
    have hnat : (5245047833 : ℕ)^4317*50000000000000^3293 ≤ 21457148424481^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245047833 10000000000 21457148424481 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015539169/5000000000 : ℝ), (5411945803/10000000000 : ℝ), (5245047833/10000000000 : ℝ)] ![(96659725651/781250000000 : ℝ), (698644660159/1562500000000 : ℝ), (21457148424481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015539169/5000000000 : ℝ)|^4317 ≤ (96659725651/781250000000 : ℝ)^3293
        have hw : |(-1015539169/5000000000 : ℝ)|=(1015539169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411945803/10000000000 : ℝ)|^4317 ≤ (698644660159/1562500000000 : ℝ)^3293
        have hw : |(5411945803/10000000000 : ℝ)|=(5411945803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245047833/10000000000 : ℝ)|^4317 ≤ (21457148424481/50000000000000 : ℝ)^3293
        have hw : |(5245047833/10000000000 : ℝ)|=(5245047833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167148063/312500000 : ℝ)*x 0 + (-423220491/2000000000 : ℝ)*x 1 + (2622523917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167148063/312500000 : ℝ)^4317 ≤ (22014946969431/50000000000000 : ℝ)^3293 := by
    have hnat : (167148063 : ℕ)^4317*50000000000000^3293 ≤ 22014946969431^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167148063 312500000 22014946969431 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423220491/2000000000 : ℝ)^4317 ≤ (13055809196463/100000000000000 : ℝ)^3293 := by
    have hnat : (423220491 : ℕ)^4317*100000000000000^3293 ≤ 13055809196463^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423220491 2000000000 13055809196463 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622523917/5000000000 : ℝ)^4317 ≤ (5364287107461/12500000000000 : ℝ)^3293 := by
    have hnat : (2622523917 : ℕ)^4317*12500000000000^3293 ≤ 5364287107461^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622523917 5000000000 5364287107461 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167148063/312500000 : ℝ), (-423220491/2000000000 : ℝ), (2622523917/5000000000 : ℝ)] ![(22014946969431/50000000000000 : ℝ), (13055809196463/100000000000000 : ℝ), (5364287107461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167148063/312500000 : ℝ)|^4317 ≤ (22014946969431/50000000000000 : ℝ)^3293
        have hw : |(167148063/312500000 : ℝ)|=(167148063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-423220491/2000000000 : ℝ)|^4317 ≤ (13055809196463/100000000000000 : ℝ)^3293
        have hw : |(-423220491/2000000000 : ℝ)|=(423220491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622523917/5000000000 : ℝ)|^4317 ≤ (5364287107461/12500000000000 : ℝ)^3293
        have hw : |(2622523917/5000000000 : ℝ)|=(2622523917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674369009/5000000000 : ℝ)*x 0 + (5245047833/10000000000 : ℝ)*x 1 + (-529025613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674369009/5000000000 : ℝ)^4317 ≤ (8805978792089/20000000000000 : ℝ)^3293 := by
    have hnat : (2674369009 : ℕ)^4317*20000000000000^3293 ≤ 8805978792089^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674369009 5000000000 8805978792089 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245047833/10000000000 : ℝ)^4317 ≤ (21457148424481/50000000000000 : ℝ)^3293 := by
    have hnat : (5245047833 : ℕ)^4317*50000000000000^3293 ≤ 21457148424481^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245047833 10000000000 21457148424481 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529025613/2500000000 : ℝ)^4317 ≤ (6527904586099/50000000000000 : ℝ)^3293 := by
    have hnat : (529025613 : ℕ)^4317*50000000000000^3293 ≤ 6527904586099^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529025613 2500000000 6527904586099 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674369009/5000000000 : ℝ), (5245047833/10000000000 : ℝ), (-529025613/2500000000 : ℝ)] ![(8805978792089/20000000000000 : ℝ), (21457148424481/50000000000000 : ℝ), (6527904586099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674369009/5000000000 : ℝ)|^4317 ≤ (8805978792089/20000000000000 : ℝ)^3293
        have hw : |(2674369009/5000000000 : ℝ)|=(2674369009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245047833/10000000000 : ℝ)|^4317 ≤ (21457148424481/50000000000000 : ℝ)^3293
        have hw : |(5245047833/10000000000 : ℝ)|=(5245047833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529025613/2500000000 : ℝ)|^4317 ≤ (6527904586099/50000000000000 : ℝ)^3293
        have hw : |(-529025613/2500000000 : ℝ)|=(529025613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161355589/5000000000 : ℝ)*x 0 + (129695379/312500000 : ℝ)*x 1 + (1125451483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161355589/5000000000 : ℝ)^4317 ≤ (16651755015127/50000000000000 : ℝ)^3293 := by
    have hnat : (2161355589 : ℕ)^4317*50000000000000^3293 ≤ 16651755015127^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161355589 5000000000 16651755015127 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129695379/312500000 : ℝ)^4317 ≤ (1262902728327/4000000000000 : ℝ)^3293 := by
    have hnat : (129695379 : ℕ)^4317*4000000000000^3293 ≤ 1262902728327^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129695379 312500000 1262902728327 4000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125451483/2500000000 : ℝ)^4317 ≤ (2195245109501/6250000000000 : ℝ)^3293 := by
    have hnat : (1125451483 : ℕ)^4317*6250000000000^3293 ≤ 2195245109501^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125451483 2500000000 2195245109501 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161355589/5000000000 : ℝ), (129695379/312500000 : ℝ), (1125451483/2500000000 : ℝ)] ![(16651755015127/50000000000000 : ℝ), (1262902728327/4000000000000 : ℝ), (2195245109501/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161355589/5000000000 : ℝ)|^4317 ≤ (16651755015127/50000000000000 : ℝ)^3293
        have hw : |(2161355589/5000000000 : ℝ)|=(2161355589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129695379/312500000 : ℝ)|^4317 ≤ (1262902728327/4000000000000 : ℝ)^3293
        have hw : |(129695379/312500000 : ℝ)|=(129695379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125451483/2500000000 : ℝ)|^4317 ≤ (2195245109501/6250000000000 : ℝ)^3293
        have hw : |(1125451483/2500000000 : ℝ)|=(1125451483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015545097/5000000000 : ℝ)*x 0 + (5245645887/10000000000 : ℝ)*x 1 + (5411344783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015545097/5000000000 : ℝ)^4317 ≤ (618626978161/5000000000000 : ℝ)^3293 := by
    have hnat : (1015545097 : ℕ)^4317*5000000000000^3293 ≤ 618626978161^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015545097 5000000000 618626978161 5000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245645887/10000000000 : ℝ)^4317 ≤ (42920711764821/100000000000000 : ℝ)^3293 := by
    have hnat : (5245645887 : ℕ)^4317*100000000000000^3293 ≤ 42920711764821^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245645887 10000000000 42920711764821 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411344783/10000000000 : ℝ)^4317 ≤ (44706748645391/100000000000000 : ℝ)^3293 := by
    have hnat : (5411344783 : ℕ)^4317*100000000000000^3293 ≤ 44706748645391^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411344783 10000000000 44706748645391 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015545097/5000000000 : ℝ), (5245645887/10000000000 : ℝ), (5411344783/10000000000 : ℝ)] ![(618626978161/5000000000000 : ℝ), (42920711764821/100000000000000 : ℝ), (44706748645391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015545097/5000000000 : ℝ)|^4317 ≤ (618626978161/5000000000000 : ℝ)^3293
        have hw : |(-1015545097/5000000000 : ℝ)|=(1015545097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245645887/10000000000 : ℝ)|^4317 ≤ (42920711764821/100000000000000 : ℝ)^3293
        have hw : |(5245645887/10000000000 : ℝ)|=(5245645887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411344783/10000000000 : ℝ)|^4317 ≤ (44706748645391/100000000000000 : ℝ)^3293
        have hw : |(5411344783/10000000000 : ℝ)|=(5411344783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305676127/10000000000 : ℝ)*x 0 + (-974902869/5000000000 : ℝ)*x 1 + (2705671903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305676127/10000000000 : ℝ)^4317 ≤ (435657691909/1000000000000 : ℝ)^3293 := by
    have hnat : (5305676127 : ℕ)^4317*1000000000000^3293 ≤ 435657691909^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305676127 10000000000 435657691909 1000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974902869/5000000000 : ℝ)^4317 ≤ (11727492729019/100000000000000 : ℝ)^3293 := by
    have hnat : (974902869 : ℕ)^4317*100000000000000^3293 ≤ 11727492729019^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974902869 5000000000 11727492729019 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705671903/5000000000 : ℝ)^4317 ≤ (44706738063757/100000000000000 : ℝ)^3293 := by
    have hnat : (2705671903 : ℕ)^4317*100000000000000^3293 ≤ 44706738063757^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705671903 5000000000 44706738063757 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305676127/10000000000 : ℝ), (-974902869/5000000000 : ℝ), (2705671903/5000000000 : ℝ)] ![(435657691909/1000000000000 : ℝ), (11727492729019/100000000000000 : ℝ), (44706738063757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305676127/10000000000 : ℝ)|^4317 ≤ (435657691909/1000000000000 : ℝ)^3293
        have hw : |(5305676127/10000000000 : ℝ)|=(5305676127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974902869/5000000000 : ℝ)|^4317 ≤ (11727492729019/100000000000000 : ℝ)^3293
        have hw : |(-974902869/5000000000 : ℝ)|=(974902869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705671903/5000000000 : ℝ)|^4317 ≤ (44706738063757/100000000000000 : ℝ)^3293
        have hw : |(2705671903/5000000000 : ℝ)|=(2705671903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652838123/5000000000 : ℝ)*x 0 + (5411343693/10000000000 : ℝ)*x 1 + (-1949805731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652838123/5000000000 : ℝ)^4317 ≤ (43565770471879/100000000000000 : ℝ)^3293 := by
    have hnat : (2652838123 : ℕ)^4317*100000000000000^3293 ≤ 43565770471879^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652838123 5000000000 43565770471879 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411343693/10000000000 : ℝ)^4317 ≤ (44706736839883/100000000000000 : ℝ)^3293 := by
    have hnat : (5411343693 : ℕ)^4317*100000000000000^3293 ≤ 44706736839883^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411343693 10000000000 44706736839883 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949805731/10000000000 : ℝ)^4317 ≤ (366484146057/3125000000000 : ℝ)^3293 := by
    have hnat : (1949805731 : ℕ)^4317*3125000000000^3293 ≤ 366484146057^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949805731 10000000000 366484146057 3125000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652838123/5000000000 : ℝ), (5411343693/10000000000 : ℝ), (-1949805731/10000000000 : ℝ)] ![(43565770471879/100000000000000 : ℝ), (44706736839883/100000000000000 : ℝ), (366484146057/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652838123/5000000000 : ℝ)|^4317 ≤ (43565770471879/100000000000000 : ℝ)^3293
        have hw : |(2652838123/5000000000 : ℝ)|=(2652838123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411343693/10000000000 : ℝ)|^4317 ≤ (44706736839883/100000000000000 : ℝ)^3293
        have hw : |(5411343693/10000000000 : ℝ)|=(5411343693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949805731/10000000000 : ℝ)|^4317 ≤ (366484146057/3125000000000 : ℝ)^3293
        have hw : |(-1949805731/10000000000 : ℝ)|=(1949805731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s6_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161368067/5000000000 : ℝ)*x 0 + (2250272971/5000000000 : ℝ)*x 1 + (259469937/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161368067/5000000000 : ℝ)^4317 ≤ (33303762087667/100000000000000 : ℝ)^3293 := by
    have hnat : (2161368067 : ℕ)^4317*100000000000000^3293 ≤ 33303762087667^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161368067 5000000000 33303762087667 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250272971/5000000000 : ℝ)^4317 ≤ (7022206933081/20000000000000 : ℝ)^3293 := by
    have hnat : (2250272971 : ℕ)^4317*20000000000000^3293 ≤ 7022206933081^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250272971 5000000000 7022206933081 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259469937/625000000 : ℝ)^4317 ≤ (31585203240353/100000000000000 : ℝ)^3293 := by
    have hnat : (259469937 : ℕ)^4317*100000000000000^3293 ≤ 31585203240353^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259469937 625000000 31585203240353 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161368067/5000000000 : ℝ), (2250272971/5000000000 : ℝ), (259469937/625000000 : ℝ)] ![(33303762087667/100000000000000 : ℝ), (7022206933081/20000000000000 : ℝ), (31585203240353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161368067/5000000000 : ℝ)|^4317 ≤ (33303762087667/100000000000000 : ℝ)^3293
        have hw : |(2161368067/5000000000 : ℝ)|=(2161368067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250272971/5000000000 : ℝ)|^4317 ≤ (7022206933081/20000000000000 : ℝ)^3293
        have hw : |(2250272971/5000000000 : ℝ)|=(2250272971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259469937/625000000 : ℝ)|^4317 ≤ (31585203240353/100000000000000 : ℝ)^3293
        have hw : |(259469937/625000000 : ℝ)|=(259469937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11183/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11177/100000 : ℝ) ^ (1079/256 : ℝ) ≤ (38071471806213/390625000000000000 : ℝ) := by
    have hpowers : (11177/100000 : ℝ)^1079 ≤ (38071471806213/390625000000000000 : ℝ)^256 := by
      have hnat : (11177 : ℕ)^1079*390625000000000000^256 ≤ 38071471806213^256*100000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11177 100000 38071471806213 390625000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11177/100000 : ℝ)) (X := (38071471806213/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3681/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (31142880545990883/100000000000000000000 : ℝ) := by
    have hpowers : (3681/25000 : ℝ)^1079 ≤ (31142880545990883/100000000000000000000 : ℝ)^256 := by
      have hnat : (3681 : ℕ)^1079*100000000000000000000^256 ≤ 31142880545990883^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 25000 31142880545990883 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/25000 : ℝ)) (X := (31142880545990883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (195350571471806213/195312500000000000 : ℝ) ≤ (1250057805062959/1250000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (195350571471806213/195312500000000000 : ℝ)^256 ≤ (1250057805062959/1250000000000000 : ℝ)^1079 := by
      have hnat : (195350571471806213 : ℕ)^256*1250000000000000^1079 ≤ 1250057805062959^1079*195312500000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195350571471806213 195312500000000000 1250057805062959 1250000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250057805062959/1250000000000000 : ℝ)) (X := (195350571471806213/195312500000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040889177328381411/100000000000000000000 : ℝ) ≤ (10000969971961897/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (100040889177328381411/100000000000000000000 : ℝ)^256 ≤ (10000969971961897/10000000000000000 : ℝ)^1079 := by
      have hnat : (100040889177328381411 : ℕ)^256*10000000000000000^1079 ≤ 10000969971961897^1079*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040889177328381411 100000000000000000000 10000969971961897 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000969971961897/10000000000000000 : ℝ)) (X := (100040889177328381411/100000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031142880545990883/50000000000000000000 : ℝ) ≤ (5000738751710061/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50031142880545990883/50000000000000000000 : ℝ)^256 ≤ (5000738751710061/5000000000000000 : ℝ)^1079 := by
      have hnat : (50031142880545990883 : ℕ)^256*5000000000000000^1079 ≤ 5000738751710061^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031142880545990883 50000000000000000000 5000738751710061 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000738751710061/5000000000000000 : ℝ)) (X := (50031142880545990883/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(38071471806213/390625000000000000 : ℝ) ≤ ((17730147459124681467/17735000000000000000 : ℝ)+2*(20301258329/14188000000000 : ℝ)*(11177/100000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (17730147459124681467/17735000000000000000 : ℝ)+2*(20301258329/14188000000000 : ℝ)*(11177/100000 : ℝ)=(1250057805062959/1250000000000000 : ℝ) by norm_num, show 1+2*(38071471806213/390625000000000000 : ℝ)=(195350571471806213/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31142880545990883/100000000000000000000 : ℝ)+(38071471806213/390625000000000000 : ℝ) ≤ ((17730147459124681467/17735000000000000000 : ℝ)+(20301258329/14188000000000 : ℝ)*((3681/25000 : ℝ)+(11177/100000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (17730147459124681467/17735000000000000000 : ℝ)+(20301258329/14188000000000 : ℝ)*((3681/25000 : ℝ)+(11177/100000 : ℝ))=(10000969971961897/10000000000000000 : ℝ) by norm_num, show 1+(31142880545990883/100000000000000000000 : ℝ)+(38071471806213/390625000000000000 : ℝ)=(100040889177328381411/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31142880545990883/100000000000000000000 : ℝ) ≤ ((17730147459124681467/17735000000000000000 : ℝ)+2*(20301258329/14188000000000 : ℝ)*(3681/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (17730147459124681467/17735000000000000000 : ℝ)+2*(20301258329/14188000000000 : ℝ)*(3681/25000 : ℝ)=(5000738751710061/5000000000000000 : ℝ) by norm_num, show 1+2*(31142880545990883/100000000000000000000 : ℝ)=(50031142880545990883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17730147459124681467/17735000000000000000 : ℝ)*(X 1 0+X 2 0)+(20301258329/14188000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (17730147459124681467/17735000000000000000 : ℝ)) (alpha := (20301258329/14188000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17730147459124681467/17735000000000000000 : ℝ)*(X 0 1+X 2 1)+(20301258329/14188000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (17730147459124681467/17735000000000000000 : ℝ)) (alpha := (20301258329/14188000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17730147459124681467/17735000000000000000 : ℝ)*(X 0 2+X 1 2)+(20301258329/14188000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (17730147459124681467/17735000000000000000 : ℝ)) (alpha := (20301258329/14188000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1015539169/5000000000 : ℝ)*X 0 0+(5411945803/10000000000 : ℝ)*X 0 1+(5245047833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167148063/312500000 : ℝ)*X 1 0+(-423220491/2000000000 : ℝ)*X 1 1+(2622523917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674369009/5000000000 : ℝ)*X 2 0+(5245047833/10000000000 : ℝ)*X 2 1+(-529025613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161355589/5000000000 : ℝ)*X 0 0+(129695379/312500000 : ℝ)*X 0 1+(1125451483/2500000000 : ℝ)*X 0 2+(2161355589/5000000000 : ℝ)*X 1 0+(129695379/312500000 : ℝ)*X 1 1+(1125451483/2500000000 : ℝ)*X 1 2+(2161355589/5000000000 : ℝ)*X 2 0+(129695379/312500000 : ℝ)*X 2 1+(1125451483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1015545097/5000000000 : ℝ)*X 0 0+(5245645887/10000000000 : ℝ)*X 0 1+(5411344783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305676127/10000000000 : ℝ)*X 1 0+(-974902869/5000000000 : ℝ)*X 1 1+(2705671903/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652838123/5000000000 : ℝ)*X 2 0+(5411343693/10000000000 : ℝ)*X 2 1+(-1949805731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2161368067/5000000000 : ℝ)*X 0 0+(2250272971/5000000000 : ℝ)*X 0 1+(259469937/625000000 : ℝ)*X 0 2+(2161368067/5000000000 : ℝ)*X 1 0+(2250272971/5000000000 : ℝ)*X 1 1+(259469937/625000000 : ℝ)*X 1 2+(2161368067/5000000000 : ℝ)*X 2 0+(2250272971/5000000000 : ℝ)*X 2 1+(259469937/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4798950720229151785610884449/443375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2027329167/100000000000000 : ℝ)*(base19) + (1893447121/100000000000000 : ℝ)*(base23) + (2275261/3125000000000 : ℝ)*(lower2) + (135573757/50000000000000 : ℝ)*(upper3) + (10888821/6250000000000 : ℝ)*(upper5) + (2209081341261151/50000000000000 : ℝ)*(major0) + (2209081341261151/50000000000000 : ℝ)*(major1) + (2209081341261151/50000000000000 : ℝ)*(major2) + (2995863988342891/50000000000000 : ℝ)*(sp0) + (18724273900237/312500000000 : ℝ)*(sp1) + (2995883890978943/50000000000000 : ℝ)*(sp2) + (1422266994365537/50000000000000 : ℝ)*(sp3) + (5212339903/12500000000000 : ℝ)*(sp4) + (21340119059/100000000000000 : ℝ)*(sp7) + (1422277664425067/50000000000000 : ℝ)*(f.failure) + (5991769675405007/100000000000000 : ℝ)*(f.sum) + (711117379949/443375000000000000000000000 : ℝ)*base66 + (7631034669748538517/886750000000000000000000000000000 : ℝ)*base67 + (12932044250581038517/886750000000000000000000000000000 : ℝ)*base69 + (444974205449038517/886750000000000000000000000000000 : ℝ)*base71 + (21396256377/44337500000000000000000000 : ℝ)*base74 + (7360796554372461483/886750000000000000000000000000000 : ℝ)*base76 + (3690806963019961483/886750000000000000000000000000000 : ℝ)*base78 + (19891722203501538517/886750000000000000000000000000000 : ℝ)*base79 + (14178257910331/1773500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (24663459/5000000000000000000000 : ℝ)*base89 + (24663459/5000000000000000000000 : ℝ)*base91 + (24663459/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3452812003049734042551/709400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1084546937/50000000000000 : ℝ)*(base19) + (2370513249/100000000000000 : ℝ)*(base23) + (6963949/100000000000000 : ℝ)*(lower3) + (27479613/100000000000000 : ℝ)*(lower4) + (4450085826798611/100000000000000 : ℝ)*(major0) + (4450085826798611/100000000000000 : ℝ)*(major1) + (4450085826798611/100000000000000 : ℝ)*(major2) + (189968513/2000000000000 : ℝ)*(sp0) + (34313327637/100000000000000 : ℝ)*(sp1) + (7214261079/20000000000000 : ℝ)*(sp2) + (75438168954789/1250000000000 : ℝ)*(sp4) + (3017513266193629/50000000000000 : ℝ)*(sp5) + (3017512286495063/50000000000000 : ℝ)*(sp6) + (286510847654749/10000000000000 : ℝ)*(sp7) + (286510847654749/10000000000000 : ℝ)*(f.failure) + (603506301480877/10000000000000 : ℝ)*(f.sum) + (5821334396573/709400000000000000000000000 : ℝ)*base66 + (688902072788207663/1773500000000000000000000000000000 : ℝ)*base68 + (12782516103491792337/1773500000000000000000000000000000 : ℝ)*base69 + (9394271625516207663/1773500000000000000000000000000000 : ℝ)*base72 + (636458032951/110843750000000000000000000 : ℝ)*base74 + (7700671039785792337/1773500000000000000000000000000000 : ℝ)*base75 + (18724329063994207663/1773500000000000000000000000000000 : ℝ)*base78 + (17333298582831292337/1773500000000000000000000000000000 : ℝ)*base79 + (1621255417303/3547000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (8620773/1000000000000000000000 : ℝ)*base89 + (8620773/1000000000000000000000 : ℝ)*base91 + (8620773/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1357_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1357_s7_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031085971/10000000000 : ℝ)*x 0 + (2705946001/5000000000 : ℝ)*x 1 + (5245096477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031085971/10000000000 : ℝ)^4317 ≤ (12372505839079/100000000000000 : ℝ)^3293 := by
    have hnat : (2031085971 : ℕ)^4317*100000000000000^3293 ≤ 12372505839079^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031085971 10000000000 12372505839079 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705946001/5000000000 : ℝ)^4317 ≤ (22356337763109/50000000000000 : ℝ)^3293 := by
    have hnat : (2705946001 : ℕ)^4317*50000000000000^3293 ≤ 22356337763109^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705946001 5000000000 22356337763109 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245096477/10000000000 : ℝ)^4317 ≤ (42914818611353/100000000000000 : ℝ)^3293 := by
    have hnat : (5245096477 : ℕ)^4317*100000000000000^3293 ≤ 42914818611353^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245096477 10000000000 42914818611353 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031085971/10000000000 : ℝ), (2705946001/5000000000 : ℝ), (5245096477/10000000000 : ℝ)] ![(12372505839079/100000000000000 : ℝ), (22356337763109/50000000000000 : ℝ), (42914818611353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031085971/10000000000 : ℝ)|^4317 ≤ (12372505839079/100000000000000 : ℝ)^3293
        have hw : |(-2031085971/10000000000 : ℝ)|=(2031085971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705946001/5000000000 : ℝ)|^4317 ≤ (22356337763109/50000000000000 : ℝ)^3293
        have hw : |(2705946001/5000000000 : ℝ)|=(2705946001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245096477/10000000000 : ℝ)|^4317 ≤ (42914818611353/100000000000000 : ℝ)^3293
        have hw : |(5245096477/10000000000 : ℝ)|=(5245096477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674361889/5000000000 : ℝ)*x 0 + (-1058028519/5000000000 : ℝ)*x 1 + (2622548203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674361889/5000000000 : ℝ)^4317 ≤ (8805948057569/20000000000000 : ℝ)^3293 := by
    have hnat : (2674361889 : ℕ)^4317*20000000000000^3293 ≤ 8805948057569^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674361889 5000000000 8805948057569 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058028519/5000000000 : ℝ)^4317 ≤ (13055441851223/100000000000000 : ℝ)^3293 := by
    have hnat : (1058028519 : ℕ)^4317*100000000000000^3293 ≤ 13055441851223^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058028519 5000000000 13055441851223 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622548203/5000000000 : ℝ)^4317 ≤ (10728704462449/25000000000000 : ℝ)^3293 := by
    have hnat : (2622548203 : ℕ)^4317*25000000000000^3293 ≤ 10728704462449^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622548203 5000000000 10728704462449 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674361889/5000000000 : ℝ), (-1058028519/5000000000 : ℝ), (2622548203/5000000000 : ℝ)] ![(8805948057569/20000000000000 : ℝ), (13055441851223/100000000000000 : ℝ), (10728704462449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674361889/5000000000 : ℝ)|^4317 ≤ (8805948057569/20000000000000 : ℝ)^3293
        have hw : |(2674361889/5000000000 : ℝ)|=(2674361889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058028519/5000000000 : ℝ)|^4317 ≤ (13055441851223/100000000000000 : ℝ)^3293
        have hw : |(-1058028519/5000000000 : ℝ)|=(1058028519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622548203/5000000000 : ℝ)|^4317 ≤ (10728704462449/25000000000000 : ℝ)^3293
        have hw : |(2622548203/5000000000 : ℝ)|=(2622548203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167147619/312500000 : ℝ)*x 0 + (5245096417/10000000000 : ℝ)*x 1 + (-2116056983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167147619/312500000 : ℝ)^4317 ≤ (44029740611593/100000000000000 : ℝ)^3293 := by
    have hnat : (167147619 : ℕ)^4317*100000000000000^3293 ≤ 44029740611593^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167147619 312500000 44029740611593 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245096417/10000000000 : ℝ)^4317 ≤ (5364352245973/12500000000000 : ℝ)^3293 := by
    have hnat : (5245096417 : ℕ)^4317*12500000000000^3293 ≤ 5364352245973^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245096417 10000000000 5364352245973 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116056983/10000000000 : ℝ)^4317 ≤ (1305544140637/10000000000000 : ℝ)^3293 := by
    have hnat : (2116056983 : ℕ)^4317*10000000000000^3293 ≤ 1305544140637^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116056983 10000000000 1305544140637 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167147619/312500000 : ℝ), (5245096417/10000000000 : ℝ), (-2116056983/10000000000 : ℝ)] ![(44029740611593/100000000000000 : ℝ), (5364352245973/12500000000000 : ℝ), (1305544140637/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167147619/312500000 : ℝ)|^4317 ≤ (44029740611593/100000000000000 : ℝ)^3293
        have hw : |(167147619/312500000 : ℝ)|=(167147619/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245096417/10000000000 : ℝ)|^4317 ≤ (5364352245973/12500000000000 : ℝ)^3293
        have hw : |(5245096417/10000000000 : ℝ)|=(5245096417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2116056983/10000000000 : ℝ)|^4317 ≤ (1305544140637/10000000000000 : ℝ)^3293
        have hw : |(-2116056983/10000000000 : ℝ)|=(2116056983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216135737/500000000 : ℝ)*x 0 + (259397473/625000000 : ℝ)*x 1 + (562712207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216135737/500000000 : ℝ)^4317 ≤ (6660709201337/20000000000000 : ℝ)^3293 := by
    have hnat : (216135737 : ℕ)^4317*20000000000000^3293 ≤ 6660709201337^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216135737 500000000 6660709201337 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259397473/625000000 : ℝ)^4317 ≤ (31573639711431/100000000000000 : ℝ)^3293 := by
    have hnat : (259397473 : ℕ)^4317*100000000000000^3293 ≤ 31573639711431^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259397473 625000000 31573639711431 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562712207/1250000000 : ℝ)^4317 ≤ (17561407134431/50000000000000 : ℝ)^3293 := by
    have hnat : (562712207 : ℕ)^4317*50000000000000^3293 ≤ 17561407134431^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562712207 1250000000 17561407134431 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216135737/500000000 : ℝ), (259397473/625000000 : ℝ), (562712207/1250000000 : ℝ)] ![(6660709201337/20000000000000 : ℝ), (31573639711431/100000000000000 : ℝ), (17561407134431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216135737/500000000 : ℝ)|^4317 ≤ (6660709201337/20000000000000 : ℝ)^3293
        have hw : |(216135737/500000000 : ℝ)|=(216135737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259397473/625000000 : ℝ)|^4317 ≤ (31573639711431/100000000000000 : ℝ)^3293
        have hw : |(259397473/625000000 : ℝ)|=(259397473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562712207/1250000000 : ℝ)|^4317 ≤ (17561407134431/50000000000000 : ℝ)^3293
        have hw : |(562712207/1250000000 : ℝ)|=(562712207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-507774469/2500000000 : ℝ)*x 0 + (655711769/1250000000 : ℝ)*x 1 + (5411291319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507774469/2500000000 : ℝ)^4317 ≤ (3093150227597/25000000000000 : ℝ)^3293 := by
    have hnat : (507774469 : ℕ)^4317*25000000000000^3293 ≤ 3093150227597^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507774469 2500000000 3093150227597 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655711769/1250000000 : ℝ)^4317 ≤ (21460614740177/50000000000000 : ℝ)^3293 := by
    have hnat : (655711769 : ℕ)^4317*50000000000000^3293 ≤ 21460614740177^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655711769 1250000000 21460614740177 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411291319/10000000000 : ℝ)^4317 ≤ (44706169591507/100000000000000 : ℝ)^3293 := by
    have hnat : (5411291319 : ℕ)^4317*100000000000000^3293 ≤ 44706169591507^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411291319 10000000000 44706169591507 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507774469/2500000000 : ℝ), (655711769/1250000000 : ℝ), (5411291319/10000000000 : ℝ)] ![(3093150227597/25000000000000 : ℝ), (21460614740177/50000000000000 : ℝ), (44706169591507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507774469/2500000000 : ℝ)|^4317 ≤ (3093150227597/25000000000000 : ℝ)^3293
        have hw : |(-507774469/2500000000 : ℝ)|=(507774469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655711769/1250000000 : ℝ)|^4317 ≤ (21460614740177/50000000000000 : ℝ)^3293
        have hw : |(655711769/1250000000 : ℝ)|=(655711769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411291319/10000000000 : ℝ)|^4317 ≤ (44706169591507/100000000000000 : ℝ)^3293
        have hw : |(5411291319/10000000000 : ℝ)|=(5411291319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42445501/80000000 : ℝ)*x 0 + (-389972417/2000000000 : ℝ)*x 1 + (5411291357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42445501/80000000 : ℝ)^4317 ≤ (21782946480739/50000000000000 : ℝ)^3293 := by
    have hnat : (42445501 : ℕ)^4317*50000000000000^3293 ≤ 21782946480739^3293*80000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42445501 80000000 21782946480739 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389972417/2000000000 : ℝ)^4317 ≤ (732996064351/6250000000000 : ℝ)^3293 := by
    have hnat : (389972417 : ℕ)^4317*6250000000000^3293 ≤ 732996064351^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389972417 2000000000 732996064351 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411291357/10000000000 : ℝ)^4317 ≤ (22353085001537/50000000000000 : ℝ)^3293 := by
    have hnat : (5411291357 : ℕ)^4317*50000000000000^3293 ≤ 22353085001537^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411291357 10000000000 22353085001537 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42445501/80000000 : ℝ), (-389972417/2000000000 : ℝ), (5411291357/10000000000 : ℝ)] ![(21782946480739/50000000000000 : ℝ), (732996064351/6250000000000 : ℝ), (22353085001537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42445501/80000000 : ℝ)|^4317 ≤ (21782946480739/50000000000000 : ℝ)^3293
        have hw : |(42445501/80000000 : ℝ)|=(42445501/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389972417/2000000000 : ℝ)|^4317 ≤ (732996064351/6250000000000 : ℝ)^3293
        have hw : |(-389972417/2000000000 : ℝ)|=(389972417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411291357/10000000000 : ℝ)|^4317 ≤ (22353085001537/50000000000000 : ℝ)^3293
        have hw : |(5411291357/10000000000 : ℝ)|=(5411291357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305687569/10000000000 : ℝ)*x 0 + (5411291469/10000000000 : ℝ)*x 1 + (-1949862007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305687569/10000000000 : ℝ)^4317 ≤ (5445736544833/12500000000000 : ℝ)^3293 := by
    have hnat : (5305687569 : ℕ)^4317*12500000000000^3293 ≤ 5445736544833^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305687569 10000000000 5445736544833 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411291469/10000000000 : ℝ)^4317 ≤ (44706171216113/100000000000000 : ℝ)^3293 := by
    have hnat : (5411291469 : ℕ)^4317*100000000000000^3293 ≤ 44706171216113^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411291469 10000000000 44706171216113 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949862007/10000000000 : ℝ)^4317 ≤ (11727936414577/100000000000000 : ℝ)^3293 := by
    have hnat : (1949862007 : ℕ)^4317*100000000000000^3293 ≤ 11727936414577^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949862007 10000000000 11727936414577 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305687569/10000000000 : ℝ), (5411291469/10000000000 : ℝ), (-1949862007/10000000000 : ℝ)] ![(5445736544833/12500000000000 : ℝ), (44706171216113/100000000000000 : ℝ), (11727936414577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305687569/10000000000 : ℝ)|^4317 ≤ (5445736544833/12500000000000 : ℝ)^3293
        have hw : |(5305687569/10000000000 : ℝ)|=(5305687569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411291469/10000000000 : ℝ)|^4317 ≤ (44706171216113/100000000000000 : ℝ)^3293
        have hw : |(5411291469/10000000000 : ℝ)|=(5411291469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949862007/10000000000 : ℝ)|^4317 ≤ (11727936414577/100000000000000 : ℝ)^3293
        have hw : |(-1949862007/10000000000 : ℝ)|=(1949862007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s7_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322740067/10000000000 : ℝ)*x 0 + (112510971/250000000 : ℝ)*x 1 + (32434569/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322740067/10000000000 : ℝ)^4317 ≤ (16651900905647/50000000000000 : ℝ)^3293 := by
    have hnat : (4322740067 : ℕ)^4317*50000000000000^3293 ≤ 16651900905647^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322740067 10000000000 16651900905647 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112510971/250000000 : ℝ)^4317 ≤ (4388742410703/12500000000000 : ℝ)^3293 := by
    have hnat : (112510971 : ℕ)^4317*12500000000000^3293 ≤ 4388742410703^3293*250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112510971 250000000 4388742410703 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32434569/78125000 : ℝ)^4317 ≤ (15793129443433/50000000000000 : ℝ)^3293 := by
    have hnat : (32434569 : ℕ)^4317*50000000000000^3293 ≤ 15793129443433^3293*78125000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32434569 78125000 15793129443433 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322740067/10000000000 : ℝ), (112510971/250000000 : ℝ), (32434569/78125000 : ℝ)] ![(16651900905647/50000000000000 : ℝ), (4388742410703/12500000000000 : ℝ), (15793129443433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322740067/10000000000 : ℝ)|^4317 ≤ (16651900905647/50000000000000 : ℝ)^3293
        have hw : |(4322740067/10000000000 : ℝ)|=(4322740067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112510971/250000000 : ℝ)|^4317 ≤ (4388742410703/12500000000000 : ℝ)^3293
        have hw : |(112510971/250000000 : ℝ)|=(112510971/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32434569/78125000 : ℝ)|^4317 ≤ (15793129443433/50000000000000 : ℝ)^3293
        have hw : |(32434569/78125000 : ℝ)|=(32434569/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (699/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3679/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11183/100000 : ℝ) ^ (1079/256 : ℝ) ≤ (9768367774029851/100000000000000000000 : ℝ) := by
    have hpowers : (11183/100000 : ℝ)^1079 ≤ (9768367774029851/100000000000000000000 : ℝ)^256 := by
      have hnat : (11183 : ℕ)^1079*100000000000000000000^256 ≤ 9768367774029851^256*100000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11183 100000 9768367774029851 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11183/100000 : ℝ)) (X := (9768367774029851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (1079/256 : ℝ) ≤ (1243220968355751/4000000000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^1079 ≤ (1243220968355751/4000000000000000000 : ℝ)^256 := by
      have hnat : (14717 : ℕ)^1079*4000000000000000000^256 ≤ 1243220968355751^256*100000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 1243220968355751 4000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (1243220968355751/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009768367774029851/50000000000000000000 : ℝ) ≤ (400018539505841/400000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50009768367774029851/50000000000000000000 : ℝ)^256 ≤ (400018539505841/400000000000000 : ℝ)^1079 := by
      have hnat : (50009768367774029851 : ℕ)^256*400000000000000^1079 ≤ 400018539505841^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009768367774029851 50000000000000000000 400018539505841 400000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400018539505841/400000000000000 : ℝ)) (X := (50009768367774029851/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020424445991461813/50000000000000000000 : ℝ) ≤ (10000969016462847/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50020424445991461813/50000000000000000000 : ℝ)^256 ≤ (10000969016462847/10000000000000000 : ℝ)^1079 := by
      have hnat : (50020424445991461813 : ℕ)^256*10000000000000000^1079 ≤ 10000969016462847^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020424445991461813 50000000000000000000 10000969016462847 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000969016462847/10000000000000000 : ℝ)) (X := (50020424445991461813/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001243220968355751/2000000000000000000 : ℝ) ≤ (10001474545279669/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (2001243220968355751/2000000000000000000 : ℝ)^256 ≤ (10001474545279669/10000000000000000 : ℝ)^1079 := by
      have hnat : (2001243220968355751 : ℕ)^256*10000000000000000^1079 ≤ 10001474545279669^1079*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001243220968355751 2000000000000000000 10001474545279669 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001474545279669/10000000000000000 : ℝ)) (X := (2001243220968355751/2000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9768367774029851/100000000000000000000 : ℝ) ≤ ((17665165653912005749/17670000000000000000 : ℝ)+2*(252764408411/176700000000000 : ℝ)*(11183/100000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (17665165653912005749/17670000000000000000 : ℝ)+2*(252764408411/176700000000000 : ℝ)*(11183/100000 : ℝ)=(400018539505841/400000000000000 : ℝ) by norm_num, show 1+2*(9768367774029851/100000000000000000000 : ℝ)=(50009768367774029851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1243220968355751/4000000000000000000 : ℝ)+(9768367774029851/100000000000000000000 : ℝ) ≤ ((17665165653912005749/17670000000000000000 : ℝ)+(252764408411/176700000000000 : ℝ)*((14717/100000 : ℝ)+(11183/100000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (17665165653912005749/17670000000000000000 : ℝ)+(252764408411/176700000000000 : ℝ)*((14717/100000 : ℝ)+(11183/100000 : ℝ))=(10000969016462847/10000000000000000 : ℝ) by norm_num, show 1+(1243220968355751/4000000000000000000 : ℝ)+(9768367774029851/100000000000000000000 : ℝ)=(50020424445991461813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1243220968355751/4000000000000000000 : ℝ) ≤ ((17665165653912005749/17670000000000000000 : ℝ)+2*(252764408411/176700000000000 : ℝ)*(14717/100000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (17665165653912005749/17670000000000000000 : ℝ)+2*(252764408411/176700000000000 : ℝ)*(14717/100000 : ℝ)=(10001474545279669/10000000000000000 : ℝ) by norm_num, show 1+2*(1243220968355751/4000000000000000000 : ℝ)=(2001243220968355751/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17665165653912005749/17670000000000000000 : ℝ)*(X 1 0+X 2 0)+(252764408411/176700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (17665165653912005749/17670000000000000000 : ℝ)) (alpha := (252764408411/176700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17665165653912005749/17670000000000000000 : ℝ)*(X 0 1+X 2 1)+(252764408411/176700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (17665165653912005749/17670000000000000000 : ℝ)) (alpha := (252764408411/176700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17665165653912005749/17670000000000000000 : ℝ)*(X 0 2+X 1 2)+(252764408411/176700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (17665165653912005749/17670000000000000000 : ℝ)) (alpha := (252764408411/176700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2031085971/10000000000 : ℝ)*X 0 0+(2705946001/5000000000 : ℝ)*X 0 1+(5245096477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674361889/5000000000 : ℝ)*X 1 0+(-1058028519/5000000000 : ℝ)*X 1 1+(2622548203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167147619/312500000 : ℝ)*X 2 0+(5245096417/10000000000 : ℝ)*X 2 1+(-2116056983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216135737/500000000 : ℝ)*X 0 0+(259397473/625000000 : ℝ)*X 0 1+(562712207/1250000000 : ℝ)*X 0 2+(216135737/500000000 : ℝ)*X 1 0+(259397473/625000000 : ℝ)*X 1 1+(562712207/1250000000 : ℝ)*X 1 2+(216135737/500000000 : ℝ)*X 2 0+(259397473/625000000 : ℝ)*X 2 1+(562712207/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-507774469/2500000000 : ℝ)*X 0 0+(655711769/1250000000 : ℝ)*X 0 1+(5411291319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42445501/80000000 : ℝ)*X 1 0+(-389972417/2000000000 : ℝ)*X 1 1+(5411291357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305687569/10000000000 : ℝ)*X 2 0+(5411291469/10000000000 : ℝ)*X 2 1+(-1949862007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322740067/10000000000 : ℝ)*X 0 0+(112510971/250000000 : ℝ)*X 0 1+(32434569/78125000 : ℝ)*X 0 2+(4322740067/10000000000 : ℝ)*X 1 0+(112510971/250000000 : ℝ)*X 1 1+(32434569/78125000 : ℝ)*X 1 2+(4322740067/10000000000 : ℝ)*X 2 0+(112510971/250000000 : ℝ)*X 2 1+(32434569/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3341674921885471460418015487/294500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2054165209/100000000000000 : ℝ)*(base19) + (1939743657/100000000000000 : ℝ)*(base23) + (15837453/20000000000000 : ℝ)*(lower2) + (116510261/50000000000000 : ℝ)*(upper3) + (197617049/100000000000000 : ℝ)*(upper5) + (4420874998326079/100000000000000 : ℝ)*(major0) + (4420874998326079/100000000000000 : ℝ)*(major1) + (4420874998326079/100000000000000 : ℝ)*(major2) + (47963246600617/800000000000 : ℝ)*(sp0) + (5995445959197893/100000000000000 : ℝ)*(sp1) + (1199089214723889/20000000000000 : ℝ)*(sp2) + (2846280744655857/100000000000000 : ℝ)*(sp3) + (42188285977/100000000000000 : ℝ)*(sp4) + (5215100433/25000000000000 : ℝ)*(sp7) + (284630160505759/10000000000000 : ℝ)*(f.failure) + (2997724006681551/50000000000000 : ℝ)*(f.sum) + (22481418386513/4417500000000000000000000000 : ℝ)*base66 + (489549330350904003/31000000000000000000000000000000 : ℝ)*base67 + (108277816436904003/31000000000000000000000000000000 : ℝ)*base69 + (432140226742904003/31000000000000000000000000000000 : ℝ)*base71 + (43583214306599/8835000000000000000000000000 : ℝ)*base73 + (610578558066904003/31000000000000000000000000000000 : ℝ)*base75 + (180834175756904003/31000000000000000000000000000000 : ℝ)*base77 + (89095428209904003/31000000000000000000000000000000 : ℝ)*base79 + (12833332137667/4417500000000000000000000000 : ℝ)*base81 + (6247543/1000000000000000000000 : ℝ)*base89 + (6247543/1000000000000000000000 : ℝ)*base91 + (6247543/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14101430351805048979372753/1472500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267554501/20000000000000 : ℝ)*(base19) + (806643879/50000000000000 : ℝ)*(base23) + (459244523/100000000000000 : ℝ)*(lower1) + (177567419/100000000000000 : ℝ)*(upper3) + (27795361/20000000000000 : ℝ)*(lower4) + (6681291/5000000000000 : ℝ)*(upper5) + (44527811082503/1000000000000 : ℝ)*(major0) + (44527811082503/1000000000000 : ℝ)*(major1) + (44527811082503/1000000000000 : ℝ)*(major2) + (9531458039/100000000000000 : ℝ)*(sp2) + (6038718111792279/100000000000000 : ℝ)*(sp4) + (241548670960791/4000000000000 : ℝ)*(sp5) + (6038706967046483/100000000000000 : ℝ)*(sp6) + (1433421892745419/50000000000000 : ℝ)*(sp7) + (1433421892745419/50000000000000 : ℝ)*(f.failure) + (6038718111792279/100000000000000 : ℝ)*(f.sum) + (3658754720773/883500000000000000000000000 : ℝ)*base65 + (15125707160120171/310000000000000000000000000000 : ℝ)*base67 + (2253076544530171/310000000000000000000000000000 : ℝ)*base69 + (53865914200290171/310000000000000000000000000000 : ℝ)*base71 + (321062067229/353400000000000000000000000 : ℝ)*base73 + (37960327644409829/310000000000000000000000000000 : ℝ)*base76 + (3048303031450171/310000000000000000000000000000 : ℝ)*base77 + (698292471700171/310000000000000000000000000000 : ℝ)*base79 + (134353526153/883500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (54064637/5000000000000000000000 : ℝ)*base90 + (54064637/5000000000000000000000 : ℝ)*base92 + (54064637/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1357_s8_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031086419/10000000000 : ℝ)*x 0 + (5411883933/10000000000 : ℝ)*x 1 + (1311276073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031086419/10000000000 : ℝ)^4317 ≤ (1546563677091/12500000000000 : ℝ)^3293 := by
    have hnat : (2031086419 : ℕ)^4317*12500000000000^3293 ≤ 1546563677091^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031086419 10000000000 1546563677091 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411883933/10000000000 : ℝ)^4317 ≤ (8942517626047/20000000000000 : ℝ)^3293 := by
    have hnat : (5411883933 : ℕ)^4317*20000000000000^3293 ≤ 8942517626047^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411883933 10000000000 8942517626047 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311276073/2500000000 : ℝ)^4317 ≤ (10728725609071/25000000000000 : ℝ)^3293 := by
    have hnat : (1311276073 : ℕ)^4317*25000000000000^3293 ≤ 10728725609071^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311276073 2500000000 10728725609071 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031086419/10000000000 : ℝ), (5411883933/10000000000 : ℝ), (1311276073/2500000000 : ℝ)] ![(1546563677091/12500000000000 : ℝ), (8942517626047/20000000000000 : ℝ), (10728725609071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031086419/10000000000 : ℝ)|^4317 ≤ (1546563677091/12500000000000 : ℝ)^3293
        have hw : |(-2031086419/10000000000 : ℝ)|=(2031086419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411883933/10000000000 : ℝ)|^4317 ≤ (8942517626047/20000000000000 : ℝ)^3293
        have hw : |(5411883933/10000000000 : ℝ)|=(5411883933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311276073/2500000000 : ℝ)|^4317 ≤ (10728725609071/25000000000000 : ℝ)^3293
        have hw : |(1311276073/2500000000 : ℝ)|=(1311276073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s8_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674361031/5000000000 : ℝ)*x 0 + (-2116049551/10000000000 : ℝ)*x 1 + (2622551889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674361031/5000000000 : ℝ)^4317 ≤ (22014860884721/50000000000000 : ℝ)^3293 := by
    have hnat : (2674361031 : ℕ)^4317*50000000000000^3293 ≤ 22014860884721^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674361031 5000000000 22014860884721 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116049551/10000000000 : ℝ)^4317 ≤ (2611076258907/20000000000000 : ℝ)^3293 := by
    have hnat : (2116049551 : ℕ)^4317*20000000000000^3293 ≤ 2611076258907^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116049551 10000000000 2611076258907 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622551889/5000000000 : ℝ)^4317 ≤ (42914896923037/100000000000000 : ℝ)^3293 := by
    have hnat : (2622551889 : ℕ)^4317*100000000000000^3293 ≤ 42914896923037^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622551889 5000000000 42914896923037 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674361031/5000000000 : ℝ), (-2116049551/10000000000 : ℝ), (2622551889/5000000000 : ℝ)] ![(22014860884721/50000000000000 : ℝ), (2611076258907/20000000000000 : ℝ), (42914896923037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674361031/5000000000 : ℝ)|^4317 ≤ (22014860884721/50000000000000 : ℝ)^3293
        have hw : |(2674361031/5000000000 : ℝ)|=(2674361031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116049551/10000000000 : ℝ)|^4317 ≤ (2611076258907/20000000000000 : ℝ)^3293
        have hw : |(-2116049551/10000000000 : ℝ)|=(2116049551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622551889/5000000000 : ℝ)|^4317 ≤ (42914896923037/100000000000000 : ℝ)^3293
        have hw : |(2622551889/5000000000 : ℝ)|=(2622551889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s8_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534872201/1000000000 : ℝ)*x 0 + (5245103761/10000000000 : ℝ)*x 1 + (-2116049643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534872201/1000000000 : ℝ)^4317 ≤ (22014860604139/50000000000000 : ℝ)^3293 := by
    have hnat : (534872201 : ℕ)^4317*50000000000000^3293 ≤ 22014860604139^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534872201 1000000000 22014860604139 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245103761/10000000000 : ℝ)^4317 ≤ (10728724185173/25000000000000 : ℝ)^3293 := by
    have hnat : (5245103761 : ℕ)^4317*25000000000000^3293 ≤ 10728724185173^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245103761 10000000000 10728724185173 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116049643/10000000000 : ℝ)^4317 ≤ (13055382038653/100000000000000 : ℝ)^3293 := by
    have hnat : (2116049643 : ℕ)^4317*100000000000000^3293 ≤ 13055382038653^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116049643 10000000000 13055382038653 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534872201/1000000000 : ℝ), (5245103761/10000000000 : ℝ), (-2116049643/10000000000 : ℝ)] ![(22014860604139/50000000000000 : ℝ), (10728724185173/25000000000000 : ℝ), (13055382038653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534872201/1000000000 : ℝ)|^4317 ≤ (22014860604139/50000000000000 : ℝ)^3293
        have hw : |(534872201/1000000000 : ℝ)|=(534872201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245103761/10000000000 : ℝ)|^4317 ≤ (10728724185173/25000000000000 : ℝ)^3293
        have hw : |(5245103761/10000000000 : ℝ)|=(5245103761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2116049643/10000000000 : ℝ)|^4317 ≤ (13055382038653/100000000000000 : ℝ)^3293
        have hw : |(-2116049643/10000000000 : ℝ)|=(2116049643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s8_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135084843/312500000 : ℝ)*x 0 + (207518803/500000000 : ℝ)*x 1 + (4501681341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135084843/312500000 : ℝ)^4317 ≤ (33303548390301/100000000000000 : ℝ)^3293 := by
    have hnat : (135084843 : ℕ)^4317*100000000000000^3293 ≤ 33303548390301^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135084843 312500000 33303548390301 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207518803/500000000 : ℝ)^4317 ≤ (6314760837509/20000000000000 : ℝ)^3293 := by
    have hnat : (207518803 : ℕ)^4317*20000000000000^3293 ≤ 6314760837509^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207518803 500000000 6314760837509 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501681341/10000000000 : ℝ)^4317 ≤ (35122647394301/100000000000000 : ℝ)^3293 := by
    have hnat : (4501681341 : ℕ)^4317*100000000000000^3293 ≤ 35122647394301^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501681341 10000000000 35122647394301 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135084843/312500000 : ℝ), (207518803/500000000 : ℝ), (4501681341/10000000000 : ℝ)] ![(33303548390301/100000000000000 : ℝ), (6314760837509/20000000000000 : ℝ), (35122647394301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135084843/312500000 : ℝ)|^4317 ≤ (33303548390301/100000000000000 : ℝ)^3293
        have hw : |(135084843/312500000 : ℝ)|=(135084843/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207518803/500000000 : ℝ)|^4317 ≤ (6314760837509/20000000000000 : ℝ)^3293
        have hw : |(207518803/500000000 : ℝ)|=(207518803/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501681341/10000000000 : ℝ)|^4317 ≤ (35122647394301/100000000000000 : ℝ)^3293
        have hw : |(4501681341/10000000000 : ℝ)|=(4501681341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s8_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (864548169/2000000000 : ℝ)*x 0 + (112510563/250000000 : ℝ)*x 1 + (4151640779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864548169/2000000000 : ℝ)^4317 ≤ (832595241729/2500000000000 : ℝ)^3293 := by
    have hnat : (864548169 : ℕ)^4317*2500000000000^3293 ≤ 832595241729^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864548169 2000000000 832595241729 2500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112510563/250000000 : ℝ)^4317 ≤ (35109772374439/100000000000000 : ℝ)^3293 := by
    have hnat : (112510563 : ℕ)^4317*100000000000000^3293 ≤ 35109772374439^3293*250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112510563 250000000 35109772374439 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4151640779/10000000000 : ℝ)^4317 ≤ (31586417942721/100000000000000 : ℝ)^3293 := by
    have hnat : (4151640779 : ℕ)^4317*100000000000000^3293 ≤ 31586417942721^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151640779 10000000000 31586417942721 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864548169/2000000000 : ℝ), (112510563/250000000 : ℝ), (4151640779/10000000000 : ℝ)] ![(832595241729/2500000000000 : ℝ), (35109772374439/100000000000000 : ℝ), (31586417942721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864548169/2000000000 : ℝ)|^4317 ≤ (832595241729/2500000000000 : ℝ)^3293
        have hw : |(864548169/2000000000 : ℝ)|=(864548169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112510563/250000000 : ℝ)|^4317 ≤ (35109772374439/100000000000000 : ℝ)^3293
        have hw : |(112510563/250000000 : ℝ)|=(112510563/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4151640779/10000000000 : ℝ)|^4317 ≤ (31586417942721/100000000000000 : ℝ)^3293
        have hw : |(4151640779/10000000000 : ℝ)|=(4151640779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2237/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3679/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (699/6250 : ℝ) ^ (1079/256 : ℝ) ≤ (9772049975787137/100000000000000000000 : ℝ) := by
    have hpowers : (699/6250 : ℝ)^1079 ≤ (9772049975787137/100000000000000000000 : ℝ)^256 := by
      have hnat : (699 : ℕ)^1079*100000000000000000000^256 ≤ 9772049975787137^256*6250^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        699 6250 9772049975787137 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (699/6250 : ℝ)) (X := (9772049975787137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3679/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (485494124074637/1562500000000000000 : ℝ) := by
    have hpowers : (3679/25000 : ℝ)^1079 ≤ (485494124074637/1562500000000000000 : ℝ)^256 := by
      have hnat : (3679 : ℕ)^1079*1562500000000000000^256 ≤ 485494124074637^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 25000 485494124074637 1562500000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/25000 : ℝ)) (X := (485494124074637/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009772049975787137/50000000000000000000 : ℝ) ≤ (10000463662345409/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50009772049975787137/50000000000000000000 : ℝ)^256 ≤ (10000463662345409/10000000000000000 : ℝ)^1079 := by
      have hnat : (50009772049975787137 : ℕ)^256*10000000000000000^1079 ≤ 10000463662345409^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009772049975787137 50000000000000000000 10000463662345409 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000463662345409/10000000000000000 : ℝ)) (X := (50009772049975787137/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008168734783312781/20000000000000000000 : ℝ) ≤ (5000484446349637/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (20008168734783312781/20000000000000000000 : ℝ)^256 ≤ (5000484446349637/5000000000000000 : ℝ)^1079 := by
      have hnat : (20008168734783312781 : ℕ)^256*5000000000000000^1079 ≤ 5000484446349637^1079*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008168734783312781 20000000000000000000 5000484446349637 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000484446349637/5000000000000000 : ℝ)) (X := (20008168734783312781/20000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (781735494124074637/781250000000000000 : ℝ) ≤ (10001474123053139/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (781735494124074637/781250000000000000 : ℝ)^256 ≤ (10001474123053139/10000000000000000 : ℝ)^1079 := by
      have hnat : (781735494124074637 : ℕ)^256*10000000000000000^1079 ≤ 10001474123053139^1079*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781735494124074637 781250000000000000 10001474123053139 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001474123053139/10000000000000000 : ℝ)) (X := (781735494124074637/781250000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9772049975787137/100000000000000000000 : ℝ) ≤ ((8827584165712183067/8830000000000000000 : ℝ)+2*(101046070773/70640000000000 : ℝ)*(699/6250 : ℝ))^(1079/256 : ℝ) := by
    rw [show (8827584165712183067/8830000000000000000 : ℝ)+2*(101046070773/70640000000000 : ℝ)*(699/6250 : ℝ)=(10000463662345409/10000000000000000 : ℝ) by norm_num, show 1+2*(9772049975787137/100000000000000000000 : ℝ)=(50009772049975787137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(485494124074637/1562500000000000000 : ℝ)+(9772049975787137/100000000000000000000 : ℝ) ≤ ((8827584165712183067/8830000000000000000 : ℝ)+(101046070773/70640000000000 : ℝ)*((3679/25000 : ℝ)+(699/6250 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (8827584165712183067/8830000000000000000 : ℝ)+(101046070773/70640000000000 : ℝ)*((3679/25000 : ℝ)+(699/6250 : ℝ))=(5000484446349637/5000000000000000 : ℝ) by norm_num, show 1+(485494124074637/1562500000000000000 : ℝ)+(9772049975787137/100000000000000000000 : ℝ)=(20008168734783312781/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(485494124074637/1562500000000000000 : ℝ) ≤ ((8827584165712183067/8830000000000000000 : ℝ)+2*(101046070773/70640000000000 : ℝ)*(3679/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (8827584165712183067/8830000000000000000 : ℝ)+2*(101046070773/70640000000000 : ℝ)*(3679/25000 : ℝ)=(10001474123053139/10000000000000000 : ℝ) by norm_num, show 1+2*(485494124074637/1562500000000000000 : ℝ)=(781735494124074637/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8827584165712183067/8830000000000000000 : ℝ)*(X 1 0+X 2 0)+(101046070773/70640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (8827584165712183067/8830000000000000000 : ℝ)) (alpha := (101046070773/70640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8827584165712183067/8830000000000000000 : ℝ)*(X 0 1+X 2 1)+(101046070773/70640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (8827584165712183067/8830000000000000000 : ℝ)) (alpha := (101046070773/70640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8827584165712183067/8830000000000000000 : ℝ)*(X 0 2+X 1 2)+(101046070773/70640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (8827584165712183067/8830000000000000000 : ℝ)) (alpha := (101046070773/70640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2031086419/10000000000 : ℝ)*X 0 0+(5411883933/10000000000 : ℝ)*X 0 1+(1311276073/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674361031/5000000000 : ℝ)*X 1 0+(-2116049551/10000000000 : ℝ)*X 1 1+(2622551889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534872201/1000000000 : ℝ)*X 2 0+(5245103761/10000000000 : ℝ)*X 2 1+(-2116049643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135084843/312500000 : ℝ)*X 0 0+(207518803/500000000 : ℝ)*X 0 1+(4501681341/10000000000 : ℝ)*X 0 2+(135084843/312500000 : ℝ)*X 1 0+(207518803/500000000 : ℝ)*X 1 1+(4501681341/10000000000 : ℝ)*X 1 2+(135084843/312500000 : ℝ)*X 2 0+(207518803/500000000 : ℝ)*X 2 1+(4501681341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((864548169/2000000000 : ℝ)*X 0 0+(112510563/250000000 : ℝ)*X 0 1+(4151640779/10000000000 : ℝ)*X 0 2+(864548169/2000000000 : ℝ)*X 1 0+(112510563/250000000 : ℝ)*X 1 1+(4151640779/10000000000 : ℝ)*X 1 2+(864548169/2000000000 : ℝ)*X 2 0+(112510563/250000000 : ℝ)*X 2 1+(4151640779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1372290039915416232710952177/441500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (565980817/100000000000000 : ℝ)*(base19) + (518152823/100000000000000 : ℝ)*(base23) + (31508117/50000000000000 : ℝ)*(lower2) + (39073331/100000000000000 : ℝ)*(lower3) + (13722651/20000000000000 : ℝ)*(lower4) + (15036417/10000000000000 : ℝ)*(lower5) + (4421237851041259/100000000000000 : ℝ)*(major0) + (4421237851041259/100000000000000 : ℝ)*(major1) + (4421237851041259/100000000000000 : ℝ)*(major2) + (5995940377160699/100000000000000 : ℝ)*(sp0) + (2997969905589941/50000000000000 : ℝ)*(sp1) + (1498984964751969/25000000000000 : ℝ)*(sp2) + (1423265242468729/50000000000000 : ℝ)*(sp3) + (4736376191/100000000000000 : ℝ)*(sp4) + (56930704426273/2000000000000 : ℝ)*(f.failure) + (5995940377160699/100000000000000 : ℝ)*(f.sum) + (29212548160497/3532000000000000000000000000 : ℝ)*base66 + (14888435412981963647/883000000000000000000000000000000 : ℝ)*base68 + (8413977522345963647/883000000000000000000000000000000 : ℝ)*base70 + (17822929727941963647/883000000000000000000000000000000 : ℝ)*base72 + (10908858658031/3532000000000000000000000000 : ℝ)*base73 + (12490942242049963647/883000000000000000000000000000000 : ℝ)*base76 + (3713114297049963647/883000000000000000000000000000000 : ℝ)*base78 + (17589596403108963647/883000000000000000000000000000000 : ℝ)*base80 + (2387467945661/3532000000000000000000000000 : ℝ)*base82 + (2555721/200000000000000000000 : ℝ)*base89 + (2555721/200000000000000000000 : ℝ)*base91 + (2555721/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1357_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1357_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1357_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1357_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1357_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
