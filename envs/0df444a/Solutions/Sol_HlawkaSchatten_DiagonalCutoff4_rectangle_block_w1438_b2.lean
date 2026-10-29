-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1438_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:35.567977+00:00
-- url     : https://prove2.me/submissions/152fc7b6-e61a-4ef1-840f-96090c4f0d14

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
theorem support_rectangle_w1438_s6_0 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-392770161/2000000000 : ℝ)*x 0 + (1081551419/2000000000 : ℝ)*x 1 + (5247102431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392770161/2000000000 : ℝ)^2199 ≤ (11983089519471/100000000000000 : ℝ)^1687 := by
    have hnat : (392770161 : ℕ)^2199*100000000000000^1687 ≤ 11983089519471^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392770161 2000000000 11983089519471 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081551419/2000000000 : ℝ)^2199 ≤ (8974672231679/20000000000000 : ℝ)^1687 := by
    have hnat : (1081551419 : ℕ)^2199*20000000000000^1687 ≤ 8974672231679^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081551419 2000000000 8974672231679 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247102431/10000000000 : ℝ)^2199 ≤ (43143549309849/100000000000000 : ℝ)^1687 := by
    have hnat : (5247102431 : ℕ)^2199*100000000000000^1687 ≤ 43143549309849^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247102431 10000000000 43143549309849 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392770161/2000000000 : ℝ), (1081551419/2000000000 : ℝ), (5247102431/10000000000 : ℝ)] ![(11983089519471/100000000000000 : ℝ), (8974672231679/20000000000000 : ℝ), (43143549309849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392770161/2000000000 : ℝ)|^2199 ≤ (11983089519471/100000000000000 : ℝ)^1687
        have hw : |(-392770161/2000000000 : ℝ)|=(392770161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081551419/2000000000 : ℝ)|^2199 ≤ (8974672231679/20000000000000 : ℝ)^1687
        have hw : |(1081551419/2000000000 : ℝ)|=(1081551419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247102431/10000000000 : ℝ)|^2199 ≤ (43143549309849/100000000000000 : ℝ)^1687
        have hw : |(5247102431/10000000000 : ℝ)|=(5247102431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_1 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347136847/10000000000 : ℝ)*x 0 + (-2045636517/10000000000 : ℝ)*x 1 + (163971951/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347136847/10000000000 : ℝ)^2199 ≤ (4421878837239/10000000000000 : ℝ)^1687 := by
    have hnat : (5347136847 : ℕ)^2199*10000000000000^1687 ≤ 4421878837239^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347136847 10000000000 4421878837239 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045636517/10000000000 : ℝ)^2199 ≤ (12637662298803/100000000000000 : ℝ)^1687 := by
    have hnat : (2045636517 : ℕ)^2199*100000000000000^1687 ≤ 12637662298803^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045636517 10000000000 12637662298803 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163971951/312500000 : ℝ)^2199 ≤ (43143549320567/100000000000000 : ℝ)^1687 := by
    have hnat : (163971951 : ℕ)^2199*100000000000000^1687 ≤ 43143549320567^1687*312500000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163971951 312500000 43143549320567 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347136847/10000000000 : ℝ), (-2045636517/10000000000 : ℝ), (163971951/312500000 : ℝ)] ![(4421878837239/10000000000000 : ℝ), (12637662298803/100000000000000 : ℝ), (43143549320567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347136847/10000000000 : ℝ)|^2199 ≤ (4421878837239/10000000000000 : ℝ)^1687
        have hw : |(5347136847/10000000000 : ℝ)|=(5347136847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045636517/10000000000 : ℝ)|^2199 ≤ (12637662298803/100000000000000 : ℝ)^1687
        have hw : |(-2045636517/10000000000 : ℝ)|=(2045636517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163971951/312500000 : ℝ)|^2199 ≤ (43143549320567/100000000000000 : ℝ)^1687
        have hw : |(163971951/312500000 : ℝ)|=(163971951/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_2 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347136847/10000000000 : ℝ)*x 0 + (5247102431/10000000000 : ℝ)*x 1 + (-1022818259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347136847/10000000000 : ℝ)^2199 ≤ (4421878837239/10000000000000 : ℝ)^1687 := by
    have hnat : (5347136847 : ℕ)^2199*10000000000000^1687 ≤ 4421878837239^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347136847 10000000000 4421878837239 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247102431/10000000000 : ℝ)^2199 ≤ (43143549309849/100000000000000 : ℝ)^1687 := by
    have hnat : (5247102431 : ℕ)^2199*100000000000000^1687 ≤ 43143549309849^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247102431 10000000000 43143549309849 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022818259/5000000000 : ℝ)^2199 ≤ (1579707788357/12500000000000 : ℝ)^1687 := by
    have hnat : (1022818259 : ℕ)^2199*12500000000000^1687 ≤ 1579707788357^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022818259 5000000000 1579707788357 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347136847/10000000000 : ℝ), (5247102431/10000000000 : ℝ), (-1022818259/5000000000 : ℝ)] ![(4421878837239/10000000000000 : ℝ), (43143549309849/100000000000000 : ℝ), (1579707788357/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347136847/10000000000 : ℝ)|^2199 ≤ (4421878837239/10000000000000 : ℝ)^1687
        have hw : |(5347136847/10000000000 : ℝ)|=(5347136847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247102431/10000000000 : ℝ)|^2199 ≤ (43143549309849/100000000000000 : ℝ)^1687
        have hw : |(5247102431/10000000000 : ℝ)|=(5247102431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022818259/5000000000 : ℝ)|^2199 ≤ (1579707788357/12500000000000 : ℝ)^1687
        have hw : |(-1022818259/5000000000 : ℝ)|=(1022818259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_3 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302127799/10000000000 : ℝ)*x 0 + (4130945101/10000000000 : ℝ)*x 1 + (2239820619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302127799/10000000000 : ℝ)^2199 ≤ (3330482594487/10000000000000 : ℝ)^1687 := by
    have hnat : (4302127799 : ℕ)^2199*10000000000000^1687 ≤ 3330482594487^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302127799 10000000000 3330482594487 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130945101/10000000000 : ℝ)^2199 ≤ (31587950409839/100000000000000 : ℝ)^1687 := by
    have hnat : (4130945101 : ℕ)^2199*100000000000000^1687 ≤ 31587950409839^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130945101 10000000000 31587950409839 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239820619/5000000000 : ℝ)^2199 ≤ (4388402954359/12500000000000 : ℝ)^1687 := by
    have hnat : (2239820619 : ℕ)^2199*12500000000000^1687 ≤ 4388402954359^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239820619 5000000000 4388402954359 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302127799/10000000000 : ℝ), (4130945101/10000000000 : ℝ), (2239820619/5000000000 : ℝ)] ![(3330482594487/10000000000000 : ℝ), (31587950409839/100000000000000 : ℝ), (4388402954359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302127799/10000000000 : ℝ)|^2199 ≤ (3330482594487/10000000000000 : ℝ)^1687
        have hw : |(4302127799/10000000000 : ℝ)|=(4302127799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130945101/10000000000 : ℝ)|^2199 ≤ (31587950409839/100000000000000 : ℝ)^1687
        have hw : |(4130945101/10000000000 : ℝ)|=(4130945101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239820619/5000000000 : ℝ)|^2199 ≤ (4388402954359/12500000000000 : ℝ)^1687
        have hw : |(2239820619/5000000000 : ℝ)|=(2239820619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_4 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-490965461/2500000000 : ℝ)*x 0 + (41981461/80000000 : ℝ)*x 1 + (5407174051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490965461/2500000000 : ℝ)^2199 ≤ (5991588660347/50000000000000 : ℝ)^1687 := by
    have hnat : (490965461 : ℕ)^2199*50000000000000^1687 ≤ 5991588660347^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490965461 2500000000 5991588660347 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41981461/80000000 : ℝ)^2199 ≤ (21574883914637/50000000000000 : ℝ)^1687 := by
    have hnat : (41981461 : ℕ)^2199*50000000000000^1687 ≤ 21574883914637^1687*80000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41981461 80000000 21574883914637 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407174051/10000000000 : ℝ)^2199 ≤ (11216763710353/25000000000000 : ℝ)^1687 := by
    have hnat : (5407174051 : ℕ)^2199*25000000000000^1687 ≤ 11216763710353^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407174051 10000000000 11216763710353 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490965461/2500000000 : ℝ), (41981461/80000000 : ℝ), (5407174051/10000000000 : ℝ)] ![(5991588660347/50000000000000 : ℝ), (21574883914637/50000000000000 : ℝ), (11216763710353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490965461/2500000000 : ℝ)|^2199 ≤ (5991588660347/50000000000000 : ℝ)^1687
        have hw : |(-490965461/2500000000 : ℝ)|=(490965461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41981461/80000000 : ℝ)|^2199 ≤ (21574883914637/50000000000000 : ℝ)^1687
        have hw : |(41981461/80000000 : ℝ)|=(41981461/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407174051/10000000000 : ℝ)|^2199 ≤ (11216763710353/25000000000000 : ℝ)^1687
        have hw : |(5407174051/10000000000 : ℝ)|=(5407174051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_5 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326333623/2500000000 : ℝ)*x 0 + (-47139119/250000000 : ℝ)*x 1 + (2703587051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326333623/2500000000 : ℝ)^2199 ≤ (43768718466151/100000000000000 : ℝ)^1687 := by
    have hnat : (1326333623 : ℕ)^2199*100000000000000^1687 ≤ 43768718466151^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326333623 2500000000 43768718466151 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47139119/250000000 : ℝ)^2199 ≤ (1136422612179/10000000000000 : ℝ)^1687 := by
    have hnat : (47139119 : ℕ)^2199*10000000000000^1687 ≤ 1136422612179^1687*250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47139119 250000000 1136422612179 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703587051/5000000000 : ℝ)^2199 ≤ (11216763848257/25000000000000 : ℝ)^1687 := by
    have hnat : (2703587051 : ℕ)^2199*25000000000000^1687 ≤ 11216763848257^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703587051 5000000000 11216763848257 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326333623/2500000000 : ℝ), (-47139119/250000000 : ℝ), (2703587051/5000000000 : ℝ)] ![(43768718466151/100000000000000 : ℝ), (1136422612179/10000000000000 : ℝ), (11216763848257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326333623/2500000000 : ℝ)|^2199 ≤ (43768718466151/100000000000000 : ℝ)^1687
        have hw : |(1326333623/2500000000 : ℝ)|=(1326333623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47139119/250000000 : ℝ)|^2199 ≤ (1136422612179/10000000000000 : ℝ)^1687
        have hw : |(-47139119/250000000 : ℝ)|=(47139119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703587051/5000000000 : ℝ)|^2199 ≤ (11216763848257/25000000000000 : ℝ)^1687
        have hw : |(2703587051/5000000000 : ℝ)|=(2703587051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_6 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305333743/10000000000 : ℝ)*x 0 + (337948423/625000000 : ℝ)*x 1 + (-471391217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305333743/10000000000 : ℝ)^2199 ≤ (2735544400723/6250000000000 : ℝ)^1687 := by
    have hnat : (5305333743 : ℕ)^2199*6250000000000^1687 ≤ 2735544400723^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305333743 10000000000 2735544400723 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337948423/625000000 : ℝ)^2199 ≤ (2804191412281/6250000000000 : ℝ)^1687 := by
    have hnat : (337948423 : ℕ)^2199*6250000000000^1687 ≤ 2804191412281^1687*625000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337948423 625000000 2804191412281 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471391217/2500000000 : ℝ)^2199 ≤ (2841056742563/25000000000000 : ℝ)^1687 := by
    have hnat : (471391217 : ℕ)^2199*25000000000000^1687 ≤ 2841056742563^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471391217 2500000000 2841056742563 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305333743/10000000000 : ℝ), (337948423/625000000 : ℝ), (-471391217/2500000000 : ℝ)] ![(2735544400723/6250000000000 : ℝ), (2804191412281/6250000000000 : ℝ), (2841056742563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305333743/10000000000 : ℝ)|^2199 ≤ (2735544400723/6250000000000 : ℝ)^1687
        have hw : |(5305333743/10000000000 : ℝ)|=(5305333743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337948423/625000000 : ℝ)|^2199 ≤ (2804191412281/6250000000000 : ℝ)^1687
        have hw : |(337948423/625000000 : ℝ)|=(337948423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471391217/2500000000 : ℝ)|^2199 ≤ (2841056742563/25000000000000 : ℝ)^1687
        have hw : |(-471391217/2500000000 : ℝ)|=(471391217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s6_7 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302151879/10000000000 : ℝ)*x 0 + (4478382731/10000000000 : ℝ)*x 1 + (4132210451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302151879/10000000000 : ℝ)^2199 ≤ (6661013787249/20000000000000 : ℝ)^1687 := by
    have hnat : (4302151879 : ℕ)^2199*20000000000000^1687 ≤ 6661013787249^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302151879 10000000000 6661013787249 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478382731/10000000000 : ℝ)^2199 ≤ (35094367793129/100000000000000 : ℝ)^1687 := by
    have hnat : (4478382731 : ℕ)^2199*100000000000000^1687 ≤ 35094367793129^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478382731 10000000000 35094367793129 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132210451/10000000000 : ℝ)^2199 ≤ (1975035203367/6250000000000 : ℝ)^1687 := by
    have hnat : (4132210451 : ℕ)^2199*6250000000000^1687 ≤ 1975035203367^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132210451 10000000000 1975035203367 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302151879/10000000000 : ℝ), (4478382731/10000000000 : ℝ), (4132210451/10000000000 : ℝ)] ![(6661013787249/20000000000000 : ℝ), (35094367793129/100000000000000 : ℝ), (1975035203367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302151879/10000000000 : ℝ)|^2199 ≤ (6661013787249/20000000000000 : ℝ)^1687
        have hw : |(4302151879/10000000000 : ℝ)|=(4302151879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478382731/10000000000 : ℝ)|^2199 ≤ (35094367793129/100000000000000 : ℝ)^1687
        have hw : |(4478382731/10000000000 : ℝ)|=(4478382731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132210451/10000000000 : ℝ)|^2199 ≤ (1975035203367/6250000000000 : ℝ)^1687
        have hw : |(4132210451/10000000000 : ℝ)|=(4132210451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1438_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/20000 : ℝ) ^ (4397/1024 : ℝ) ≤ (8770517963692781/100000000000000000000 : ℝ) := by
    have hpowers : (2271/20000 : ℝ)^4397 ≤ (8770517963692781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2271 : ℕ)^4397*100000000000000000000^1024 ≤ 8770517963692781^1024*20000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 20000 8770517963692781 100000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/20000 : ℝ)) (X := (8770517963692781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (4397/1024 : ℝ) ≤ (27085313856865353/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^4397 ≤ (27085313856865353/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2953 : ℕ)^4397*100000000000000000000^1024 ≤ 27085313856865353^1024*20000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 27085313856865353 100000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (27085313856865353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008770517963692781/50000000000000000000 : ℝ) ≤ (312512764962213/312500000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50008770517963692781/50000000000000000000 : ℝ)^1024 ≤ (312512764962213/312500000000000 : ℝ)^4397 := by
      have hnat : (50008770517963692781 : ℕ)^1024*312500000000000^4397 ≤ 312512764962213^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008770517963692781 50000000000000000000 312512764962213 312500000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312512764962213/312500000000000 : ℝ)) (X := (50008770517963692781/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017927915910279067/50000000000000000000 : ℝ) ≤ (1000083491751963/1000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50017927915910279067/50000000000000000000 : ℝ)^1024 ≤ (1000083491751963/1000000000000000 : ℝ)^4397 := by
      have hnat : (50017927915910279067 : ℕ)^1024*1000000000000000^4397 ≤ 1000083491751963^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017927915910279067 50000000000000000000 1000083491751963 1000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000083491751963/1000000000000000 : ℝ)) (X := (50017927915910279067/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027085313856865353/50000000000000000000 : ℝ) ≤ (2500315339062111/2500000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50027085313856865353/50000000000000000000 : ℝ)^1024 ≤ (2500315339062111/2500000000000000 : ℝ)^4397 := by
      have hnat : (50027085313856865353 : ℕ)^1024*2500000000000000^4397 ≤ 2500315339062111^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027085313856865353 50000000000000000000 2500315339062111 2500000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500315339062111/2500000000000000 : ℝ)) (X := (50027085313856865353/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8770517963692781/100000000000000000000 : ℝ) ≤ ((1704585424457265831/1705000000000000000 : ℝ)+2*(213219364407/170500000000000 : ℝ)*(2271/20000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (1704585424457265831/1705000000000000000 : ℝ)+2*(213219364407/170500000000000 : ℝ)*(2271/20000 : ℝ)=(312512764962213/312500000000000 : ℝ) by norm_num, show 1+2*(8770517963692781/100000000000000000000 : ℝ)=(50008770517963692781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27085313856865353/100000000000000000000 : ℝ)+(8770517963692781/100000000000000000000 : ℝ) ≤ ((1704585424457265831/1705000000000000000 : ℝ)+(213219364407/170500000000000 : ℝ)*((2953/20000 : ℝ)+(2271/20000 : ℝ)))^(4397/1024 : ℝ) := by
    rw [show (1704585424457265831/1705000000000000000 : ℝ)+(213219364407/170500000000000 : ℝ)*((2953/20000 : ℝ)+(2271/20000 : ℝ))=(1000083491751963/1000000000000000 : ℝ) by norm_num, show 1+(27085313856865353/100000000000000000000 : ℝ)+(8770517963692781/100000000000000000000 : ℝ)=(50017927915910279067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27085313856865353/100000000000000000000 : ℝ) ≤ ((1704585424457265831/1705000000000000000 : ℝ)+2*(213219364407/170500000000000 : ℝ)*(2953/20000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (1704585424457265831/1705000000000000000 : ℝ)+2*(213219364407/170500000000000 : ℝ)*(2953/20000 : ℝ)=(2500315339062111/2500000000000000 : ℝ) by norm_num, show 1+2*(27085313856865353/100000000000000000000 : ℝ)=(50027085313856865353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1704585424457265831/1705000000000000000 : ℝ)*(X 1 0+X 2 0)+(213219364407/170500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (1704585424457265831/1705000000000000000 : ℝ)) (alpha := (213219364407/170500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1704585424457265831/1705000000000000000 : ℝ)*(X 0 1+X 2 1)+(213219364407/170500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (1704585424457265831/1705000000000000000 : ℝ)) (alpha := (213219364407/170500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1704585424457265831/1705000000000000000 : ℝ)*(X 0 2+X 1 2)+(213219364407/170500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (1704585424457265831/1705000000000000000 : ℝ)) (alpha := (213219364407/170500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-392770161/2000000000 : ℝ)*X 0 0+(1081551419/2000000000 : ℝ)*X 0 1+(5247102431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347136847/10000000000 : ℝ)*X 1 0+(-2045636517/10000000000 : ℝ)*X 1 1+(163971951/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347136847/10000000000 : ℝ)*X 2 0+(5247102431/10000000000 : ℝ)*X 2 1+(-1022818259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302127799/10000000000 : ℝ)*X 0 0+(4130945101/10000000000 : ℝ)*X 0 1+(2239820619/5000000000 : ℝ)*X 0 2+(4302127799/10000000000 : ℝ)*X 1 0+(4130945101/10000000000 : ℝ)*X 1 1+(2239820619/5000000000 : ℝ)*X 1 2+(4302127799/10000000000 : ℝ)*X 2 0+(4130945101/10000000000 : ℝ)*X 2 1+(2239820619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-490965461/2500000000 : ℝ)*X 0 0+(41981461/80000000 : ℝ)*X 0 1+(5407174051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326333623/2500000000 : ℝ)*X 1 0+(-47139119/250000000 : ℝ)*X 1 1+(2703587051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305333743/10000000000 : ℝ)*X 2 0+(337948423/625000000 : ℝ)*X 2 1+(-471391217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302151879/10000000000 : ℝ)*X 0 0+(4478382731/10000000000 : ℝ)*X 0 1+(4132210451/10000000000 : ℝ)*X 0 2+(4302151879/10000000000 : ℝ)*X 1 0+(4478382731/10000000000 : ℝ)*X 1 1+(4132210451/10000000000 : ℝ)*X 1 2+(4302151879/10000000000 : ℝ)*X 2 0+(4478382731/10000000000 : ℝ)*X 2 1+(4132210451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (408634242053345765353651209/42625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1737894043/100000000000000 : ℝ)*(base19) + (323943231/20000000000000 : ℝ)*(base23) + (31595667/50000000000000 : ℝ)*(lower2) + (47907977/20000000000000 : ℝ)*(upper3) + (152236331/100000000000000 : ℝ)*(upper5) + (4546233912291613/100000000000000 : ℝ)*(major0) + (4546233912291613/100000000000000 : ℝ)*(major1) + (2273116956145807/50000000000000 : ℝ)*(major2) + (3112284853125151/50000000000000 : ℝ)*(sp0) + (24898418579209/400000000000 : ℝ)*(sp1) + (6224604762980137/100000000000000 : ℝ)*(sp2) + (1433921408445723/50000000000000 : ℝ)*(sp3) + (3667644599/10000000000000 : ℝ)*(sp4) + (18305437913/100000000000000 : ℝ)*(sp7) + (1433930561164679/50000000000000 : ℝ)*(f.failure) + (1556151595674073/25000000000000 : ℝ)*(f.sum) + (34767774446161/17050000000000000000000000000 : ℝ)*base66 + (163187873928431327/15500000000000000000000000000000 : ℝ)*base68 + (367985660091725617/85250000000000000000000000000000 : ℝ)*base69 + (187166354429431327/15500000000000000000000000000000 : ℝ)*base72 + (7858487458439/17050000000000000000000000000 : ℝ)*base73 + (193332935075274383/85250000000000000000000000000000 : ℝ)*base76 + (1051312632642314597/170500000000000000000000000000000 : ℝ)*base78 + (211053778350314597/170500000000000000000000000000000 : ℝ)*base80 + (1988072306317/4262500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (24950537/5000000000000000000000 : ℝ)*base89 + (24950537/5000000000000000000000 : ℝ)*base91 + (25049463/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71251112053632587736047373/5328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1468805607/100000000000000 : ℝ)*(base19) + (84521207/10000000000000 : ℝ)*(base23) + (434938741/100000000000000 : ℝ)*(lower1) + (33954313/12500000000000 : ℝ)*(upper3) + (122691571/100000000000000 : ℝ)*(lower4) + (23628231/50000000000000 : ℝ)*(upper5) + (572412881495911/12500000000000 : ℝ)*(major0) + (572412881495911/12500000000000 : ℝ)*(major1) + (572412881495911/12500000000000 : ℝ)*(major2) + (3847900349/100000000000000 : ℝ)*(sp2) + (6269883818638247/100000000000000 : ℝ)*(sp4) + (19593382343227/312500000000 : ℝ)*(sp5) + (1567469781381457/25000000000000 : ℝ)*(sp6) + (144436091977077/5000000000000 : ℝ)*(sp7) + (144436091977077/5000000000000 : ℝ)*(f.failure) + (6269883818638247/100000000000000 : ℝ)*(f.sum) + (4255014658573/1065625000000000000000000000 : ℝ)*base66 + (1566537940786650459/21312500000000000000000000000000 : ℝ)*base68 + (36708767443025459/21312500000000000000000000000000 : ℝ)*base70 + (3232215705344462959/21312500000000000000000000000000 : ℝ)*base72 + (3586576661179/2131250000000000000000000000 : ℝ)*base73 + (1223980416999462959/21312500000000000000000000000000 : ℝ)*base76 + (130703811523849541/21312500000000000000000000000000 : ℝ)*base77 + (233125597053400459/21312500000000000000000000000000 : ℝ)*base80 + (9802251708567/4262500000000000000000000000 : ℝ)*base82 + (1740731/500000000000000000000 : ℝ)*base89 + (1740731/500000000000000000000 : ℝ)*base91 + (1740731/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1438_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1438_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1438_s7_0 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1963853137/10000000000 : ℝ)*x 0 + (1351933909/2500000000 : ℝ)*x 1 + (5247122357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963853137/10000000000 : ℝ)^2199 ≤ (2995777016889/25000000000000 : ℝ)^1687 := by
    have hnat : (1963853137 : ℕ)^2199*25000000000000^1687 ≤ 2995777016889^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963853137 10000000000 2995777016889 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351933909/2500000000 : ℝ)^2199 ≤ (44873129050031/100000000000000 : ℝ)^1687 := by
    have hnat : (1351933909 : ℕ)^2199*100000000000000^1687 ≤ 44873129050031^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351933909 2500000000 44873129050031 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247122357/10000000000 : ℝ)^2199 ≤ (21571881436631/50000000000000 : ℝ)^1687 := by
    have hnat : (5247122357 : ℕ)^2199*50000000000000^1687 ≤ 21571881436631^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247122357 10000000000 21571881436631 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1963853137/10000000000 : ℝ), (1351933909/2500000000 : ℝ), (5247122357/10000000000 : ℝ)] ![(2995777016889/25000000000000 : ℝ), (44873129050031/100000000000000 : ℝ), (21571881436631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1963853137/10000000000 : ℝ)|^2199 ≤ (2995777016889/25000000000000 : ℝ)^1687
        have hw : |(-1963853137/10000000000 : ℝ)|=(1963853137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351933909/2500000000 : ℝ)|^2199 ≤ (44873129050031/100000000000000 : ℝ)^1687
        have hw : |(1351933909/2500000000 : ℝ)|=(1351933909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247122357/10000000000 : ℝ)|^2199 ≤ (21571881436631/50000000000000 : ℝ)^1687
        have hw : |(5247122357/10000000000 : ℝ)|=(5247122357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_1 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069426319/2000000000 : ℝ)*x 0 + (-2045617359/10000000000 : ℝ)*x 1 + (1311780527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069426319/2000000000 : ℝ)^2199 ≤ (22109365879423/50000000000000 : ℝ)^1687 := by
    have hnat : (1069426319 : ℕ)^2199*50000000000000^1687 ≤ 22109365879423^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069426319 2000000000 22109365879423 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045617359/10000000000 : ℝ)^2199 ≤ (12637508022943/100000000000000 : ℝ)^1687 := by
    have hnat : (2045617359 : ℕ)^2199*100000000000000^1687 ≤ 12637508022943^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045617359 10000000000 12637508022943 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311780527/2500000000 : ℝ)^2199 ≤ (43143760204521/100000000000000 : ℝ)^1687 := by
    have hnat : (1311780527 : ℕ)^2199*100000000000000^1687 ≤ 43143760204521^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311780527 2500000000 43143760204521 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069426319/2000000000 : ℝ), (-2045617359/10000000000 : ℝ), (1311780527/2500000000 : ℝ)] ![(22109365879423/50000000000000 : ℝ), (12637508022943/100000000000000 : ℝ), (43143760204521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069426319/2000000000 : ℝ)|^2199 ≤ (22109365879423/50000000000000 : ℝ)^1687
        have hw : |(1069426319/2000000000 : ℝ)|=(1069426319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045617359/10000000000 : ℝ)|^2199 ≤ (12637508022943/100000000000000 : ℝ)^1687
        have hw : |(-2045617359/10000000000 : ℝ)|=(2045617359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311780527/2500000000 : ℝ)|^2199 ≤ (43143760204521/100000000000000 : ℝ)^1687
        have hw : |(1311780527/2500000000 : ℝ)|=(1311780527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_2 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336782831/2500000000 : ℝ)*x 0 + (1049424509/2000000000 : ℝ)*x 1 + (-2045617139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336782831/2500000000 : ℝ)^2199 ≤ (22109364418811/50000000000000 : ℝ)^1687 := by
    have hnat : (1336782831 : ℕ)^2199*50000000000000^1687 ≤ 22109364418811^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336782831 2500000000 22109364418811 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049424509/2000000000 : ℝ)^2199 ≤ (21571882444107/50000000000000 : ℝ)^1687 := by
    have hnat : (1049424509 : ℕ)^2199*50000000000000^1687 ≤ 21571882444107^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049424509 2000000000 21571882444107 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045617139/10000000000 : ℝ)^2199 ≤ (6318753125663/50000000000000 : ℝ)^1687 := by
    have hnat : (2045617139 : ℕ)^2199*50000000000000^1687 ≤ 6318753125663^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045617139 10000000000 6318753125663 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336782831/2500000000 : ℝ), (1049424509/2000000000 : ℝ), (-2045617139/10000000000 : ℝ)] ![(22109364418811/50000000000000 : ℝ), (21571882444107/50000000000000 : ℝ), (6318753125663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336782831/2500000000 : ℝ)|^2199 ≤ (22109364418811/50000000000000 : ℝ)^1687
        have hw : |(1336782831/2500000000 : ℝ)|=(1336782831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049424509/2000000000 : ℝ)|^2199 ≤ (21571882444107/50000000000000 : ℝ)^1687
        have hw : |(1049424509/2000000000 : ℝ)|=(1049424509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045617139/10000000000 : ℝ)|^2199 ≤ (6318753125663/50000000000000 : ℝ)^1687
        have hw : |(-2045617139/10000000000 : ℝ)|=(2045617139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_3 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4201298/9765625 : ℝ)*x 0 + (1032747467/2500000000 : ℝ)*x 1 + (4479596221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201298/9765625 : ℝ)^2199 ≤ (33304839597987/100000000000000 : ℝ)^1687 := by
    have hnat : (4201298 : ℕ)^2199*100000000000000^1687 ≤ 33304839597987^1687*9765625^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201298 9765625 33304839597987 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032747467/2500000000 : ℝ)^2199 ≤ (31588396621461/100000000000000 : ℝ)^1687 := by
    have hnat : (1032747467 : ℕ)^2199*100000000000000^1687 ≤ 31588396621461^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032747467 2500000000 31588396621461 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479596221/10000000000 : ℝ)^2199 ≤ (35106763760417/100000000000000 : ℝ)^1687 := by
    have hnat : (4479596221 : ℕ)^2199*100000000000000^1687 ≤ 35106763760417^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479596221 10000000000 35106763760417 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201298/9765625 : ℝ), (1032747467/2500000000 : ℝ), (4479596221/10000000000 : ℝ)] ![(33304839597987/100000000000000 : ℝ), (31588396621461/100000000000000 : ℝ), (35106763760417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201298/9765625 : ℝ)|^2199 ≤ (33304839597987/100000000000000 : ℝ)^1687
        have hw : |(4201298/9765625 : ℝ)|=(4201298/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032747467/2500000000 : ℝ)|^2199 ≤ (31588396621461/100000000000000 : ℝ)^1687
        have hw : |(1032747467/2500000000 : ℝ)|=(1032747467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479596221/10000000000 : ℝ)|^2199 ≤ (35106763760417/100000000000000 : ℝ)^1687
        have hw : |(4479596221/10000000000 : ℝ)|=(4479596221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_4 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1963864011/10000000000 : ℝ)*x 0 + (5124709/9765625 : ℝ)*x 1 + (5407153241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963864011/10000000000 : ℝ)^2199 ≤ (2995798639111/25000000000000 : ℝ)^1687 := by
    have hnat : (1963864011 : ℕ)^2199*25000000000000^1687 ≤ 2995798639111^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963864011 10000000000 2995798639111 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124709/9765625 : ℝ)^2199 ≤ (2157498783281/5000000000000 : ℝ)^1687 := by
    have hnat : (5124709 : ℕ)^2199*5000000000000^1687 ≤ 2157498783281^1687*9765625^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124709 9765625 2157498783281 5000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407153241/10000000000 : ℝ)^2199 ≤ (4486682976023/10000000000000 : ℝ)^1687 := by
    have hnat : (5407153241 : ℕ)^2199*10000000000000^1687 ≤ 4486682976023^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407153241 10000000000 4486682976023 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1963864011/10000000000 : ℝ), (5124709/9765625 : ℝ), (5407153241/10000000000 : ℝ)] ![(2995798639111/25000000000000 : ℝ), (2157498783281/5000000000000 : ℝ), (4486682976023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1963864011/10000000000 : ℝ)|^2199 ≤ (2995798639111/25000000000000 : ℝ)^1687
        have hw : |(-1963864011/10000000000 : ℝ)|=(1963864011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124709/9765625 : ℝ)|^2199 ≤ (2157498783281/5000000000000 : ℝ)^1687
        have hw : |(5124709/9765625 : ℝ)|=(5124709/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407153241/10000000000 : ℝ)|^2199 ≤ (4486682976023/10000000000000 : ℝ)^1687
        have hw : |(5407153241/10000000000 : ℝ)|=(5407153241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_5 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305339743/10000000000 : ℝ)*x 0 + (-377117259/2000000000 : ℝ)*x 1 + (5407153239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305339743/10000000000 : ℝ)^2199 ≤ (21884387467133/50000000000000 : ℝ)^1687 := by
    have hnat : (5305339743 : ℕ)^2199*50000000000000^1687 ≤ 21884387467133^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305339743 10000000000 21884387467133 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377117259/2000000000 : ℝ)^2199 ≤ (2841098825951/25000000000000 : ℝ)^1687 := by
    have hnat : (377117259 : ℕ)^2199*25000000000000^1687 ≤ 2841098825951^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377117259 2000000000 2841098825951 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407153239/10000000000 : ℝ)^2199 ≤ (22433414869299/50000000000000 : ℝ)^1687 := by
    have hnat : (5407153239 : ℕ)^2199*50000000000000^1687 ≤ 22433414869299^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407153239 10000000000 22433414869299 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305339743/10000000000 : ℝ), (-377117259/2000000000 : ℝ), (5407153239/10000000000 : ℝ)] ![(21884387467133/50000000000000 : ℝ), (2841098825951/25000000000000 : ℝ), (22433414869299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305339743/10000000000 : ℝ)|^2199 ≤ (21884387467133/50000000000000 : ℝ)^1687
        have hw : |(5305339743/10000000000 : ℝ)|=(5305339743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377117259/2000000000 : ℝ)|^2199 ≤ (2841098825951/25000000000000 : ℝ)^1687
        have hw : |(-377117259/2000000000 : ℝ)|=(377117259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407153239/10000000000 : ℝ)|^2199 ≤ (22433414869299/50000000000000 : ℝ)^1687
        have hw : |(5407153239/10000000000 : ℝ)|=(5407153239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_6 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305339713/10000000000 : ℝ)*x 0 + (1081430643/2000000000 : ℝ)*x 1 + (-188558637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305339713/10000000000 : ℝ)^2199 ≤ (10942193652913/25000000000000 : ℝ)^1687 := by
    have hnat : (5305339713 : ℕ)^2199*25000000000000^1687 ≤ 10942193652913^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305339713 10000000000 10942193652913 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081430643/2000000000 : ℝ)^2199 ≤ (22433414739507/50000000000000 : ℝ)^1687 := by
    have hnat : (1081430643 : ℕ)^2199*50000000000000^1687 ≤ 22433414739507^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081430643 2000000000 22433414739507 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188558637/1000000000 : ℝ)^2199 ≤ (2272879178603/20000000000000 : ℝ)^1687 := by
    have hnat : (188558637 : ℕ)^2199*20000000000000^1687 ≤ 2272879178603^1687*1000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188558637 1000000000 2272879178603 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305339713/10000000000 : ℝ), (1081430643/2000000000 : ℝ), (-188558637/1000000000 : ℝ)] ![(10942193652913/25000000000000 : ℝ), (22433414739507/50000000000000 : ℝ), (2272879178603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305339713/10000000000 : ℝ)|^2199 ≤ (10942193652913/25000000000000 : ℝ)^1687
        have hw : |(5305339713/10000000000 : ℝ)|=(5305339713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081430643/2000000000 : ℝ)|^2199 ≤ (22433414739507/50000000000000 : ℝ)^1687
        have hw : |(1081430643/2000000000 : ℝ)|=(1081430643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188558637/1000000000 : ℝ)|^2199 ≤ (2272879178603/20000000000000 : ℝ)^1687
        have hw : |(-188558637/1000000000 : ℝ)|=(188558637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s7_7 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302153697/10000000000 : ℝ)*x 0 + (895667637/2000000000 : ℝ)*x 1 + (2066127129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302153697/10000000000 : ℝ)^2199 ≤ (33305087281707/100000000000000 : ℝ)^1687 := by
    have hnat : (4302153697 : ℕ)^2199*100000000000000^1687 ≤ 33305087281707^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302153697 10000000000 33305087281707 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895667637/2000000000 : ℝ)^2199 ≤ (35093912769007/100000000000000 : ℝ)^1687 := by
    have hnat : (895667637 : ℕ)^2199*100000000000000^1687 ≤ 35093912769007^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895667637 2000000000 35093912769007 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066127129/5000000000 : ℝ)^2199 ≤ (1580049996867/5000000000000 : ℝ)^1687 := by
    have hnat : (2066127129 : ℕ)^2199*5000000000000^1687 ≤ 1580049996867^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066127129 5000000000 1580049996867 5000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302153697/10000000000 : ℝ), (895667637/2000000000 : ℝ), (2066127129/5000000000 : ℝ)] ![(33305087281707/100000000000000 : ℝ), (35093912769007/100000000000000 : ℝ), (1580049996867/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302153697/10000000000 : ℝ)|^2199 ≤ (33305087281707/100000000000000 : ℝ)^1687
        have hw : |(4302153697/10000000000 : ℝ)|=(4302153697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895667637/2000000000 : ℝ)|^2199 ≤ (35093912769007/100000000000000 : ℝ)^1687
        have hw : |(895667637/2000000000 : ℝ)|=(895667637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066127129/5000000000 : ℝ)|^2199 ≤ (1580049996867/5000000000000 : ℝ)^1687
        have hw : |(2066127129/5000000000 : ℝ)|=(2066127129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1438_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5679/50000 : ℝ) ^ (4397/1024 : ℝ) ≤ (8780472128795811/100000000000000000000 : ℝ) := by
    have hpowers : (5679/50000 : ℝ)^4397 ≤ (8780472128795811/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5679 : ℕ)^4397*100000000000000000000^1024 ≤ 8780472128795811^1024*50000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5679 50000 8780472128795811 100000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5679/50000 : ℝ)) (X := (8780472128795811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (4397/1024 : ℝ) ≤ (13530845488209897/50000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^4397 ≤ (13530845488209897/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7381 : ℕ)^4397*50000000000000000000^1024 ≤ 13530845488209897^1024*50000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 13530845488209897 50000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (13530845488209897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008780472128795811/50000000000000000000 : ℝ) ≤ (10000408942365659/10000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50008780472128795811/50000000000000000000 : ℝ)^1024 ≤ (10000408942365659/10000000000000000 : ℝ)^4397 := by
      have hnat : (50008780472128795811 : ℕ)^1024*10000000000000000^4397 ≤ 10000408942365659^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008780472128795811 50000000000000000000 10000408942365659 10000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000408942365659/10000000000000000 : ℝ)) (X := (50008780472128795811/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007168432621043121/20000000000000000000 : ℝ) ≤ (5000417299640909/5000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (20007168432621043121/20000000000000000000 : ℝ)^1024 ≤ (5000417299640909/5000000000000000 : ℝ)^4397 := by
      have hnat : (20007168432621043121 : ℕ)^1024*5000000000000000^4397 ≤ 5000417299640909^4397*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007168432621043121 20000000000000000000 5000417299640909 5000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000417299640909/5000000000000000 : ℝ)) (X := (20007168432621043121/20000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013530845488209897/25000000000000000000 : ℝ) ≤ (10001260256197977/10000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (25013530845488209897/25000000000000000000 : ℝ)^1024 ≤ (10001260256197977/10000000000000000 : ℝ)^4397 := by
      have hnat : (25013530845488209897 : ℕ)^1024*10000000000000000^4397 ≤ 10001260256197977^4397*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013530845488209897 25000000000000000000 10001260256197977 10000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001260256197977/10000000000000000 : ℝ)) (X := (25013530845488209897/25000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8780472128795811/100000000000000000000 : ℝ) ≤ ((531745669020394303/531875000000000000 : ℝ)+2*(425656916159/340400000000000 : ℝ)*(5679/50000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (531745669020394303/531875000000000000 : ℝ)+2*(425656916159/340400000000000 : ℝ)*(5679/50000 : ℝ)=(10000408942365659/10000000000000000 : ℝ) by norm_num, show 1+2*(8780472128795811/100000000000000000000 : ℝ)=(50008780472128795811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13530845488209897/50000000000000000000 : ℝ)+(8780472128795811/100000000000000000000 : ℝ) ≤ ((531745669020394303/531875000000000000 : ℝ)+(425656916159/340400000000000 : ℝ)*((7381/50000 : ℝ)+(5679/50000 : ℝ)))^(4397/1024 : ℝ) := by
    rw [show (531745669020394303/531875000000000000 : ℝ)+(425656916159/340400000000000 : ℝ)*((7381/50000 : ℝ)+(5679/50000 : ℝ))=(5000417299640909/5000000000000000 : ℝ) by norm_num, show 1+(13530845488209897/50000000000000000000 : ℝ)+(8780472128795811/100000000000000000000 : ℝ)=(20007168432621043121/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13530845488209897/50000000000000000000 : ℝ) ≤ ((531745669020394303/531875000000000000 : ℝ)+2*(425656916159/340400000000000 : ℝ)*(7381/50000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (531745669020394303/531875000000000000 : ℝ)+2*(425656916159/340400000000000 : ℝ)*(7381/50000 : ℝ)=(10001260256197977/10000000000000000 : ℝ) by norm_num, show 1+2*(13530845488209897/50000000000000000000 : ℝ)=(25013530845488209897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (531745669020394303/531875000000000000 : ℝ)*(X 1 0+X 2 0)+(425656916159/340400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (531745669020394303/531875000000000000 : ℝ)) (alpha := (425656916159/340400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (531745669020394303/531875000000000000 : ℝ)*(X 0 1+X 2 1)+(425656916159/340400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (531745669020394303/531875000000000000 : ℝ)) (alpha := (425656916159/340400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (531745669020394303/531875000000000000 : ℝ)*(X 0 2+X 1 2)+(425656916159/340400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (531745669020394303/531875000000000000 : ℝ)) (alpha := (425656916159/340400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1963853137/10000000000 : ℝ)*X 0 0+(1351933909/2500000000 : ℝ)*X 0 1+(5247122357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069426319/2000000000 : ℝ)*X 1 0+(-2045617359/10000000000 : ℝ)*X 1 1+(1311780527/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336782831/2500000000 : ℝ)*X 2 0+(1049424509/2000000000 : ℝ)*X 2 1+(-2045617139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4201298/9765625 : ℝ)*X 0 0+(1032747467/2500000000 : ℝ)*X 0 1+(4479596221/10000000000 : ℝ)*X 0 2+(4201298/9765625 : ℝ)*X 1 0+(1032747467/2500000000 : ℝ)*X 1 1+(4479596221/10000000000 : ℝ)*X 1 2+(4201298/9765625 : ℝ)*X 2 0+(1032747467/2500000000 : ℝ)*X 2 1+(4479596221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1963864011/10000000000 : ℝ)*X 0 0+(5124709/9765625 : ℝ)*X 0 1+(5407153241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305339743/10000000000 : ℝ)*X 1 0+(-377117259/2000000000 : ℝ)*X 1 1+(5407153239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305339713/10000000000 : ℝ)*X 2 0+(1081430643/2000000000 : ℝ)*X 2 1+(-188558637/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302153697/10000000000 : ℝ)*X 0 0+(895667637/2000000000 : ℝ)*X 0 1+(2066127129/5000000000 : ℝ)*X 0 2+(4302153697/10000000000 : ℝ)*X 1 0+(895667637/2000000000 : ℝ)*X 1 1+(2066127129/5000000000 : ℝ)*X 1 2+(4302153697/10000000000 : ℝ)*X 2 0+(895667637/2000000000 : ℝ)*X 2 1+(2066127129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6147903230868176399241/2127500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1265758331/100000000000000 : ℝ)*(base19) + (569852619/100000000000000 : ℝ)*(base23) + (16580927/10000000000000 : ℝ)*(upper3) + (8135231/4000000000000 : ℝ)*(upper4) + (6294357/5000000000000 : ℝ)*(upper5) + (568421883878777/12500000000000 : ℝ)*(major0) + (568421883878777/12500000000000 : ℝ)*(major1) + (4547375071030217/100000000000000 : ℝ)*(major2) + (6226151512157961/100000000000000 : ℝ)*(sp0) + (1245233558085103/20000000000000 : ℝ)*(sp1) + (3113084243165613/50000000000000 : ℝ)*(sp2) + (1434286246498371/50000000000000 : ℝ)*(sp3) + (3508805177/20000000000000 : ℝ)*(sp4) + (8496555461/100000000000000 : ℝ)*(sp7) + (717145247388051/25000000000000 : ℝ)*(f.failure) + (3113084528091923/50000000000000 : ℝ)*(f.sum) + (163122021582487/34040000000000000000000000000 : ℝ)*base65 + (835138274597284229/106375000000000000000000000000000 : ℝ)*base68 + (64732038488066251/53187500000000000000000000000000 : ℝ)*base69 + (284619457592840771/106375000000000000000000000000000 : ℝ)*base71 + (98729308205393/34040000000000000000000000000 : ℝ)*base74 + (1091538056984308749/53187500000000000000000000000000 : ℝ)*base76 + (13098471235236319/6648437500000000000000000000000 : ℝ)*base78 + (950723166420903/3324218750000000000000000000000 : ℝ)*base79 + (207295825257/531875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (44862653/2500000000000000000000 : ℝ)*base89 + (44862653/2500000000000000000000 : ℝ)*base91 + (19862653/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275162876736082690931753013/53187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (839792613/100000000000000 : ℝ)*(base19) + (948779503/100000000000000 : ℝ)*(base23) + (71868849/25000000000000 : ℝ)*(lower1) + (1163481/1562500000000 : ℝ)*(upper3) + (16502907/20000000000000 : ℝ)*(lower4) + (31570439/25000000000000 : ℝ)*(upper5) + (4580477348731817/100000000000000 : ℝ)*(major0) + (4580477348731817/100000000000000 : ℝ)*(major1) + (4580477348731817/100000000000000 : ℝ)*(major2) + (140668877/10000000000000 : ℝ)*(sp1) + (3135745957039391/50000000000000 : ℝ)*(sp4) + (6271489667597399/100000000000000 : ℝ)*(sp5) + (6271490965299279/100000000000000 : ℝ)*(sp6) + (288946261093651/10000000000000 : ℝ)*(sp7) + (288946261093651/10000000000000 : ℝ)*(f.failure) + (3135745957039391/50000000000000 : ℝ)*(f.sum) + (21550470717543/17020000000000000000000000000 : ℝ)*base65 + (620890058522098977/106375000000000000000000000000000 : ℝ)*base67 + (791671591499598977/106375000000000000000000000000000 : ℝ)*base69 + (849028775026473977/106375000000000000000000000000000 : ℝ)*base71 + (44545063491603/17020000000000000000000000000 : ℝ)*base73 + (379732270223473977/106375000000000000000000000000000 : ℝ)*base75 + (552158715263526023/106375000000000000000000000000000 : ℝ)*base78 + (961523288581723977/106375000000000000000000000000000 : ℝ)*base79 + (19666343866097/17020000000000000000000000000 : ℝ)*base82 + (2420547/1000000000000000000000 : ℝ)*base90 + (2420547/1000000000000000000000 : ℝ)*base92 + (2420547/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1438_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1438_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1438_box_0 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-360768603/2000000000 : ℝ)*x 0 + (5259638/9765625 : ℝ)*x 1 + (5385869677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360768603/2000000000 : ℝ)^2199 ≤ (10726475382667/100000000000000 : ℝ)^1687 := by
    have hnat : (360768603 : ℕ)^2199*100000000000000^1687 ≤ 10726475382667^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360768603 2000000000 10726475382667 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259638/9765625 : ℝ)^2199 ≤ (44636760325293/100000000000000 : ℝ)^1687 := by
    have hnat : (5259638 : ℕ)^2199*100000000000000^1687 ≤ 44636760325293^1687*9765625^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259638 9765625 44636760325293 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385869677/10000000000 : ℝ)^2199 ≤ (44636764268411/100000000000000 : ℝ)^1687 := by
    have hnat : (5385869677 : ℕ)^2199*100000000000000^1687 ≤ 44636764268411^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385869677 10000000000 44636764268411 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360768603/2000000000 : ℝ), (5259638/9765625 : ℝ), (5385869677/10000000000 : ℝ)] ![(10726475382667/100000000000000 : ℝ), (44636760325293/100000000000000 : ℝ), (44636764268411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360768603/2000000000 : ℝ)|^2199 ≤ (10726475382667/100000000000000 : ℝ)^1687
        have hw : |(-360768603/2000000000 : ℝ)|=(360768603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259638/9765625 : ℝ)|^2199 ≤ (44636760325293/100000000000000 : ℝ)^1687
        have hw : |(5259638/9765625 : ℝ)|=(5259638/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385869677/10000000000 : ℝ)|^2199 ≤ (44636764268411/100000000000000 : ℝ)^1687
        have hw : |(5385869677/10000000000 : ℝ)|=(5385869677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_1 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286126827/10000000000 : ℝ)*x 0 + (-194091159/1000000000 : ℝ)*x 1 + (1077173881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286126827/10000000000 : ℝ)^2199 ≤ (21781138505241/50000000000000 : ℝ)^1687 := by
    have hnat : (5286126827 : ℕ)^2199*50000000000000^1687 ≤ 21781138505241^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286126827 10000000000 21781138505241 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194091159/1000000000 : ℝ)^2199 ≤ (11800961642937/100000000000000 : ℝ)^1687 := by
    have hnat : (194091159 : ℕ)^2199*100000000000000^1687 ≤ 11800961642937^1687*1000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194091159 1000000000 11800961642937 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077173881/2000000000 : ℝ)^2199 ≤ (22318380664989/50000000000000 : ℝ)^1687 := by
    have hnat : (1077173881 : ℕ)^2199*50000000000000^1687 ≤ 22318380664989^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077173881 2000000000 22318380664989 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286126827/10000000000 : ℝ), (-194091159/1000000000 : ℝ), (1077173881/2000000000 : ℝ)] ![(21781138505241/50000000000000 : ℝ), (11800961642937/100000000000000 : ℝ), (22318380664989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286126827/10000000000 : ℝ)|^2199 ≤ (21781138505241/50000000000000 : ℝ)^1687
        have hw : |(5286126827/10000000000 : ℝ)|=(5286126827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-194091159/1000000000 : ℝ)|^2199 ≤ (11800961642937/100000000000000 : ℝ)^1687
        have hw : |(-194091159/1000000000 : ℝ)|=(194091159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077173881/2000000000 : ℝ)|^2199 ≤ (22318380664989/50000000000000 : ℝ)^1687
        have hw : |(1077173881/2000000000 : ℝ)|=(1077173881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_2 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643063429/5000000000 : ℝ)*x 0 + (215434767/400000000 : ℝ)*x 1 + (-970455931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643063429/5000000000 : ℝ)^2199 ≤ (21781138671741/50000000000000 : ℝ)^1687 := by
    have hnat : (2643063429 : ℕ)^2199*50000000000000^1687 ≤ 21781138671741^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643063429 5000000000 21781138671741 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215434767/400000000 : ℝ)^2199 ≤ (44636758845273/100000000000000 : ℝ)^1687 := by
    have hnat : (215434767 : ℕ)^2199*100000000000000^1687 ≤ 44636758845273^1687*400000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215434767 400000000 44636758845273 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970455931/5000000000 : ℝ)^2199 ≤ (11800963798649/100000000000000 : ℝ)^1687 := by
    have hnat : (970455931 : ℕ)^2199*100000000000000^1687 ≤ 11800963798649^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970455931 5000000000 11800963798649 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643063429/5000000000 : ℝ), (215434767/400000000 : ℝ), (-970455931/5000000000 : ℝ)] ![(21781138671741/50000000000000 : ℝ), (44636758845273/100000000000000 : ℝ), (11800963798649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643063429/5000000000 : ℝ)|^2199 ≤ (21781138671741/50000000000000 : ℝ)^1687
        have hw : |(2643063429/5000000000 : ℝ)|=(2643063429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215434767/400000000 : ℝ)|^2199 ≤ (44636758845273/100000000000000 : ℝ)^1687
        have hw : |(215434767/400000000 : ℝ)|=(215434767/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970455931/5000000000 : ℝ)|^2199 ≤ (11800963798649/100000000000000 : ℝ)^1687
        have hw : |(-970455931/5000000000 : ℝ)|=(970455931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_3 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2224122739/5000000000 : ℝ)*x 0 + (4232762697/10000000000 : ℝ)*x 1 + (4232762369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224122739/5000000000 : ℝ)^2199 ≤ (34786839125009/100000000000000 : ℝ)^1687 := by
    have hnat : (2224122739 : ℕ)^2199*100000000000000^1687 ≤ 34786839125009^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224122739 5000000000 34786839125009 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232762697/10000000000 : ℝ)^2199 ≤ (32606582082277/100000000000000 : ℝ)^1687 := by
    have hnat : (4232762697 : ℕ)^2199*100000000000000^1687 ≤ 32606582082277^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232762697 10000000000 32606582082277 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232762369/10000000000 : ℝ)^2199 ≤ (32606578788719/100000000000000 : ℝ)^1687 := by
    have hnat : (4232762369 : ℕ)^2199*100000000000000^1687 ≤ 32606578788719^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232762369 10000000000 32606578788719 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2224122739/5000000000 : ℝ), (4232762697/10000000000 : ℝ), (4232762369/10000000000 : ℝ)] ![(34786839125009/100000000000000 : ℝ), (32606582082277/100000000000000 : ℝ), (32606578788719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2224122739/5000000000 : ℝ)|^2199 ≤ (34786839125009/100000000000000 : ℝ)^1687
        have hw : |(2224122739/5000000000 : ℝ)|=(2224122739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232762697/10000000000 : ℝ)|^2199 ≤ (32606582082277/100000000000000 : ℝ)^1687
        have hw : |(4232762697/10000000000 : ℝ)|=(4232762697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232762369/10000000000 : ℝ)|^2199 ≤ (32606578788719/100000000000000 : ℝ)^1687
        have hw : |(4232762369/10000000000 : ℝ)|=(4232762369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_4 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126596467/10000000000 : ℝ)*x 0 + (5266657739/10000000000 : ℝ)*x 1 + (263332817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126596467/10000000000 : ℝ)^2199 ≤ (13293498950629/100000000000000 : ℝ)^1687 := by
    have hnat : (2126596467 : ℕ)^2199*100000000000000^1687 ≤ 13293498950629^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126596467 10000000000 13293498950629 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266657739/10000000000 : ℝ)^2199 ≤ (8467433207/19531250000 : ℝ)^1687 := by
    have hnat : (5266657739 : ℕ)^2199*19531250000^1687 ≤ 8467433207^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266657739 10000000000 8467433207 19531250000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263332817/500000000 : ℝ)^2199 ≤ (1354788844021/3125000000000 : ℝ)^1687 := by
    have hnat : (263332817 : ℕ)^2199*3125000000000^1687 ≤ 1354788844021^1687*500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263332817 500000000 1354788844021 3125000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126596467/10000000000 : ℝ), (5266657739/10000000000 : ℝ), (263332817/500000000 : ℝ)] ![(13293498950629/100000000000000 : ℝ), (8467433207/19531250000 : ℝ), (1354788844021/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126596467/10000000000 : ℝ)|^2199 ≤ (13293498950629/100000000000000 : ℝ)^1687
        have hw : |(-2126596467/10000000000 : ℝ)|=(2126596467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266657739/10000000000 : ℝ)|^2199 ≤ (8467433207/19531250000 : ℝ)^1687
        have hw : |(5266657739/10000000000 : ℝ)|=(5266657739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263332817/500000000 : ℝ)|^2199 ≤ (1354788844021/3125000000000 : ℝ)^1687
        have hw : |(263332817/500000000 : ℝ)|=(263332817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_5 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684763237/5000000000 : ℝ)*x 0 + (-397873757/2000000000 : ℝ)*x 1 + (1053331577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684763237/5000000000 : ℝ)^2199 ≤ (44460288932451/100000000000000 : ℝ)^1687 := by
    have hnat : (2684763237 : ℕ)^2199*100000000000000^1687 ≤ 44460288932451^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684763237 5000000000 44460288932451 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397873757/2000000000 : ℝ)^2199 ≤ (609322573209/5000000000000 : ℝ)^1687 := by
    have hnat : (397873757 : ℕ)^2199*5000000000000^1687 ≤ 609322573209^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397873757 2000000000 609322573209 5000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053331577/2000000000 : ℝ)^2199 ≤ (4335325958641/10000000000000 : ℝ)^1687 := by
    have hnat : (1053331577 : ℕ)^2199*10000000000000^1687 ≤ 4335325958641^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053331577 2000000000 4335325958641 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684763237/5000000000 : ℝ), (-397873757/2000000000 : ℝ), (1053331577/2000000000 : ℝ)] ![(44460288932451/100000000000000 : ℝ), (609322573209/5000000000000 : ℝ), (4335325958641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684763237/5000000000 : ℝ)|^2199 ≤ (44460288932451/100000000000000 : ℝ)^1687
        have hw : |(2684763237/5000000000 : ℝ)|=(2684763237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397873757/2000000000 : ℝ)|^2199 ≤ (609322573209/5000000000000 : ℝ)^1687
        have hw : |(-397873757/2000000000 : ℝ)|=(397873757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053331577/2000000000 : ℝ)|^2199 ≤ (4335325958641/10000000000000 : ℝ)^1687
        have hw : |(1053331577/2000000000 : ℝ)|=(1053331577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_6 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073905353/2000000000 : ℝ)*x 0 + (1053331459/2000000000 : ℝ)*x 1 + (-397873837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073905353/2000000000 : ℝ)^2199 ≤ (11115073018311/25000000000000 : ℝ)^1687 := by
    have hnat : (1073905353 : ℕ)^2199*25000000000000^1687 ≤ 11115073018311^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073905353 2000000000 11115073018311 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053331459/2000000000 : ℝ)^2199 ≤ (43353253255753/100000000000000 : ℝ)^1687 := by
    have hnat : (1053331459 : ℕ)^2199*100000000000000^1687 ≤ 43353253255753^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053331459 2000000000 43353253255753 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397873837/2000000000 : ℝ)^2199 ≤ (12186454658159/100000000000000 : ℝ)^1687 := by
    have hnat : (397873837 : ℕ)^2199*100000000000000^1687 ≤ 12186454658159^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397873837 2000000000 12186454658159 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073905353/2000000000 : ℝ), (1053331459/2000000000 : ℝ), (-397873837/2000000000 : ℝ)] ![(11115073018311/25000000000000 : ℝ), (43353253255753/100000000000000 : ℝ), (12186454658159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073905353/2000000000 : ℝ)|^2199 ≤ (11115073018311/25000000000000 : ℝ)^1687
        have hw : |(1073905353/2000000000 : ℝ)|=(1073905353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053331459/2000000000 : ℝ)|^2199 ≤ (43353253255753/100000000000000 : ℝ)^1687
        have hw : |(1053331459/2000000000 : ℝ)|=(1053331459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397873837/2000000000 : ℝ)|^2199 ≤ (12186454658159/100000000000000 : ℝ)^1687
        have hw : |(-397873837/2000000000 : ℝ)|=(397873837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_7 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (129842269/312500000 : ℝ)*x 0 + (4379358597/10000000000 : ℝ)*x 1 + (875871613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129842269/312500000 : ℝ)^2199 ≤ (7956863435269/25000000000000 : ℝ)^1687 := by
    have hnat : (129842269 : ℕ)^2199*25000000000000^1687 ≤ 7956863435269^1687*312500000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129842269 312500000 7956863435269 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4379358597/10000000000 : ℝ)^2199 ≤ (8521568955517/25000000000000 : ℝ)^1687 := by
    have hnat : (4379358597 : ℕ)^2199*25000000000000^1687 ≤ 8521568955517^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379358597 10000000000 8521568955517 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875871613/2000000000 : ℝ)^2199 ≤ (34086270424591/100000000000000 : ℝ)^1687 := by
    have hnat : (875871613 : ℕ)^2199*100000000000000^1687 ≤ 34086270424591^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875871613 2000000000 34086270424591 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129842269/312500000 : ℝ), (4379358597/10000000000 : ℝ), (875871613/2000000000 : ℝ)] ![(7956863435269/25000000000000 : ℝ), (8521568955517/25000000000000 : ℝ), (34086270424591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129842269/312500000 : ℝ)|^2199 ≤ (7956863435269/25000000000000 : ℝ)^1687
        have hw : |(129842269/312500000 : ℝ)|=(129842269/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4379358597/10000000000 : ℝ)|^2199 ≤ (8521568955517/25000000000000 : ℝ)^1687
        have hw : |(4379358597/10000000000 : ℝ)|=(4379358597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875871613/2000000000 : ℝ)|^2199 ≤ (34086270424591/100000000000000 : ℝ)^1687
        have hw : |(875871613/2000000000 : ℝ)|=(875871613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_8 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029297839/5000000000 : ℝ)*x 0 + (648019761/1250000000 : ℝ)*x 1 + (2699919029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029297839/5000000000 : ℝ)^2199 ≤ (6371060184617/50000000000000 : ℝ)^1687 := by
    have hnat : (1029297839 : ℕ)^2199*50000000000000^1687 ≤ 6371060184617^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029297839 5000000000 6371060184617 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648019761/1250000000 : ℝ)^2199 ≤ (42470154660547/100000000000000 : ℝ)^1687 := by
    have hnat : (648019761 : ℕ)^2199*100000000000000^1687 ≤ 42470154660547^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648019761 1250000000 42470154660547 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699919029/5000000000 : ℝ)^2199 ≤ (44787724957541/100000000000000 : ℝ)^1687 := by
    have hnat : (2699919029 : ℕ)^2199*100000000000000^1687 ≤ 44787724957541^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699919029 5000000000 44787724957541 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029297839/5000000000 : ℝ), (648019761/1250000000 : ℝ), (2699919029/5000000000 : ℝ)] ![(6371060184617/50000000000000 : ℝ), (42470154660547/100000000000000 : ℝ), (44787724957541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029297839/5000000000 : ℝ)|^2199 ≤ (6371060184617/50000000000000 : ℝ)^1687
        have hw : |(-1029297839/5000000000 : ℝ)|=(1029297839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648019761/1250000000 : ℝ)|^2199 ≤ (42470154660547/100000000000000 : ℝ)^1687
        have hw : |(648019761/1250000000 : ℝ)|=(648019761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699919029/5000000000 : ℝ)|^2199 ≤ (44787724957541/100000000000000 : ℝ)^1687
        have hw : |(2699919029/5000000000 : ℝ)|=(2699919029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_9 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638175541/5000000000 : ℝ)*x 0 + (-483777009/2500000000 : ℝ)*x 1 + (5399837329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638175541/5000000000 : ℝ)^2199 ≤ (5432161990639/12500000000000 : ℝ)^1687 := by
    have hnat : (2638175541 : ℕ)^2199*12500000000000^1687 ≤ 5432161990639^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638175541 5000000000 5432161990639 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483777009/2500000000 : ℝ)^2199 ≤ (5877493488587/50000000000000 : ℝ)^1687 := by
    have hnat : (483777009 : ℕ)^2199*50000000000000^1687 ≤ 5877493488587^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483777009 2500000000 5877493488587 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399837329/10000000000 : ℝ)^2199 ≤ (44787717075913/100000000000000 : ℝ)^1687 := by
    have hnat : (5399837329 : ℕ)^2199*100000000000000^1687 ≤ 44787717075913^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399837329 10000000000 44787717075913 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638175541/5000000000 : ℝ), (-483777009/2500000000 : ℝ), (5399837329/10000000000 : ℝ)] ![(5432161990639/12500000000000 : ℝ), (5877493488587/50000000000000 : ℝ), (44787717075913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638175541/5000000000 : ℝ)|^2199 ≤ (5432161990639/12500000000000 : ℝ)^1687
        have hw : |(2638175541/5000000000 : ℝ)|=(2638175541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-483777009/2500000000 : ℝ)|^2199 ≤ (5877493488587/50000000000000 : ℝ)^1687
        have hw : |(-483777009/2500000000 : ℝ)|=(483777009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399837329/10000000000 : ℝ)|^2199 ≤ (44787717075913/100000000000000 : ℝ)^1687
        have hw : |(5399837329/10000000000 : ℝ)|=(5399837329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_10 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (263817549/500000000 : ℝ)*x 0 + (5399836853/10000000000 : ℝ)*x 1 + (-77404353/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263817549/500000000 : ℝ)^2199 ≤ (43457294830049/100000000000000 : ℝ)^1687 := by
    have hnat : (263817549 : ℕ)^2199*100000000000000^1687 ≤ 43457294830049^1687*500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263817549 500000000 43457294830049 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399836853/10000000000 : ℝ)^2199 ≤ (4478771192961/10000000000000 : ℝ)^1687 := by
    have hnat : (5399836853 : ℕ)^2199*10000000000000^1687 ≤ 4478771192961^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399836853 10000000000 4478771192961 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77404353/400000000 : ℝ)^2199 ≤ (11754993224643/100000000000000 : ℝ)^1687 := by
    have hnat : (77404353 : ℕ)^2199*100000000000000^1687 ≤ 11754993224643^1687*400000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77404353 400000000 11754993224643 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263817549/500000000 : ℝ), (5399836853/10000000000 : ℝ), (-77404353/400000000 : ℝ)] ![(43457294830049/100000000000000 : ℝ), (4478771192961/10000000000000 : ℝ), (11754993224643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263817549/500000000 : ℝ)|^2199 ≤ (43457294830049/100000000000000 : ℝ)^1687
        have hw : |(263817549/500000000 : ℝ)|=(263817549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399836853/10000000000 : ℝ)|^2199 ≤ (4478771192961/10000000000000 : ℝ)^1687
        have hw : |(5399836853/10000000000 : ℝ)|=(5399836853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77404353/400000000 : ℝ)|^2199 ≤ (11754993224643/100000000000000 : ℝ)^1687
        have hw : |(-77404353/400000000 : ℝ)|=(77404353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_11 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1120513457/2500000000 : ℝ)*x 0 + (1053892683/2500000000 : ℝ)*x 1 + (2107785951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120513457/2500000000 : ℝ)^2199 ≤ (35131871675979/100000000000000 : ℝ)^1687 := by
    have hnat : (1120513457 : ℕ)^2199*100000000000000^1687 ≤ 35131871675979^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120513457 2500000000 35131871675979 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053892683/2500000000 : ℝ)^2199 ≤ (32434058284883/100000000000000 : ℝ)^1687 := by
    have hnat : (1053892683 : ℕ)^2199*100000000000000^1687 ≤ 32434058284883^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053892683 2500000000 32434058284883 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107785951/5000000000 : ℝ)^2199 ≤ (4054258752343/12500000000000 : ℝ)^1687 := by
    have hnat : (2107785951 : ℕ)^2199*12500000000000^1687 ≤ 4054258752343^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107785951 5000000000 4054258752343 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120513457/2500000000 : ℝ), (1053892683/2500000000 : ℝ), (2107785951/5000000000 : ℝ)] ![(35131871675979/100000000000000 : ℝ), (32434058284883/100000000000000 : ℝ), (4054258752343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120513457/2500000000 : ℝ)|^2199 ≤ (35131871675979/100000000000000 : ℝ)^1687
        have hw : |(1120513457/2500000000 : ℝ)|=(1120513457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053892683/2500000000 : ℝ)|^2199 ≤ (32434058284883/100000000000000 : ℝ)^1687
        have hw : |(1053892683/2500000000 : ℝ)|=(1053892683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107785951/5000000000 : ℝ)|^2199 ≤ (4054258752343/12500000000000 : ℝ)^1687
        have hw : |(2107785951/5000000000 : ℝ)|=(2107785951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_12 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-936004353/5000000000 : ℝ)*x 0 + (2733180783/5000000000 : ℝ)*x 1 + (131388181/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936004353/5000000000 : ℝ)^2199 ≤ (11257844405827/100000000000000 : ℝ)^1687 := by
    have hnat : (936004353 : ℕ)^2199*100000000000000^1687 ≤ 11257844405827^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936004353 5000000000 11257844405827 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733180783/5000000000 : ℝ)^2199 ≤ (45508288682653/100000000000000 : ℝ)^1687 := by
    have hnat : (2733180783 : ℕ)^2199*100000000000000^1687 ≤ 45508288682653^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733180783 5000000000 45508288682653 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131388181/250000000 : ℝ)^2199 ≤ (8646773378367/20000000000000 : ℝ)^1687 := by
    have hnat : (131388181 : ℕ)^2199*20000000000000^1687 ≤ 8646773378367^1687*250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131388181 250000000 8646773378367 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936004353/5000000000 : ℝ), (2733180783/5000000000 : ℝ), (131388181/250000000 : ℝ)] ![(11257844405827/100000000000000 : ℝ), (45508288682653/100000000000000 : ℝ), (8646773378367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936004353/5000000000 : ℝ)|^2199 ≤ (11257844405827/100000000000000 : ℝ)^1687
        have hw : |(-936004353/5000000000 : ℝ)|=(936004353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733180783/5000000000 : ℝ)|^2199 ≤ (45508288682653/100000000000000 : ℝ)^1687
        have hw : |(2733180783/5000000000 : ℝ)|=(2733180783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131388181/250000000 : ℝ)|^2199 ≤ (8646773378367/20000000000000 : ℝ)^1687
        have hw : |(131388181/250000000 : ℝ)|=(131388181/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_13 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5377311887/10000000000 : ℝ)*x 0 + (-1993794473/10000000000 : ℝ)*x 1 + (2627763369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377311887/10000000000 : ℝ)^2199 ≤ (44544336201819/100000000000000 : ℝ)^1687 := by
    have hnat : (5377311887 : ℕ)^2199*100000000000000^1687 ≤ 44544336201819^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377311887 10000000000 44544336201819 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993794473/10000000000 : ℝ)^2199 ≤ (12221802278149/100000000000000 : ℝ)^1687 := by
    have hnat : (1993794473 : ℕ)^2199*100000000000000^1687 ≤ 12221802278149^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993794473 10000000000 12221802278149 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627763369/5000000000 : ℝ)^2199 ≤ (43233861508869/100000000000000 : ℝ)^1687 := by
    have hnat : (2627763369 : ℕ)^2199*100000000000000^1687 ≤ 43233861508869^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627763369 5000000000 43233861508869 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377311887/10000000000 : ℝ), (-1993794473/10000000000 : ℝ), (2627763369/5000000000 : ℝ)] ![(44544336201819/100000000000000 : ℝ), (12221802278149/100000000000000 : ℝ), (43233861508869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377311887/10000000000 : ℝ)|^2199 ≤ (44544336201819/100000000000000 : ℝ)^1687
        have hw : |(5377311887/10000000000 : ℝ)|=(5377311887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993794473/10000000000 : ℝ)|^2199 ≤ (12221802278149/100000000000000 : ℝ)^1687
        have hw : |(-1993794473/10000000000 : ℝ)|=(1993794473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627763369/5000000000 : ℝ)|^2199 ≤ (43233861508869/100000000000000 : ℝ)^1687
        have hw : |(2627763369/5000000000 : ℝ)|=(2627763369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_14 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2688655917/5000000000 : ℝ)*x 0 + (1051105481/2000000000 : ℝ)*x 1 + (-1993793649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688655917/5000000000 : ℝ)^2199 ≤ (44544335629533/100000000000000 : ℝ)^1687 := by
    have hnat : (2688655917 : ℕ)^2199*100000000000000^1687 ≤ 44544335629533^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688655917 5000000000 44544335629533 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051105481/2000000000 : ℝ)^2199 ≤ (2702116791321/6250000000000 : ℝ)^1687 := by
    have hnat : (1051105481 : ℕ)^2199*6250000000000^1687 ≤ 2702116791321^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051105481 2000000000 2702116791321 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993793649/10000000000 : ℝ)^2199 ≤ (12221795694113/100000000000000 : ℝ)^1687 := by
    have hnat : (1993793649 : ℕ)^2199*100000000000000^1687 ≤ 12221795694113^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993793649 10000000000 12221795694113 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688655917/5000000000 : ℝ), (1051105481/2000000000 : ℝ), (-1993793649/10000000000 : ℝ)] ![(44544335629533/100000000000000 : ℝ), (2702116791321/6250000000000 : ℝ), (12221795694113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688655917/5000000000 : ℝ)|^2199 ≤ (44544335629533/100000000000000 : ℝ)^1687
        have hw : |(2688655917/5000000000 : ℝ)|=(2688655917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051105481/2000000000 : ℝ)|^2199 ≤ (2702116791321/6250000000000 : ℝ)^1687
        have hw : |(1051105481/2000000000 : ℝ)|=(1051105481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993793649/10000000000 : ℝ)|^2199 ≤ (12221795694113/100000000000000 : ℝ)^1687
        have hw : |(-1993793649/10000000000 : ℝ)|=(1993793649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_box_15 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4127120123/10000000000 : ℝ)*x 0 + (2196516833/5000000000 : ℝ)*x 1 + (4393033843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127120123/10000000000 : ℝ)^2199 ≤ (31549830657291/100000000000000 : ℝ)^1687 := by
    have hnat : (4127120123 : ℕ)^2199*100000000000000^1687 ≤ 31549830657291^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127120123 10000000000 31549830657291 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196516833/5000000000 : ℝ)^2199 ≤ (6845016752669/20000000000000 : ℝ)^1687 := by
    have hnat : (2196516833 : ℕ)^2199*20000000000000^1687 ≤ 6845016752669^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196516833 5000000000 6845016752669 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4393033843/10000000000 : ℝ)^2199 ≤ (17112542780411/50000000000000 : ℝ)^1687 := by
    have hnat : (4393033843 : ℕ)^2199*50000000000000^1687 ≤ 17112542780411^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393033843 10000000000 17112542780411 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127120123/10000000000 : ℝ), (2196516833/5000000000 : ℝ), (4393033843/10000000000 : ℝ)] ![(31549830657291/100000000000000 : ℝ), (6845016752669/20000000000000 : ℝ), (17112542780411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127120123/10000000000 : ℝ)|^2199 ≤ (31549830657291/100000000000000 : ℝ)^1687
        have hw : |(4127120123/10000000000 : ℝ)|=(4127120123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2196516833/5000000000 : ℝ)|^2199 ≤ (6845016752669/20000000000000 : ℝ)^1687
        have hw : |(2196516833/5000000000 : ℝ)|=(2196516833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4393033843/10000000000 : ℝ)|^2199 ≤ (17112542780411/50000000000000 : ℝ)^1687
        have hw : |(4393033843/10000000000 : ℝ)|=(4393033843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1438_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12581/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59131/100000 : ℝ) ∧ (40249/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42359/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11359/100000 : ℝ) ^ (4397/1024 : ℝ) ≤ (4391896054476739/50000000000000000000 : ℝ) := by
    have hpowers : (11359/100000 : ℝ)^4397 ≤ (4391896054476739/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11359 : ℕ)^4397*50000000000000000000^1024 ≤ 4391896054476739^1024*100000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11359 100000 4391896054476739 50000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11359/100000 : ℝ)) (X := (4391896054476739/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (4397/1024 : ℝ) ≤ (6763455049053771/25000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^4397 ≤ (6763455049053771/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14761 : ℕ)^4397*25000000000000000000^1024 ≤ 6763455049053771^1024*100000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 6763455049053771 25000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (6763455049053771/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004391896054476739/25000000000000000000 : ℝ) ≤ (2000081819396049/2000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (25004391896054476739/25000000000000000000 : ℝ)^1024 ≤ (2000081819396049/2000000000000000 : ℝ)^4397 := by
      have hnat : (25004391896054476739 : ℕ)^1024*2000000000000000^4397 ≤ 2000081819396049^4397*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004391896054476739 25000000000000000000 2000081819396049 2000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081819396049/2000000000000000 : ℝ)) (X := (25004391896054476739/25000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017918806152584281/50000000000000000000 : ℝ) ≤ (5000417246664579/5000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50017918806152584281/50000000000000000000 : ℝ)^1024 ≤ (5000417246664579/5000000000000000 : ℝ)^4397 := by
      have hnat : (50017918806152584281 : ℕ)^1024*5000000000000000^4397 ≤ 5000417246664579^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017918806152584281 50000000000000000000 5000417246664579 5000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000417246664579/5000000000000000 : ℝ)) (X := (50017918806152584281/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506763455049053771/12500000000000000000 : ℝ) ≤ (10001259889678071/10000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (12506763455049053771/12500000000000000000 : ℝ)^1024 ≤ (10001259889678071/10000000000000000 : ℝ)^4397 := by
      have hnat : (12506763455049053771 : ℕ)^1024*10000000000000000^4397 ≤ 10001259889678071^4397*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506763455049053771 12500000000000000000 10001259889678071 10000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259889678071/10000000000000000 : ℝ)) (X := (12506763455049053771/12500000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4391896054476739/50000000000000000000 : ℝ) ≤ ((2834310632806015663/2835000000000000000 : ℝ)+2*(141798782971/113400000000000 : ℝ)*(11359/100000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (2834310632806015663/2835000000000000000 : ℝ)+2*(141798782971/113400000000000 : ℝ)*(11359/100000 : ℝ)=(2000081819396049/2000000000000000 : ℝ) by norm_num, show 1+2*(4391896054476739/50000000000000000000 : ℝ)=(25004391896054476739/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6763455049053771/25000000000000000000 : ℝ)+(4391896054476739/50000000000000000000 : ℝ) ≤ ((2834310632806015663/2835000000000000000 : ℝ)+(141798782971/113400000000000 : ℝ)*((14761/100000 : ℝ)+(11359/100000 : ℝ)))^(4397/1024 : ℝ) := by
    rw [show (2834310632806015663/2835000000000000000 : ℝ)+(141798782971/113400000000000 : ℝ)*((14761/100000 : ℝ)+(11359/100000 : ℝ))=(5000417246664579/5000000000000000 : ℝ) by norm_num, show 1+(6763455049053771/25000000000000000000 : ℝ)+(4391896054476739/50000000000000000000 : ℝ)=(50017918806152584281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6763455049053771/25000000000000000000 : ℝ) ≤ ((2834310632806015663/2835000000000000000 : ℝ)+2*(141798782971/113400000000000 : ℝ)*(14761/100000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (2834310632806015663/2835000000000000000 : ℝ)+2*(141798782971/113400000000000 : ℝ)*(14761/100000 : ℝ)=(10001259889678071/10000000000000000 : ℝ) by norm_num, show 1+2*(6763455049053771/25000000000000000000 : ℝ)=(12506763455049053771/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2834310632806015663/2835000000000000000 : ℝ)*(X 1 0+X 2 0)+(141798782971/113400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (2834310632806015663/2835000000000000000 : ℝ)) (alpha := (141798782971/113400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2834310632806015663/2835000000000000000 : ℝ)*(X 0 1+X 2 1)+(141798782971/113400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (2834310632806015663/2835000000000000000 : ℝ)) (alpha := (141798782971/113400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2834310632806015663/2835000000000000000 : ℝ)*(X 0 2+X 1 2)+(141798782971/113400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (2834310632806015663/2835000000000000000 : ℝ)) (alpha := (141798782971/113400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-360768603/2000000000 : ℝ)*X 0 0+(5259638/9765625 : ℝ)*X 0 1+(5385869677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286126827/10000000000 : ℝ)*X 1 0+(-194091159/1000000000 : ℝ)*X 1 1+(1077173881/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2643063429/5000000000 : ℝ)*X 2 0+(215434767/400000000 : ℝ)*X 2 1+(-970455931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2224122739/5000000000 : ℝ)*X 0 0+(4232762697/10000000000 : ℝ)*X 0 1+(4232762369/10000000000 : ℝ)*X 0 2+(2224122739/5000000000 : ℝ)*X 1 0+(4232762697/10000000000 : ℝ)*X 1 1+(4232762369/10000000000 : ℝ)*X 1 2+(2224122739/5000000000 : ℝ)*X 2 0+(4232762697/10000000000 : ℝ)*X 2 1+(4232762369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2126596467/10000000000 : ℝ)*X 0 0+(5266657739/10000000000 : ℝ)*X 0 1+(263332817/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684763237/5000000000 : ℝ)*X 1 0+(-397873757/2000000000 : ℝ)*X 1 1+(1053331577/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1073905353/2000000000 : ℝ)*X 2 0+(1053331459/2000000000 : ℝ)*X 2 1+(-397873837/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((129842269/312500000 : ℝ)*X 0 0+(4379358597/10000000000 : ℝ)*X 0 1+(875871613/2000000000 : ℝ)*X 0 2+(129842269/312500000 : ℝ)*X 1 0+(4379358597/10000000000 : ℝ)*X 1 1+(875871613/2000000000 : ℝ)*X 1 2+(129842269/312500000 : ℝ)*X 2 0+(4379358597/10000000000 : ℝ)*X 2 1+(875871613/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1029297839/5000000000 : ℝ)*X 0 0+(648019761/1250000000 : ℝ)*X 0 1+(2699919029/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638175541/5000000000 : ℝ)*X 1 0+(-483777009/2500000000 : ℝ)*X 1 1+(5399837329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((263817549/500000000 : ℝ)*X 2 0+(5399836853/10000000000 : ℝ)*X 2 1+(-77404353/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1120513457/2500000000 : ℝ)*X 0 0+(1053892683/2500000000 : ℝ)*X 0 1+(2107785951/5000000000 : ℝ)*X 0 2+(1120513457/2500000000 : ℝ)*X 1 0+(1053892683/2500000000 : ℝ)*X 1 1+(2107785951/5000000000 : ℝ)*X 1 2+(1120513457/2500000000 : ℝ)*X 2 0+(1053892683/2500000000 : ℝ)*X 2 1+(2107785951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-936004353/5000000000 : ℝ)*X 0 0+(2733180783/5000000000 : ℝ)*X 0 1+(131388181/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377311887/10000000000 : ℝ)*X 1 0+(-1993794473/10000000000 : ℝ)*X 1 1+(2627763369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688655917/5000000000 : ℝ)*X 2 0+(1051105481/2000000000 : ℝ)*X 2 1+(-1993793649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4127120123/10000000000 : ℝ)*X 0 0+(2196516833/5000000000 : ℝ)*X 0 1+(4393033843/10000000000 : ℝ)*X 0 2+(4127120123/10000000000 : ℝ)*X 1 0+(2196516833/5000000000 : ℝ)*X 1 1+(4393033843/10000000000 : ℝ)*X 1 2+(4127120123/10000000000 : ℝ)*X 2 0+(2196516833/5000000000 : ℝ)*X 2 1+(4393033843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12581/20000 : ℝ) ≤ (-29721452028387771638608373044147/47250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24128847/50000000000000 : ℝ)*(lower0) + (1003119/20000000000000 : ℝ)*(upper3) + (13199137/50000000000000 : ℝ)*(lower4) + (65493079/50000000000000 : ℝ)*(lower5) + (3026648185491869/100000000000000 : ℝ)*(major0) + (3026648185491869/100000000000000 : ℝ)*(major1) + (3026648185491869/100000000000000 : ℝ)*(major2) + (4164965229041141/100000000000000 : ℝ)*(sp4) + (2082355002014003/50000000000000 : ℝ)*(sp5) + (2082449792344451/50000000000000 : ℝ)*(sp6) + (954637050094669/50000000000000 : ℝ)*(sp7) + (24556411727/100000000000000 : ℝ)*(sp8) + (139890712431/50000000000000 : ℝ)*(sp13) + (45100381983/50000000000000 : ℝ)*(sp14) + (954637050094669/50000000000000 : ℝ)*(f.failure) + (1041247446363217/25000000000000 : ℝ)*(f.sum) + (7146360144629/5670000000000000000000000000 : ℝ)*base65 + (465713330600380853/283500000000000000000000000000000 : ℝ)*base68 + (1250588832797119147/283500000000000000000000000000000 : ℝ)*base69 + (16417422213880853/283500000000000000000000000000000 : ℝ)*base72 + (2624367318299/5670000000000000000000000000 : ℝ)*base73 + (1591044731237119147/283500000000000000000000000000000 : ℝ)*base75 + (943040065880119147/283500000000000000000000000000000 : ℝ)*base77 + (1889834263292119147/283500000000000000000000000000000 : ℝ)*base79 + (24098268641579/5670000000000000000000000000 : ℝ)*base81 + (38494493/5000000000000000000000 : ℝ)*base90 + (38494493/5000000000000000000000 : ℝ)*base92 + (38494493/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59131/100000 : ℝ) ≤ (9313574258557542987818894511389/15750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22755101/100000000000000 : ℝ)*(lower0) + (4999819/12500000000000 : ℝ)*(upper2) + (62485369/50000000000000 : ℝ)*(lower5) + (309856154894359/10000000000000 : ℝ)*(major0) + (309856154894359/10000000000000 : ℝ)*(major1) + (3098561548943591/100000000000000 : ℝ)*(major2) + (211138104930609/5000000000000 : ℝ)*(sp0) + (4222770692412711/100000000000000 : ℝ)*(sp1) + (422274075362277/10000000000000 : ℝ)*(sp2) + (97731734657481/5000000000000 : ℝ)*(sp3) + (2556610591/100000000000000 : ℝ)*(sp5) + (1943721087/50000000000000 : ℝ)*(sp7) + (8123850133/25000000000000 : ℝ)*(sp10) + (11150411123/100000000000000 : ℝ)*(sp12) + (977319290295897/50000000000000 : ℝ)*(f.failure) + (2111386624511651/50000000000000 : ℝ)*(f.sum) + (8730190903997/3780000000000000000000000000 : ℝ)*base65 + (2172141560034161/9450000000000000000000000000000 : ℝ)*base68 + (33808387539079537/31500000000000000000000000000000 : ℝ)*base69 + (11638003262184161/9450000000000000000000000000000 : ℝ)*base72 + (35896204263377/3780000000000000000000000000 : ℝ)*base73 + (172335603324079537/31500000000000000000000000000000 : ℝ)*base75 + (115301502870017/28350000000000000000000000000000 : ℝ)*base77 + (98222478239670017/28350000000000000000000000000000 : ℝ)*base79 + (638628075439/567000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1032809/5000000000000000000000 : ℝ)*base90 + (1032809/5000000000000000000000 : ℝ)*base92 + (51032809/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40249/50000 : ℝ) ≤ (792426644506101397633282834817/984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414833591/100000000000000 : ℝ)*(upper0) + (139485429/100000000000000 : ℝ)*(upper2) + (94910449/20000000000000 : ℝ)*(lower5) + (212871574064791/6250000000000 : ℝ)*(major0) + (212871574064791/6250000000000 : ℝ)*(major1) + (212871574064791/6250000000000 : ℝ)*(major2) + (94307885577/100000000000000 : ℝ)*(sp1) + (6192722461/10000000000000 : ℝ)*(sp3) + (14865548389/100000000000000 : ℝ)*(sp4) + (4636480457745407/100000000000000 : ℝ)*(sp8) + (231820992309293/5000000000000 : ℝ)*(sp9) + (4636514154071437/100000000000000 : ℝ)*(sp10) + (1074240396968421/50000000000000 : ℝ)*(sp11) + (18830777641/100000000000000 : ℝ)*(sp12) + (537135680290363/25000000000000 : ℝ)*(f.failure) + (4636514154071437/100000000000000 : ℝ)*(f.sum) + (10841127926347/2835000000000000000000000000 : ℝ)*base66 + (216801612125315183/17718750000000000000000000000000 : ℝ)*base67 + (33059420731846433/17718750000000000000000000000000 : ℝ)*base69 + (207290934006065183/17718750000000000000000000000000 : ℝ)*base71 + (4520332753513/708750000000000000000000000 : ℝ)*base74 + (2057580885815183/17718750000000000000000000000000 : ℝ)*base75 + (111702112784596433/17718750000000000000000000000000 : ℝ)*base77 + (48420549382940183/17718750000000000000000000000000 : ℝ)*base79 + (6134669151427/2835000000000000000000000000 : ℝ)*base82 + (98411/2500000000000000000000 : ℝ)*base90 + (98411/2500000000000000000000 : ℝ)*base92 + (98411/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42359/50000 : ℝ) ≤ (-2001414060712116955234503909143/2362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118758473/100000000000000 : ℝ)*(lower1) + (36111297/12500000000000 : ℝ)*(lower2) + (13199881/10000000000000 : ℝ)*(upper5) + (172177519810039/5000000000000 : ℝ)*(major0) + (172177519810039/5000000000000 : ℝ)*(major1) + (172177519810039/5000000000000 : ℝ)*(major2) + (4669702311/50000000000000 : ℝ)*(sp4) + (50419398297/12500000000000 : ℝ)*(sp5) + (123093480327/100000000000000 : ℝ)*(sp7) + (5663182887/100000000000000 : ℝ)*(sp8) + (474305954735061/10000000000000 : ℝ)*(sp12) + (4742671194751743/100000000000000 : ℝ)*(sp13) + (118576863748453/2500000000000 : ℝ)*(sp14) + (2172141795342361/100000000000000 : ℝ)*(sp15) + (67883277775709/3125000000000 : ℝ)*(f.failure) + (118576863748453/2500000000000 : ℝ)*(f.sum) + (506918009519/113400000000000000000000000 : ℝ)*base66 + (14538253833959143/14175000000000000000000000000000 : ℝ)*base68 + (140769921473834143/14175000000000000000000000000000 : ℝ)*base70 + (90090981004665857/14175000000000000000000000000000 : ℝ)*base71 + (2406645013/1107421875000000000000000 : ℝ)*base73 + (81368815235234143/14175000000000000000000000000000 : ℝ)*base76 + (7029381752040857/14175000000000000000000000000000 : ℝ)*base77 + (35951201982509143/14175000000000000000000000000000 : ℝ)*base80 + (149679856493/141750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1488627/312500000000000000000 : ℝ)*base89 + (1488627/312500000000000000000 : ℝ)*base91 + (1488627/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1438_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12581/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59131/100000 : ℝ) else (40249/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42359/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1438_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1438_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12581/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59131/100000 : ℝ) else (40249/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42359/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1438_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1438_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1438_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12581/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59131/100000 : ℝ) else (40249/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42359/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1438_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
