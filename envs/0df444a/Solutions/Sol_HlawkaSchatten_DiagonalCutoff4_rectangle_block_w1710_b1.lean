-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:36.889412+00:00
-- url     : https://prove2.me/submissions/c21e8800-cd53-41f2-b02d-296191db2cf4

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
theorem support_rectangle_w1710_s3_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-706037481/5000000000 : ℝ)*x 0 + (5470025003/10000000000 : ℝ)*x 1 + (642287313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (706037481/5000000000 : ℝ)^5303 ≤ (4419587164783/50000000000000 : ℝ)^4279 := by
    have hnat : (706037481 : ℕ)^5303*50000000000000^4279 ≤ 4419587164783^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706037481 5000000000 4419587164783 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470025003/10000000000 : ℝ)^5303 ≤ (47346512218771/100000000000000 : ℝ)^4279 := by
    have hnat : (5470025003 : ℕ)^5303*100000000000000^4279 ≤ 47346512218771^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470025003 10000000000 47346512218771 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642287313/1250000000 : ℝ)^5303 ≤ (43814313432573/100000000000000 : ℝ)^4279 := by
    have hnat : (642287313 : ℕ)^5303*100000000000000^4279 ≤ 43814313432573^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642287313 1250000000 43814313432573 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-706037481/5000000000 : ℝ), (5470025003/10000000000 : ℝ), (642287313/1250000000 : ℝ)] ![(4419587164783/50000000000000 : ℝ), (47346512218771/100000000000000 : ℝ), (43814313432573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-706037481/5000000000 : ℝ)|^5303 ≤ (4419587164783/50000000000000 : ℝ)^4279
        have hw : |(-706037481/5000000000 : ℝ)|=(706037481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470025003/10000000000 : ℝ)|^5303 ≤ (47346512218771/100000000000000 : ℝ)^4279
        have hw : |(5470025003/10000000000 : ℝ)|=(5470025003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642287313/1250000000 : ℝ)|^5303 ≤ (43814313432573/100000000000000 : ℝ)^4279
        have hw : |(642287313/1250000000 : ℝ)|=(642287313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343516981/10000000000 : ℝ)*x 0 + (-1584083897/10000000000 : ℝ)*x 1 + (642287309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343516981/10000000000 : ℝ)^5303 ≤ (9198647818929/20000000000000 : ℝ)^4279 := by
    have hnat : (5343516981 : ℕ)^5303*20000000000000^4279 ≤ 9198647818929^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343516981 10000000000 9198647818929 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1584083897/10000000000 : ℝ)^5303 ≤ (5096223900331/50000000000000 : ℝ)^4279 := by
    have hnat : (1584083897 : ℕ)^5303*50000000000000^4279 ≤ 5096223900331^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584083897 10000000000 5096223900331 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642287309/1250000000 : ℝ)^5303 ≤ (43814313094411/100000000000000 : ℝ)^4279 := by
    have hnat : (642287309 : ℕ)^5303*100000000000000^4279 ≤ 43814313094411^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642287309 1250000000 43814313094411 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343516981/10000000000 : ℝ), (-1584083897/10000000000 : ℝ), (642287309/1250000000 : ℝ)] ![(9198647818929/20000000000000 : ℝ), (5096223900331/50000000000000 : ℝ), (43814313094411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343516981/10000000000 : ℝ)|^5303 ≤ (9198647818929/20000000000000 : ℝ)^4279
        have hw : |(5343516981/10000000000 : ℝ)|=(5343516981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1584083897/10000000000 : ℝ)|^5303 ≤ (5096223900331/50000000000000 : ℝ)^4279
        have hw : |(-1584083897/10000000000 : ℝ)|=(1584083897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642287309/1250000000 : ℝ)|^5303 ≤ (43814313094411/100000000000000 : ℝ)^4279
        have hw : |(642287309/1250000000 : ℝ)|=(642287309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343516943/10000000000 : ℝ)*x 0 + (1284574623/2500000000 : ℝ)*x 1 + (-1584083921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343516943/10000000000 : ℝ)^5303 ≤ (2874577418081/6250000000000 : ℝ)^4279 := by
    have hnat : (5343516943 : ℕ)^5303*6250000000000^4279 ≤ 2874577418081^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343516943 10000000000 2874577418081 6250000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284574623/2500000000 : ℝ)^5303 ≤ (21907156652881/50000000000000 : ℝ)^4279 := by
    have hnat : (1284574623 : ℕ)^5303*50000000000000^4279 ≤ 21907156652881^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284574623 2500000000 21907156652881 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584083921/10000000000 : ℝ)^5303 ≤ (10192447992039/100000000000000 : ℝ)^4279 := by
    have hnat : (1584083921 : ℕ)^5303*100000000000000^4279 ≤ 10192447992039^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584083921 10000000000 10192447992039 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343516943/10000000000 : ℝ), (1284574623/2500000000 : ℝ), (-1584083921/10000000000 : ℝ)] ![(2874577418081/6250000000000 : ℝ), (21907156652881/50000000000000 : ℝ), (10192447992039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343516943/10000000000 : ℝ)|^5303 ≤ (2874577418081/6250000000000 : ℝ)^4279
        have hw : |(5343516943/10000000000 : ℝ)|=(5343516943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284574623/2500000000 : ℝ)|^5303 ≤ (21907156652881/50000000000000 : ℝ)^4279
        have hw : |(1284574623/2500000000 : ℝ)|=(1284574623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1584083921/10000000000 : ℝ)|^5303 ≤ (10192447992039/100000000000000 : ℝ)^4279
        have hw : |(-1584083921/10000000000 : ℝ)|=(1584083921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205235373/500000000 : ℝ)*x 0 + (5690077/15625000 : ℝ)*x 1 + (460340129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205235373/500000000 : ℝ)^5303 ≤ (16584693803937/50000000000000 : ℝ)^4279 := by
    have hnat : (205235373 : ℕ)^5303*50000000000000^4279 ≤ 16584693803937^4279*500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205235373 500000000 16584693803937 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690077/15625000 : ℝ)^5303 ≤ (28596516848349/100000000000000 : ℝ)^4279 := by
    have hnat : (5690077 : ℕ)^5303*100000000000000^4279 ≤ 28596516848349^4279*15625000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690077 15625000 28596516848349 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460340129/1000000000 : ℝ)^5303 ≤ (305872764187/800000000000 : ℝ)^4279 := by
    have hnat : (460340129 : ℕ)^5303*800000000000^4279 ≤ 305872764187^4279*1000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460340129 1000000000 305872764187 800000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205235373/500000000 : ℝ), (5690077/15625000 : ℝ), (460340129/1000000000 : ℝ)] ![(16584693803937/50000000000000 : ℝ), (28596516848349/100000000000000 : ℝ), (305872764187/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205235373/500000000 : ℝ)|^5303 ≤ (16584693803937/50000000000000 : ℝ)^4279
        have hw : |(205235373/500000000 : ℝ)|=(205235373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690077/15625000 : ℝ)|^5303 ≤ (28596516848349/100000000000000 : ℝ)^4279
        have hw : |(5690077/15625000 : ℝ)|=(5690077/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460340129/1000000000 : ℝ)|^5303 ≤ (305872764187/800000000000 : ℝ)^4279
        have hw : |(460340129/1000000000 : ℝ)|=(460340129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-706112663/5000000000 : ℝ)*x 0 + (1285493039/2500000000 : ℝ)*x 1 + (683287073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (706112663/5000000000 : ℝ)^5303 ≤ (4420170412027/50000000000000 : ℝ)^4279 := by
    have hnat : (706112663 : ℕ)^5303*50000000000000^4279 ≤ 4420170412027^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706112663 5000000000 4420170412027 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285493039/2500000000 : ℝ)^5303 ≤ (2192656920353/5000000000000 : ℝ)^4279 := by
    have hnat : (1285493039 : ℕ)^5303*5000000000000^4279 ≤ 2192656920353^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285493039 2500000000 2192656920353 5000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683287073/1250000000 : ℝ)^5303 ≤ (47306520754459/100000000000000 : ℝ)^4279 := by
    have hnat : (683287073 : ℕ)^5303*100000000000000^4279 ≤ 47306520754459^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683287073 1250000000 47306520754459 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-706112663/5000000000 : ℝ), (1285493039/2500000000 : ℝ), (683287073/1250000000 : ℝ)] ![(4420170412027/50000000000000 : ℝ), (2192656920353/5000000000000 : ℝ), (47306520754459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-706112663/5000000000 : ℝ)|^5303 ≤ (4420170412027/50000000000000 : ℝ)^4279
        have hw : |(-706112663/5000000000 : ℝ)|=(706112663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285493039/2500000000 : ℝ)|^5303 ≤ (2192656920353/5000000000000 : ℝ)^4279
        have hw : |(1285493039/2500000000 : ℝ)|=(1285493039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683287073/1250000000 : ℝ)|^5303 ≤ (47306520754459/100000000000000 : ℝ)^4279
        have hw : |(683287073/1250000000 : ℝ)|=(683287073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_5 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254722969/10000000000 : ℝ)*x 0 + (-1256085841/10000000000 : ℝ)*x 1 + (5466296563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254722969/10000000000 : ℝ)^5303 ≤ (45047956246821/100000000000000 : ℝ)^4279 := by
    have hnat : (5254722969 : ℕ)^5303*100000000000000^4279 ≤ 45047956246821^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254722969 10000000000 45047956246821 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256085841/10000000000 : ℝ)^5303 ≤ (3822761601977/50000000000000 : ℝ)^4279 := by
    have hnat : (1256085841 : ℕ)^5303*50000000000000^4279 ≤ 3822761601977^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256085841 10000000000 3822761601977 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466296563/10000000000 : ℝ)^5303 ≤ (47306520529229/100000000000000 : ℝ)^4279 := by
    have hnat : (5466296563 : ℕ)^5303*100000000000000^4279 ≤ 47306520529229^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466296563 10000000000 47306520529229 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254722969/10000000000 : ℝ), (-1256085841/10000000000 : ℝ), (5466296563/10000000000 : ℝ)] ![(45047956246821/100000000000000 : ℝ), (3822761601977/50000000000000 : ℝ), (47306520529229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254722969/10000000000 : ℝ)|^5303 ≤ (45047956246821/100000000000000 : ℝ)^4279
        have hw : |(5254722969/10000000000 : ℝ)|=(5254722969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1256085841/10000000000 : ℝ)|^5303 ≤ (3822761601977/50000000000000 : ℝ)^4279
        have hw : |(-1256085841/10000000000 : ℝ)|=(1256085841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466296563/10000000000 : ℝ)|^5303 ≤ (47306520529229/100000000000000 : ℝ)^4279
        have hw : |(5466296563/10000000000 : ℝ)|=(5466296563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_6 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627361477/5000000000 : ℝ)*x 0 + (218651863/400000000 : ℝ)*x 1 + (-251217169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627361477/5000000000 : ℝ)^5303 ≤ (9009591217491/20000000000000 : ℝ)^4279 := by
    have hnat : (2627361477 : ℕ)^5303*20000000000000^4279 ≤ 9009591217491^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627361477 5000000000 9009591217491 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218651863/400000000 : ℝ)^5303 ≤ (11826630164483/25000000000000 : ℝ)^4279 := by
    have hnat : (218651863 : ℕ)^5303*25000000000000^4279 ≤ 11826630164483^4279*400000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218651863 400000000 11826630164483 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251217169/2000000000 : ℝ)^5303 ≤ (477845202133/6250000000000 : ℝ)^4279 := by
    have hnat : (251217169 : ℕ)^5303*6250000000000^4279 ≤ 477845202133^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251217169 2000000000 477845202133 6250000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627361477/5000000000 : ℝ), (218651863/400000000 : ℝ), (-251217169/2000000000 : ℝ)] ![(9009591217491/20000000000000 : ℝ), (11826630164483/25000000000000 : ℝ), (477845202133/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627361477/5000000000 : ℝ)|^5303 ≤ (9009591217491/20000000000000 : ℝ)^4279
        have hw : |(2627361477/5000000000 : ℝ)|=(2627361477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218651863/400000000 : ℝ)|^5303 ≤ (11826630164483/25000000000000 : ℝ)^4279
        have hw : |(218651863/400000000 : ℝ)|=(218651863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251217169/2000000000 : ℝ)|^5303 ≤ (477845202133/6250000000000 : ℝ)^4279
        have hw : |(-251217169/2000000000 : ℝ)|=(251217169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s3_7 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2052571707/5000000000 : ℝ)*x 0 + (229637527/500000000 : ℝ)*x 1 + (73049177/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052571707/5000000000 : ℝ)^5303 ≤ (6634750715619/20000000000000 : ℝ)^4279 := by
    have hnat : (2052571707 : ℕ)^5303*20000000000000^4279 ≤ 6634750715619^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052571707 5000000000 6634750715619 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229637527/500000000 : ℝ)^5303 ≤ (38124495360433/100000000000000 : ℝ)^4279 := by
    have hnat : (229637527 : ℕ)^5303*100000000000000^4279 ≤ 38124495360433^4279*500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229637527 500000000 38124495360433 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73049177/200000000 : ℝ)^5303 ≤ (28701751043769/100000000000000 : ℝ)^4279 := by
    have hnat : (73049177 : ℕ)^5303*100000000000000^4279 ≤ 28701751043769^4279*200000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73049177 200000000 28701751043769 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052571707/5000000000 : ℝ), (229637527/500000000 : ℝ), (73049177/200000000 : ℝ)] ![(6634750715619/20000000000000 : ℝ), (38124495360433/100000000000000 : ℝ), (28701751043769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052571707/5000000000 : ℝ)|^5303 ≤ (6634750715619/20000000000000 : ℝ)^4279
        have hw : |(2052571707/5000000000 : ℝ)|=(2052571707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229637527/500000000 : ℝ)|^5303 ≤ (38124495360433/100000000000000 : ℝ)^4279
        have hw : |(229637527/500000000 : ℝ)|=(229637527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73049177/200000000 : ℝ)|^5303 ≤ (28701751043769/100000000000000 : ℝ)^4279
        have hw : |(73049177/200000000 : ℝ)|=(73049177/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1001/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1069/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1069/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1069/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1069/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1069/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1069/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10001/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (27001389388169/4000000000000000000 : ℝ) := by
    have hpowers : (10001/100000 : ℝ)^5295 ≤ (27001389388169/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10001 : ℕ)^5295*4000000000000000000^1024 ≤ 27001389388169^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001 100000 27001389388169 4000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10001/100000 : ℝ)) (X := (27001389388169/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1069/6250 : ℝ) ^ (5295/1024 : ℝ) ≤ (216499066512267/2000000000000000000 : ℝ) := by
    have hpowers : (1069/6250 : ℝ)^5295 ≤ (216499066512267/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1069 : ℕ)^5295*2000000000000000000^1024 ≤ 216499066512267^1024*6250^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1069 6250 216499066512267 2000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1069/6250 : ℝ)) (X := (216499066512267/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000027001389388169/2000000000000000000 : ℝ) ≤ (2000005221770007/2000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (2000027001389388169/2000000000000000000 : ℝ)^1024 ≤ (2000005221770007/2000000000000000 : ℝ)^5295 := by
      have hnat : (2000027001389388169 : ℕ)^1024*2000000000000000^5295 ≤ 2000005221770007^5295*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000027001389388169 2000000000000000000 2000005221770007 2000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005221770007/2000000000000000 : ℝ)) (X := (2000027001389388169/2000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000459999522412703/4000000000000000000 : ℝ) ≤ (10000222387944117/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (4000459999522412703/4000000000000000000 : ℝ)^1024 ≤ (10000222387944117/10000000000000000 : ℝ)^5295 := by
      have hnat : (4000459999522412703 : ℕ)^1024*10000000000000000^5295 ≤ 10000222387944117^5295*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000459999522412703 4000000000000000000 10000222387944117 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000222387944117/10000000000000000 : ℝ)) (X := (4000459999522412703/4000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000216499066512267/1000000000000000000 : ℝ) ≤ (10000418667038199/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (1000216499066512267/1000000000000000000 : ℝ)^1024 ≤ (10000418667038199/10000000000000000 : ℝ)^5295 := by
      have hnat : (1000216499066512267 : ℕ)^1024*10000000000000000^5295 ≤ 10000418667038199^5295*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000216499066512267 1000000000000000000 10000418667038199 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000418667038199/10000000000000000 : ℝ)) (X := (1000216499066512267/1000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27001389388169/4000000000000000000 : ℝ) ≤ ((71026259476721970441/71030000000000000000 : ℝ)+2*(98139547041/355150000000000 : ℝ)*(10001/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (71026259476721970441/71030000000000000000 : ℝ)+2*(98139547041/355150000000000 : ℝ)*(10001/100000 : ℝ)=(2000005221770007/2000000000000000 : ℝ) by norm_num, show 1+2*(27001389388169/4000000000000000000 : ℝ)=(2000027001389388169/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(216499066512267/2000000000000000000 : ℝ)+(27001389388169/4000000000000000000 : ℝ) ≤ ((71026259476721970441/71030000000000000000 : ℝ)+(98139547041/355150000000000 : ℝ)*((1069/6250 : ℝ)+(10001/100000 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (71026259476721970441/71030000000000000000 : ℝ)+(98139547041/355150000000000 : ℝ)*((1069/6250 : ℝ)+(10001/100000 : ℝ))=(10000222387944117/10000000000000000 : ℝ) by norm_num, show 1+(216499066512267/2000000000000000000 : ℝ)+(27001389388169/4000000000000000000 : ℝ)=(4000459999522412703/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(216499066512267/2000000000000000000 : ℝ) ≤ ((71026259476721970441/71030000000000000000 : ℝ)+2*(98139547041/355150000000000 : ℝ)*(1069/6250 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (71026259476721970441/71030000000000000000 : ℝ)+2*(98139547041/355150000000000 : ℝ)*(1069/6250 : ℝ)=(10000418667038199/10000000000000000 : ℝ) by norm_num, show 1+2*(216499066512267/2000000000000000000 : ℝ)=(1000216499066512267/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71026259476721970441/71030000000000000000 : ℝ)*(X 1 0+X 2 0)+(98139547041/355150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10001/100000 : ℝ)) (hi := (1069/6250 : ℝ)) (c := (71026259476721970441/71030000000000000000 : ℝ)) (alpha := (98139547041/355150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71026259476721970441/71030000000000000000 : ℝ)*(X 0 1+X 2 1)+(98139547041/355150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10001/100000 : ℝ)) (hi := (1069/6250 : ℝ)) (c := (71026259476721970441/71030000000000000000 : ℝ)) (alpha := (98139547041/355150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71026259476721970441/71030000000000000000 : ℝ)*(X 0 2+X 1 2)+(98139547041/355150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10001/100000 : ℝ)) (hi := (1069/6250 : ℝ)) (c := (71026259476721970441/71030000000000000000 : ℝ)) (alpha := (98139547041/355150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-706037481/5000000000 : ℝ)*X 0 0+(5470025003/10000000000 : ℝ)*X 0 1+(642287313/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343516981/10000000000 : ℝ)*X 1 0+(-1584083897/10000000000 : ℝ)*X 1 1+(642287309/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343516943/10000000000 : ℝ)*X 2 0+(1284574623/2500000000 : ℝ)*X 2 1+(-1584083921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((205235373/500000000 : ℝ)*X 0 0+(5690077/15625000 : ℝ)*X 0 1+(460340129/1000000000 : ℝ)*X 0 2+(205235373/500000000 : ℝ)*X 1 0+(5690077/15625000 : ℝ)*X 1 1+(460340129/1000000000 : ℝ)*X 1 2+(205235373/500000000 : ℝ)*X 2 0+(5690077/15625000 : ℝ)*X 2 1+(460340129/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-706112663/5000000000 : ℝ)*X 0 0+(1285493039/2500000000 : ℝ)*X 0 1+(683287073/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254722969/10000000000 : ℝ)*X 1 0+(-1256085841/10000000000 : ℝ)*X 1 1+(5466296563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627361477/5000000000 : ℝ)*X 2 0+(218651863/400000000 : ℝ)*X 2 1+(-251217169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2052571707/5000000000 : ℝ)*X 0 0+(229637527/500000000 : ℝ)*X 0 1+(73049177/200000000 : ℝ)*X 0 2+(2052571707/5000000000 : ℝ)*X 1 0+(229637527/500000000 : ℝ)*X 1 1+(73049177/200000000 : ℝ)*X 1 2+(2052571707/5000000000 : ℝ)*X 2 0+(229637527/500000000 : ℝ)*X 2 1+(73049177/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55846935556175054120667/4439375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1897974969/100000000000000 : ℝ)*(base19) + (1770554707/100000000000000 : ℝ)*(base23) + (56631879/100000000000000 : ℝ)*(lower2) + (157243213/50000000000000 : ℝ)*(upper3) + (44157071/20000000000000 : ℝ)*(upper5) + (2027175634437179/100000000000000 : ℝ)*(major0) + (2027175634437179/100000000000000 : ℝ)*(major1) + (2027175634437179/100000000000000 : ℝ)*(major2) + (1507275270214271/50000000000000 : ℝ)*(sp0) + (3014566892735231/100000000000000 : ℝ)*(sp1) + (3014567020155493/100000000000000 : ℝ)*(sp2) + (1039775146341713/100000000000000 : ℝ)*(sp3) + (18250281657/100000000000000 : ℝ)*(sp4) + (6912492121/100000000000000 : ℝ)*(sp7) + (519891029416917/50000000000000 : ℝ)*(f.failure) + (15072843953551/500000000000 : ℝ)*(f.sum) + (59324136604179/17757500000000000000000000000 : ℝ)*base65 + (59356235170283225939/7103000000000000000000000000000000 : ℝ)*base67 + (2840483817650774061/7103000000000000000000000000000000 : ℝ)*base70 + (7056934339822225939/7103000000000000000000000000000000 : ℝ)*base71 + (147631095681583/35515000000000000000000000000 : ℝ)*base73 + (58054987885778774061/7103000000000000000000000000000000 : ℝ)*base76 + (28688692614158225939/7103000000000000000000000000000000 : ℝ)*base77 + (59697420854830774061/7103000000000000000000000000000000 : ℝ)*base80 + (8221715492327/35515000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3878197/500000000000000000000 : ℝ)*base90 + (3878197/500000000000000000000 : ℝ)*base92 + (3878197/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8633588222740722958171931841/887875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135326117/10000000000000 : ℝ)*(base19) + (36080403/2500000000000 : ℝ)*(base23) + (199805983/50000000000000 : ℝ)*(lower1) + (51860389/25000000000000 : ℝ)*(upper3) + (44586531/100000000000000 : ℝ)*(lower4) + (101371197/50000000000000 : ℝ)*(upper5) + (518351882571533/25000000000000 : ℝ)*(major0) + (518351882571533/25000000000000 : ℝ)*(major1) + (518351882571533/25000000000000 : ℝ)*(major2) + (822946633/100000000000000 : ℝ)*(sp2) + (1541659671076079/50000000000000 : ℝ)*(sp4) + (770829497222747/25000000000000 : ℝ)*(sp5) + (770829268997351/25000000000000 : ℝ)*(sp6) + (106349539429081/10000000000000 : ℝ)*(sp7) + (106349539429081/10000000000000 : ℝ)*(f.failure) + (1541659671076079/50000000000000 : ℝ)*(f.sum) + (7142963382583/1109843750000000000000000000 : ℝ)*base66 + (43590878668071343947/1775750000000000000000000000000000 : ℝ)*base68 + (11130905511785656053/1775750000000000000000000000000000 : ℝ)*base69 + (156947795355669343947/1775750000000000000000000000000000 : ℝ)*base72 + (59151766535639/8878750000000000000000000000 : ℝ)*base74 + (203973012077006656053/1775750000000000000000000000000000 : ℝ)*base75 + (5357212600783406053/1775750000000000000000000000000000 : ℝ)*base77 + (21027676358662656053/1775750000000000000000000000000000 : ℝ)*base79 + (34958494549581/35515000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (399879/100000000000000000000 : ℝ)*base89 + (399879/100000000000000000000 : ℝ)*base91 + (399879/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1710_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1001/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1710_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1710_s4_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1412080041/10000000000 : ℝ)*x 0 + (1367501733/2500000000 : ℝ)*x 1 + (32114457/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1412080041/10000000000 : ℝ)^5303 ≤ (8839213730969/100000000000000 : ℝ)^4279 := by
    have hnat : (1412080041 : ℕ)^5303*100000000000000^4279 ≤ 8839213730969^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412080041 10000000000 8839213730969 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367501733/2500000000 : ℝ)^5303 ≤ (23673159185673/50000000000000 : ℝ)^4279 := by
    have hnat : (1367501733 : ℕ)^5303*50000000000000^4279 ≤ 23673159185673^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367501733 2500000000 23673159185673 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32114457/62500000 : ℝ)^5303 ≤ (8762893577709/20000000000000 : ℝ)^4279 := by
    have hnat : (32114457 : ℕ)^5303*20000000000000^4279 ≤ 8762893577709^4279*62500000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32114457 62500000 8762893577709 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1412080041/10000000000 : ℝ), (1367501733/2500000000 : ℝ), (32114457/62500000 : ℝ)] ![(8839213730969/100000000000000 : ℝ), (23673159185673/50000000000000 : ℝ), (8762893577709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1412080041/10000000000 : ℝ)|^5303 ≤ (8839213730969/100000000000000 : ℝ)^4279
        have hw : |(-1412080041/10000000000 : ℝ)|=(1412080041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367501733/2500000000 : ℝ)|^5303 ≤ (23673159185673/50000000000000 : ℝ)^4279
        have hw : |(1367501733/2500000000 : ℝ)|=(1367501733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32114457/62500000 : ℝ)|^5303 ≤ (8762893577709/20000000000000 : ℝ)^4279
        have hw : |(32114457/62500000 : ℝ)|=(32114457/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s4_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343511403/10000000000 : ℝ)*x 0 + (-792035081/5000000000 : ℝ)*x 1 + (2569157233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343511403/10000000000 : ℝ)^5303 ≤ (14372868623/31250000000 : ℝ)^4279 := by
    have hnat : (5343511403 : ℕ)^5303*31250000000^4279 ≤ 14372868623^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343511403 10000000000 14372868623 31250000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (792035081/5000000000 : ℝ)^5303 ≤ (10192338277021/100000000000000 : ℝ)^4279 := by
    have hnat : (792035081 : ℕ)^5303*100000000000000^4279 ≤ 10192338277021^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792035081 5000000000 10192338277021 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569157233/5000000000 : ℝ)^5303 ≤ (43814482112533/100000000000000 : ℝ)^4279 := by
    have hnat : (2569157233 : ℕ)^5303*100000000000000^4279 ≤ 43814482112533^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569157233 5000000000 43814482112533 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343511403/10000000000 : ℝ), (-792035081/5000000000 : ℝ), (2569157233/5000000000 : ℝ)] ![(14372868623/31250000000 : ℝ), (10192338277021/100000000000000 : ℝ), (43814482112533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343511403/10000000000 : ℝ)|^5303 ≤ (14372868623/31250000000 : ℝ)^4279
        have hw : |(5343511403/10000000000 : ℝ)|=(5343511403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-792035081/5000000000 : ℝ)|^5303 ≤ (10192338277021/100000000000000 : ℝ)^4279
        have hw : |(-792035081/5000000000 : ℝ)|=(792035081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569157233/5000000000 : ℝ)|^5303 ≤ (43814482112533/100000000000000 : ℝ)^4279
        have hw : |(2569157233/5000000000 : ℝ)|=(2569157233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s4_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213740481/400000000 : ℝ)*x 0 + (5138313397/10000000000 : ℝ)*x 1 + (-1584070747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213740481/400000000 : ℝ)^5303 ≤ (45993186228531/100000000000000 : ℝ)^4279 := by
    have hnat : (213740481 : ℕ)^5303*100000000000000^4279 ≤ 45993186228531^4279*400000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213740481 400000000 45993186228531 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138313397/10000000000 : ℝ)^5303 ≤ (4381447081577/10000000000000 : ℝ)^4279 := by
    have hnat : (5138313397 : ℕ)^5303*10000000000000^4279 ≤ 4381447081577^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138313397 10000000000 4381447081577 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584070747/10000000000 : ℝ)^5303 ≤ (10192342941839/100000000000000 : ℝ)^4279 := by
    have hnat : (1584070747 : ℕ)^5303*100000000000000^4279 ≤ 10192342941839^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584070747 10000000000 10192342941839 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213740481/400000000 : ℝ), (5138313397/10000000000 : ℝ), (-1584070747/10000000000 : ℝ)] ![(45993186228531/100000000000000 : ℝ), (4381447081577/10000000000000 : ℝ), (10192342941839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213740481/400000000 : ℝ)|^5303 ≤ (45993186228531/100000000000000 : ℝ)^4279
        have hw : |(213740481/400000000 : ℝ)|=(213740481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138313397/10000000000 : ℝ)|^5303 ≤ (4381447081577/10000000000000 : ℝ)^4279
        have hw : |(5138313397/10000000000 : ℝ)|=(5138313397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1584070747/10000000000 : ℝ)|^5303 ≤ (10192342941839/100000000000000 : ℝ)^4279
        have hw : |(-1584070747/10000000000 : ℝ)|=(1584070747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s4_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2052355281/5000000000 : ℝ)*x 0 + (364169669/1000000000 : ℝ)*x 1 + (575419181/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052355281/5000000000 : ℝ)^5303 ≤ (8292354668309/25000000000000 : ℝ)^4279 := by
    have hnat : (2052355281 : ℕ)^5303*25000000000000^4279 ≤ 8292354668309^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052355281 5000000000 8292354668309 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364169669/1000000000 : ℝ)^5303 ≤ (14298489117483/50000000000000 : ℝ)^4279 := by
    have hnat : (364169669 : ℕ)^5303*50000000000000^4279 ≤ 14298489117483^4279*1000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364169669 1000000000 14298489117483 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575419181/1250000000 : ℝ)^5303 ≤ (9558400768919/25000000000000 : ℝ)^4279 := by
    have hnat : (575419181 : ℕ)^5303*25000000000000^4279 ≤ 9558400768919^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575419181 1250000000 9558400768919 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052355281/5000000000 : ℝ), (364169669/1000000000 : ℝ), (575419181/1250000000 : ℝ)] ![(8292354668309/25000000000000 : ℝ), (14298489117483/50000000000000 : ℝ), (9558400768919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052355281/5000000000 : ℝ)|^5303 ≤ (8292354668309/25000000000000 : ℝ)^4279
        have hw : |(2052355281/5000000000 : ℝ)|=(2052355281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364169669/1000000000 : ℝ)|^5303 ≤ (14298489117483/50000000000000 : ℝ)^4279
        have hw : |(364169669/1000000000 : ℝ)|=(364169669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(575419181/1250000000 : ℝ)|^5303 ≤ (9558400768919/25000000000000 : ℝ)^4279
        have hw : |(575419181/1250000000 : ℝ)|=(575419181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s4_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1412230183/10000000000 : ℝ)*x 0 + (5141986443/10000000000 : ℝ)*x 1 + (5466278991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1412230183/10000000000 : ℝ)^5303 ≤ (1768075700841/20000000000000 : ℝ)^4279 := by
    have hnat : (1412230183 : ℕ)^5303*20000000000000^4279 ≤ 1768075700841^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412230183 10000000000 1768075700841 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141986443/10000000000 : ℝ)^5303 ≤ (10963322353029/25000000000000 : ℝ)^4279 := by
    have hnat : (5141986443 : ℕ)^5303*25000000000000^4279 ≤ 10963322353029^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141986443 10000000000 10963322353029 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466278991/10000000000 : ℝ)^5303 ≤ (11826583016331/25000000000000 : ℝ)^4279 := by
    have hnat : (5466278991 : ℕ)^5303*25000000000000^4279 ≤ 11826583016331^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466278991 10000000000 11826583016331 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1412230183/10000000000 : ℝ), (5141986443/10000000000 : ℝ), (5466278991/10000000000 : ℝ)] ![(1768075700841/20000000000000 : ℝ), (10963322353029/25000000000000 : ℝ), (11826583016331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1412230183/10000000000 : ℝ)|^5303 ≤ (1768075700841/20000000000000 : ℝ)^4279
        have hw : |(-1412230183/10000000000 : ℝ)|=(1412230183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141986443/10000000000 : ℝ)|^5303 ≤ (10963322353029/25000000000000 : ℝ)^4279
        have hw : |(5141986443/10000000000 : ℝ)|=(5141986443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466278991/10000000000 : ℝ)|^5303 ≤ (11826583016331/25000000000000 : ℝ)^4279
        have hw : |(5466278991/10000000000 : ℝ)|=(5466278991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s4_5 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254726821/10000000000 : ℝ)*x 0 + (218651157/400000000 : ℝ)*x 1 + (-628052747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254726821/10000000000 : ℝ)^5303 ≤ (703874955813/1562500000000 : ℝ)^4279 := by
    have hnat : (5254726821 : ℕ)^5303*1562500000000^4279 ≤ 703874955813^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254726821 10000000000 703874955813 1562500000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218651157/400000000 : ℝ)^5303 ≤ (47306331357459/100000000000000 : ℝ)^4279 := by
    have hnat : (218651157 : ℕ)^5303*100000000000000^4279 ≤ 47306331357459^4279*400000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218651157 400000000 47306331357459 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628052747/5000000000 : ℝ)^5303 ≤ (477854465919/6250000000000 : ℝ)^4279 := by
    have hnat : (628052747 : ℕ)^5303*6250000000000^4279 ≤ 477854465919^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628052747 5000000000 477854465919 6250000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254726821/10000000000 : ℝ), (218651157/400000000 : ℝ), (-628052747/5000000000 : ℝ)] ![(703874955813/1562500000000 : ℝ), (47306331357459/100000000000000 : ℝ), (477854465919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254726821/10000000000 : ℝ)|^5303 ≤ (703874955813/1562500000000 : ℝ)^4279
        have hw : |(5254726821/10000000000 : ℝ)|=(5254726821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218651157/400000000 : ℝ)|^5303 ≤ (47306331357459/100000000000000 : ℝ)^4279
        have hw : |(218651157/400000000 : ℝ)|=(218651157/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-628052747/5000000000 : ℝ)|^5303 ≤ (477854465919/6250000000000 : ℝ)^4279
        have hw : |(-628052747/5000000000 : ℝ)|=(628052747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s4_6 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4105146539/10000000000 : ℝ)*x 0 + (4592703849/10000000000 : ℝ)*x 1 + (1826252479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4105146539/10000000000 : ℝ)^5303 ≤ (8293446218647/25000000000000 : ℝ)^4279 := by
    have hnat : (4105146539 : ℕ)^5303*25000000000000^4279 ≤ 8293446218647^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4105146539 10000000000 8293446218647 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4592703849/10000000000 : ℝ)^5303 ≤ (38124015026537/100000000000000 : ℝ)^4279 := by
    have hnat : (4592703849 : ℕ)^5303*100000000000000^4279 ≤ 38124015026537^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592703849 10000000000 38124015026537 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1826252479/5000000000 : ℝ)^5303 ≤ (28702200077889/100000000000000 : ℝ)^4279 := by
    have hnat : (1826252479 : ℕ)^5303*100000000000000^4279 ≤ 28702200077889^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826252479 5000000000 28702200077889 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4105146539/10000000000 : ℝ), (4592703849/10000000000 : ℝ), (1826252479/5000000000 : ℝ)] ![(8293446218647/25000000000000 : ℝ), (38124015026537/100000000000000 : ℝ), (28702200077889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4105146539/10000000000 : ℝ)|^5303 ≤ (8293446218647/25000000000000 : ℝ)^4279
        have hw : |(4105146539/10000000000 : ℝ)|=(4105146539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4592703849/10000000000 : ℝ)|^5303 ≤ (38124015026537/100000000000000 : ℝ)^4279
        have hw : |(4592703849/10000000000 : ℝ)|=(4592703849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1826252479/5000000000 : ℝ)|^5303 ≤ (28702200077889/100000000000000 : ℝ)^4279
        have hw : |(1826252479/5000000000 : ℝ)|=(1826252479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1001/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1001/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1001/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1001/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1001/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1001/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1001/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1001/10000 : ℝ) ^ (5295/1024 : ℝ) ≤ (339090901864831/50000000000000000000 : ℝ) := by
    have hpowers : (1001/10000 : ℝ)^5295 ≤ (339090901864831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1001 : ℕ)^5295*50000000000000000000^1024 ≤ 339090901864831^1024*10000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001 10000 339090901864831 50000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1001/10000 : ℝ)) (X := (339090901864831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17093/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (10789002856174561/100000000000000000000 : ℝ) := by
    have hpowers : (17093/100000 : ℝ)^5295 ≤ (10789002856174561/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17093 : ℕ)^5295*100000000000000000000^1024 ≤ 10789002856174561^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17093 100000 10789002856174561 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17093/100000 : ℝ)) (X := (10789002856174561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000339090901864831/25000000000000000000 : ℝ) ≤ (2500006557642759/2500000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (25000339090901864831/25000000000000000000 : ℝ)^1024 ≤ (2500006557642759/2500000000000000 : ℝ)^5295 := by
      have hnat : (25000339090901864831 : ℕ)^1024*2500000000000000^5295 ≤ 2500006557642759^5295*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000339090901864831 25000000000000000000 2500006557642759 2500000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500006557642759/2500000000000000 : ℝ)) (X := (25000339090901864831/25000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011467184659904223/100000000000000000000 : ℝ) ≤ (10000221753617943/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (100011467184659904223/100000000000000000000 : ℝ)^1024 ≤ (10000221753617943/10000000000000000 : ℝ)^5295 := by
      have hnat : (100011467184659904223 : ℕ)^1024*10000000000000000^5295 ≤ 10000221753617943^5295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011467184659904223 100000000000000000000 10000221753617943 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000221753617943/10000000000000000 : ℝ)) (X := (100011467184659904223/100000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010789002856174561/50000000000000000000 : ℝ) ≤ (200008345533297/200000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50010789002856174561/50000000000000000000 : ℝ)^1024 ≤ (200008345533297/200000000000000 : ℝ)^5295 := by
      have hnat : (50010789002856174561 : ℕ)^1024*200000000000000^5295 ≤ 200008345533297^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010789002856174561 50000000000000000000 200008345533297 200000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200008345533297/200000000000000 : ℝ)) (X := (50010789002856174561/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(339090901864831/50000000000000000000 : ℝ) ≤ ((2951094642488982077/2951250000000000000 : ℝ)+2*(65174348969/236100000000000 : ℝ)*(1001/10000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (2951094642488982077/2951250000000000000 : ℝ)+2*(65174348969/236100000000000 : ℝ)*(1001/10000 : ℝ)=(2500006557642759/2500000000000000 : ℝ) by norm_num, show 1+2*(339090901864831/50000000000000000000 : ℝ)=(25000339090901864831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10789002856174561/100000000000000000000 : ℝ)+(339090901864831/50000000000000000000 : ℝ) ≤ ((2951094642488982077/2951250000000000000 : ℝ)+(65174348969/236100000000000 : ℝ)*((17093/100000 : ℝ)+(1001/10000 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (2951094642488982077/2951250000000000000 : ℝ)+(65174348969/236100000000000 : ℝ)*((17093/100000 : ℝ)+(1001/10000 : ℝ))=(10000221753617943/10000000000000000 : ℝ) by norm_num, show 1+(10789002856174561/100000000000000000000 : ℝ)+(339090901864831/50000000000000000000 : ℝ)=(100011467184659904223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10789002856174561/100000000000000000000 : ℝ) ≤ ((2951094642488982077/2951250000000000000 : ℝ)+2*(65174348969/236100000000000 : ℝ)*(17093/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (2951094642488982077/2951250000000000000 : ℝ)+2*(65174348969/236100000000000 : ℝ)*(17093/100000 : ℝ)=(200008345533297/200000000000000 : ℝ) by norm_num, show 1+2*(10789002856174561/100000000000000000000 : ℝ)=(50010789002856174561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2951094642488982077/2951250000000000000 : ℝ)*(X 1 0+X 2 0)+(65174348969/236100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (1001/10000 : ℝ)) (hi := (17093/100000 : ℝ)) (c := (2951094642488982077/2951250000000000000 : ℝ)) (alpha := (65174348969/236100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2951094642488982077/2951250000000000000 : ℝ)*(X 0 1+X 2 1)+(65174348969/236100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (1001/10000 : ℝ)) (hi := (17093/100000 : ℝ)) (c := (2951094642488982077/2951250000000000000 : ℝ)) (alpha := (65174348969/236100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2951094642488982077/2951250000000000000 : ℝ)*(X 0 2+X 1 2)+(65174348969/236100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (1001/10000 : ℝ)) (hi := (17093/100000 : ℝ)) (c := (2951094642488982077/2951250000000000000 : ℝ)) (alpha := (65174348969/236100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1412080041/10000000000 : ℝ)*X 0 0+(1367501733/2500000000 : ℝ)*X 0 1+(32114457/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343511403/10000000000 : ℝ)*X 1 0+(-792035081/5000000000 : ℝ)*X 1 1+(2569157233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213740481/400000000 : ℝ)*X 2 0+(5138313397/10000000000 : ℝ)*X 2 1+(-1584070747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2052355281/5000000000 : ℝ)*X 0 0+(364169669/1000000000 : ℝ)*X 0 1+(575419181/1250000000 : ℝ)*X 0 2+(2052355281/5000000000 : ℝ)*X 1 0+(364169669/1000000000 : ℝ)*X 1 1+(575419181/1250000000 : ℝ)*X 1 2+(2052355281/5000000000 : ℝ)*X 2 0+(364169669/1000000000 : ℝ)*X 2 1+(575419181/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1412230183/10000000000 : ℝ)*X 0 0+(5141986443/10000000000 : ℝ)*X 0 1+(5466278991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254726821/10000000000 : ℝ)*X 2 0+(218651157/400000000 : ℝ)*X 2 1+(-628052747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4105146539/10000000000 : ℝ)*X 0 0+(4592703849/10000000000 : ℝ)*X 0 1+(1826252479/5000000000 : ℝ)*X 0 2+(4105146539/10000000000 : ℝ)*X 1 0+(4592703849/10000000000 : ℝ)*X 1 1+(1826252479/5000000000 : ℝ)*X 1 2+(4105146539/10000000000 : ℝ)*X 2 0+(4592703849/10000000000 : ℝ)*X 2 1+(1826252479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (220157499942978716457421289/49187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582209033/100000000000000 : ℝ)*(base19) + (479387529/50000000000000 : ℝ)*(base23) + (25888139/100000000000000 : ℝ)*(upper2) + (51343879/25000000000000 : ℝ)*(upper3) + (2027372042201581/100000000000000 : ℝ)*(major0) + (2027372042201581/100000000000000 : ℝ)*(major1) + (2027372042201581/100000000000000 : ℝ)*(major2) + (60296927858553/2000000000000 : ℝ)*(sp0) + (753715138097543/25000000000000 : ℝ)*(sp1) + (1507429401200947/50000000000000 : ℝ)*(sp2) + (1039876669892167/100000000000000 : ℝ)*(sp3) + (2948334311/20000000000000 : ℝ)*(sp4) + (1373422253/100000000000000 : ℝ)*(sp5) + (1532678919/25000000000000 : ℝ)*(sp6) + (1039882800607843/100000000000000 : ℝ)*(f.failure) + (1507430567299603/50000000000000 : ℝ)*(f.sum) + (10627430154787/5902500000000000000000000000 : ℝ)*base65 + (269028618257517079/98375000000000000000000000000000 : ℝ)*base67 + (1086704932873767079/98375000000000000000000000000000 : ℝ)*base69 + (373780117044392079/98375000000000000000000000000000 : ℝ)*base71 + (2574491783461/11805000000000000000000000000 : ℝ)*base74 + (187630314287642079/98375000000000000000000000000000 : ℝ)*base75 + (778889178933267079/98375000000000000000000000000000 : ℝ)*base77 + (251803817034267079/98375000000000000000000000000000 : ℝ)*base79 + (45063472103669/11805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6224963/1000000000000000000000 : ℝ)*base90 + (6224963/1000000000000000000000 : ℝ)*base92 + (6224963/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1710_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1001/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1710_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1710_s5_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335877939/2500000000 : ℝ)*x 0 + (-31681399/200000000 : ℝ)*x 1 + (513831427/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335877939/2500000000 : ℝ)^5303 ≤ (45993183359083/100000000000000 : ℝ)^4279 := by
    have hnat : (1335877939 : ℕ)^5303*100000000000000^4279 ≤ 45993183359083^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335877939 2500000000 45993183359083 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31681399/200000000 : ℝ)^5303 ≤ (2548084146631/25000000000000 : ℝ)^4279 := by
    have hnat : (31681399 : ℕ)^5303*25000000000000^4279 ≤ 2548084146631^4279*200000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31681399 200000000 2548084146631 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513831427/1000000000 : ℝ)^5303 ≤ (10953620010321/25000000000000 : ℝ)^4279 := by
    have hnat : (513831427 : ℕ)^5303*25000000000000^4279 ≤ 10953620010321^4279*1000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513831427 1000000000 10953620010321 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335877939/2500000000 : ℝ), (-31681399/200000000 : ℝ), (513831427/1000000000 : ℝ)] ![(45993183359083/100000000000000 : ℝ), (2548084146631/25000000000000 : ℝ), (10953620010321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335877939/2500000000 : ℝ)|^5303 ≤ (45993183359083/100000000000000 : ℝ)^4279
        have hw : |(1335877939/2500000000 : ℝ)|=(1335877939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31681399/200000000 : ℝ)|^5303 ≤ (2548084146631/25000000000000 : ℝ)^4279
        have hw : |(-31681399/200000000 : ℝ)|=(31681399/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513831427/1000000000 : ℝ)|^5303 ≤ (10953620010321/25000000000000 : ℝ)^4279
        have hw : |(513831427/1000000000 : ℝ)|=(513831427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s5_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-706114967/5000000000 : ℝ)*x 0 + (642748381/1250000000 : ℝ)*x 1 + (218651143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (706114967/5000000000 : ℝ)^5303 ≤ (4420188286243/50000000000000 : ℝ)^4279 := by
    have hnat : (706114967 : ℕ)^5303*50000000000000^4279 ≤ 4420188286243^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706114967 5000000000 4420188286243 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642748381/1250000000 : ℝ)^5303 ≤ (43853295806607/100000000000000 : ℝ)^4279 := by
    have hnat : (642748381 : ℕ)^5303*100000000000000^4279 ≤ 43853295806607^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642748381 1250000000 43853295806607 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218651143/400000000 : ℝ)^5303 ≤ (47306327603627/100000000000000 : ℝ)^4279 := by
    have hnat : (218651143 : ℕ)^5303*100000000000000^4279 ≤ 47306327603627^4279*400000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218651143 400000000 47306327603627 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-706114967/5000000000 : ℝ), (642748381/1250000000 : ℝ), (218651143/400000000 : ℝ)] ![(4420188286243/50000000000000 : ℝ), (43853295806607/100000000000000 : ℝ), (47306327603627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-706114967/5000000000 : ℝ)|^5303 ≤ (4420188286243/50000000000000 : ℝ)^4279
        have hw : |(-706114967/5000000000 : ℝ)|=(706114967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642748381/1250000000 : ℝ)|^5303 ≤ (43853295806607/100000000000000 : ℝ)^4279
        have hw : |(642748381/1250000000 : ℝ)|=(642748381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218651143/400000000 : ℝ)|^5303 ≤ (47306327603627/100000000000000 : ℝ)^4279
        have hw : |(218651143/400000000 : ℝ)|=(218651143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s5_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627363551/5000000000 : ℝ)*x 0 + (-628052881/5000000000 : ℝ)*x 1 + (2733139229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627363551/5000000000 : ℝ)^5303 ≤ (4504800015749/10000000000000 : ℝ)^4279 := by
    have hnat : (2627363551 : ℕ)^5303*10000000000000^4279 ≤ 4504800015749^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627363551 5000000000 4504800015749 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628052881/5000000000 : ℝ)^5303 ≤ (7645673476343/100000000000000 : ℝ)^4279 := by
    have hnat : (628052881 : ℕ)^5303*100000000000000^4279 ≤ 7645673476343^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628052881 5000000000 7645673476343 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733139229/5000000000 : ℝ)^5303 ≤ (23653163174387/50000000000000 : ℝ)^4279 := by
    have hnat : (2733139229 : ℕ)^5303*50000000000000^4279 ≤ 23653163174387^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733139229 5000000000 23653163174387 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627363551/5000000000 : ℝ), (-628052881/5000000000 : ℝ), (2733139229/5000000000 : ℝ)] ![(4504800015749/10000000000000 : ℝ), (7645673476343/100000000000000 : ℝ), (23653163174387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627363551/5000000000 : ℝ)|^5303 ≤ (4504800015749/10000000000000 : ℝ)^4279
        have hw : |(2627363551/5000000000 : ℝ)|=(2627363551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-628052881/5000000000 : ℝ)|^5303 ≤ (7645673476343/100000000000000 : ℝ)^4279
        have hw : |(-628052881/5000000000 : ℝ)|=(628052881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733139229/5000000000 : ℝ)|^5303 ≤ (23653163174387/50000000000000 : ℝ)^4279
        have hw : |(2733139229/5000000000 : ℝ)|=(2733139229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s5_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050945423/2000000000 : ℝ)*x 0 + (218651139/400000000 : ℝ)*x 1 + (-31402643/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050945423/2000000000 : ℝ)^5303 ≤ (45048000295607/100000000000000 : ℝ)^4279 := by
    have hnat : (1050945423 : ℕ)^5303*100000000000000^4279 ≤ 45048000295607^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050945423 2000000000 45048000295607 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218651139/400000000 : ℝ)^5303 ≤ (47306326531103/100000000000000 : ℝ)^4279 := by
    have hnat : (218651139 : ℕ)^5303*100000000000000^4279 ≤ 47306326531103^4279*400000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218651139 400000000 47306326531103 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31402643/250000000 : ℝ)^5303 ≤ (7645673159519/100000000000000 : ℝ)^4279 := by
    have hnat : (31402643 : ℕ)^5303*100000000000000^4279 ≤ 7645673159519^4279*250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31402643 250000000 7645673159519 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050945423/2000000000 : ℝ), (218651139/400000000 : ℝ), (-31402643/250000000 : ℝ)] ![(45048000295607/100000000000000 : ℝ), (47306326531103/100000000000000 : ℝ), (7645673159519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050945423/2000000000 : ℝ)|^5303 ≤ (45048000295607/100000000000000 : ℝ)^4279
        have hw : |(1050945423/2000000000 : ℝ)|=(1050945423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218651139/400000000 : ℝ)|^5303 ≤ (47306326531103/100000000000000 : ℝ)^4279
        have hw : |(218651139/400000000 : ℝ)|=(218651139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31402643/250000000 : ℝ)|^5303 ≤ (7645673159519/100000000000000 : ℝ)^4279
        have hw : |(-31402643/250000000 : ℝ)|=(31402643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s5_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4105146787/10000000000 : ℝ)*x 0 + (229635109/500000000 : ℝ)*x 1 + (1826253233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4105146787/10000000000 : ℝ)^5303 ≤ (16586893679139/50000000000000 : ℝ)^4279 := by
    have hnat : (4105146787 : ℕ)^5303*50000000000000^4279 ≤ 16586893679139^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4105146787 10000000000 16586893679139 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229635109/500000000 : ℝ)^5303 ≤ (38123997856713/100000000000000 : ℝ)^4279 := by
    have hnat : (229635109 : ℕ)^5303*100000000000000^4279 ≤ 38123997856713^4279*500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229635109 500000000 38123997856713 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1826253233/5000000000 : ℝ)^5303 ≤ (14351107381971/50000000000000 : ℝ)^4279 := by
    have hnat : (1826253233 : ℕ)^5303*50000000000000^4279 ≤ 14351107381971^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826253233 5000000000 14351107381971 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4105146787/10000000000 : ℝ), (229635109/500000000 : ℝ), (1826253233/5000000000 : ℝ)] ![(16586893679139/50000000000000 : ℝ), (38123997856713/100000000000000 : ℝ), (14351107381971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4105146787/10000000000 : ℝ)|^5303 ≤ (16586893679139/50000000000000 : ℝ)^4279
        have hw : |(4105146787/10000000000 : ℝ)|=(4105146787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229635109/500000000 : ℝ)|^5303 ≤ (38123997856713/100000000000000 : ℝ)^4279
        have hw : |(229635109/500000000 : ℝ)|=(229635109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1826253233/5000000000 : ℝ)|^5303 ≤ (14351107381971/50000000000000 : ℝ)^4279
        have hw : |(1826253233/5000000000 : ℝ)|=(1826253233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4273/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17093/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (10011/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (678532207316381/100000000000000000000 : ℝ) := by
    have hpowers : (10011/100000 : ℝ)^5295 ≤ (678532207316381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10011 : ℕ)^5295*100000000000000000000^1024 ≤ 678532207316381^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011 100000 678532207316381 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10011/100000 : ℝ)) (X := (678532207316381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17093/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (10789002856174561/100000000000000000000 : ℝ) := by
    have hpowers : (17093/100000 : ℝ)^5295 ≤ (10789002856174561/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17093 : ℕ)^5295*100000000000000000000^1024 ≤ 10789002856174561^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17093 100000 10789002856174561 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17093/100000 : ℝ)) (X := (10789002856174561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000678532207316381/50000000000000000000 : ℝ) ≤ (10000026244123797/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50000678532207316381/50000000000000000000 : ℝ)^1024 ≤ (10000026244123797/10000000000000000 : ℝ)^5295 := by
      have hnat : (50000678532207316381 : ℕ)^1024*10000000000000000^5295 ≤ 10000026244123797^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000678532207316381 50000000000000000000 10000026244123797 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026244123797/10000000000000000 : ℝ)) (X := (50000678532207316381/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005733767531745471/50000000000000000000 : ℝ) ≤ (1000022176039377/1000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50005733767531745471/50000000000000000000 : ℝ)^1024 ≤ (1000022176039377/1000000000000000 : ℝ)^5295 := by
      have hnat : (50005733767531745471 : ℕ)^1024*1000000000000000^5295 ≤ 1000022176039377^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005733767531745471 50000000000000000000 1000022176039377 1000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000022176039377/1000000000000000 : ℝ)) (X := (50005733767531745471/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010789002856174561/50000000000000000000 : ℝ) ≤ (10000417276663743/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50010789002856174561/50000000000000000000 : ℝ)^1024 ≤ (10000417276663743/10000000000000000 : ℝ)^5295 := by
      have hnat : (50010789002856174561 : ℕ)^1024*10000000000000000^5295 ≤ 10000417276663743^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010789002856174561 50000000000000000000 10000417276663743 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417276663743/10000000000000000 : ℝ)) (X := (50010789002856174561/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(678532207316381/100000000000000000000 : ℝ) ≤ ((17704067808531832737/17705000000000000000 : ℝ)+2*(195516269973/708200000000000 : ℝ)*(10011/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (17704067808531832737/17705000000000000000 : ℝ)+2*(195516269973/708200000000000 : ℝ)*(10011/100000 : ℝ)=(10000026244123797/10000000000000000 : ℝ) by norm_num, show 1+2*(678532207316381/100000000000000000000 : ℝ)=(50000678532207316381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10789002856174561/100000000000000000000 : ℝ)+(678532207316381/100000000000000000000 : ℝ) ≤ ((17704067808531832737/17705000000000000000 : ℝ)+(195516269973/708200000000000 : ℝ)*((17093/100000 : ℝ)+(10011/100000 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (17704067808531832737/17705000000000000000 : ℝ)+(195516269973/708200000000000 : ℝ)*((17093/100000 : ℝ)+(10011/100000 : ℝ))=(1000022176039377/1000000000000000 : ℝ) by norm_num, show 1+(10789002856174561/100000000000000000000 : ℝ)+(678532207316381/100000000000000000000 : ℝ)=(50005733767531745471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10789002856174561/100000000000000000000 : ℝ) ≤ ((17704067808531832737/17705000000000000000 : ℝ)+2*(195516269973/708200000000000 : ℝ)*(17093/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (17704067808531832737/17705000000000000000 : ℝ)+2*(195516269973/708200000000000 : ℝ)*(17093/100000 : ℝ)=(10000417276663743/10000000000000000 : ℝ) by norm_num, show 1+2*(10789002856174561/100000000000000000000 : ℝ)=(50010789002856174561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17704067808531832737/17705000000000000000 : ℝ)*(X 1 0+X 2 0)+(195516269973/708200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (17093/100000 : ℝ)) (c := (17704067808531832737/17705000000000000000 : ℝ)) (alpha := (195516269973/708200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17704067808531832737/17705000000000000000 : ℝ)*(X 0 1+X 2 1)+(195516269973/708200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (17093/100000 : ℝ)) (c := (17704067808531832737/17705000000000000000 : ℝ)) (alpha := (195516269973/708200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17704067808531832737/17705000000000000000 : ℝ)*(X 0 2+X 1 2)+(195516269973/708200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (17093/100000 : ℝ)) (c := (17704067808531832737/17705000000000000000 : ℝ)) (alpha := (195516269973/708200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1335877939/2500000000 : ℝ)*X 1 0+(-31681399/200000000 : ℝ)*X 1 1+(513831427/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s5_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-706114967/5000000000 : ℝ)*X 0 0+(642748381/1250000000 : ℝ)*X 0 1+(218651143/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2627363551/5000000000 : ℝ)*X 1 0+(-628052881/5000000000 : ℝ)*X 1 1+(2733139229/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050945423/2000000000 : ℝ)*X 2 0+(218651139/400000000 : ℝ)*X 2 1+(-31402643/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4105146787/10000000000 : ℝ)*X 0 0+(229635109/500000000 : ℝ)*X 0 1+(1826253233/5000000000 : ℝ)*X 0 2+(4105146787/10000000000 : ℝ)*X 1 0+(229635109/500000000 : ℝ)*X 1 1+(1826253233/5000000000 : ℝ)*X 1 2+(4105146787/10000000000 : ℝ)*X 2 0+(229635109/500000000 : ℝ)*X 2 1+(1826253233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8552244908027837792882847/3541000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (362911621/100000000000000 : ℝ)*(base19) + (401272857/100000000000000 : ℝ)*(base23) + (47020693/50000000000000 : ℝ)*(lower1) + (31748389/100000000000000 : ℝ)*(upper3) + (1687067/10000000000000 : ℝ)*(lower4) + (42437881/50000000000000 : ℝ)*(upper5) + (8294500390323/400000000000 : ℝ)*(major0) + (8294500390323/400000000000 : ℝ)*(major1) + (8294500390323/400000000000 : ℝ)*(major2) + (81277927/100000000000000 : ℝ)*(sp0) + (308364312541087/10000000000000 : ℝ)*(sp1) + (3083642681221321/100000000000000 : ℝ)*(sp2) + (770910681034503/25000000000000 : ℝ)*(sp3) + (1063606989243753/100000000000000 : ℝ)*(sp4) + (1063606989243753/100000000000000 : ℝ)*(f.failure) + (308364312541087/10000000000000 : ℝ)*(f.sum) + (1557834705801/885250000000000000000000000 : ℝ)*base65 + (29815245119220949/7082000000000000000000000000000 : ℝ)*base68 + (43490047810756949/7082000000000000000000000000000 : ℝ)*base70 + (4150523576849051/7082000000000000000000000000000 : ℝ)*base71 + (9186844186167/3541000000000000000000000000 : ℝ)*base73 + (73365706676487051/7082000000000000000000000000000 : ℝ)*base75 + (30270045601117051/7082000000000000000000000000000 : ℝ)*base77 + (7673463945699051/7082000000000000000000000000000 : ℝ)*base79 + (196246229603/3541000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1755273/1000000000000000000000 : ℝ)*base90 + (1755273/1000000000000000000000 : ℝ)*base92 + (1755273/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1710_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1710_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1710_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1710_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1710_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1710_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
