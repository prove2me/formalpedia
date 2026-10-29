-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1589_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:23.367592+00:00
-- url     : https://prove2.me/submissions/9cfe6c41-9e79-4ad5-acba-297f38412a88

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
theorem support_rectangle_w1589_s0_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1607122953/10000000000 : ℝ)*x 0 + (5855951877/10000000000 : ℝ)*x 1 + (4886891459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1607122953/10000000000 : ℝ)^4675 ≤ (9624292632229/100000000000000 : ℝ)^3651 := by
    have hnat : (1607122953 : ℕ)^4675*100000000000000^3651 ≤ 9624292632229^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607122953 10000000000 9624292632229 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5855951877/10000000000 : ℝ)^4675 ≤ (10079646673189/20000000000000 : ℝ)^3651 := by
    have hnat : (5855951877 : ℕ)^4675*20000000000000^3651 ≤ 10079646673189^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5855951877 10000000000 10079646673189 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886891459/10000000000 : ℝ)^4675 ≤ (4997184248663/12500000000000 : ℝ)^3651 := by
    have hnat : (4886891459 : ℕ)^4675*12500000000000^3651 ≤ 4997184248663^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886891459 10000000000 4997184248663 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1607122953/10000000000 : ℝ), (5855951877/10000000000 : ℝ), (4886891459/10000000000 : ℝ)] ![(9624292632229/100000000000000 : ℝ), (10079646673189/20000000000000 : ℝ), (4997184248663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1607122953/10000000000 : ℝ)|^4675 ≤ (9624292632229/100000000000000 : ℝ)^3651
        have hw : |(-1607122953/10000000000 : ℝ)|=(1607122953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5855951877/10000000000 : ℝ)|^4675 ≤ (10079646673189/20000000000000 : ℝ)^3651
        have hw : |(5855951877/10000000000 : ℝ)|=(5855951877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886891459/10000000000 : ℝ)|^4675 ≤ (4997184248663/12500000000000 : ℝ)^3651
        have hw : |(4886891459/10000000000 : ℝ)|=(4886891459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (682680041/1250000000 : ℝ)*x 0 + (-1072582349/5000000000 : ℝ)*x 1 + (4886891299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (682680041/1250000000 : ℝ)^4675 ≤ (46092413710649/100000000000000 : ℝ)^3651 := by
    have hnat : (682680041 : ℕ)^4675*100000000000000^3651 ≤ 46092413710649^3651*1250000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682680041 1250000000 46092413710649 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072582349/5000000000 : ℝ)^4675 ≤ (696505698283/5000000000000 : ℝ)^3651 := by
    have hnat : (1072582349 : ℕ)^4675*5000000000000^3651 ≤ 696505698283^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072582349 5000000000 696505698283 5000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886891299/10000000000 : ℝ)^4675 ≤ (39977472313311/100000000000000 : ℝ)^3651 := by
    have hnat : (4886891299 : ℕ)^4675*100000000000000^3651 ≤ 39977472313311^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886891299 10000000000 39977472313311 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(682680041/1250000000 : ℝ), (-1072582349/5000000000 : ℝ), (4886891299/10000000000 : ℝ)] ![(46092413710649/100000000000000 : ℝ), (696505698283/5000000000000 : ℝ), (39977472313311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(682680041/1250000000 : ℝ)|^4675 ≤ (46092413710649/100000000000000 : ℝ)^3651
        have hw : |(682680041/1250000000 : ℝ)|=(682680041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072582349/5000000000 : ℝ)|^4675 ≤ (696505698283/5000000000000 : ℝ)^3651
        have hw : |(-1072582349/5000000000 : ℝ)|=(1072582349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886891299/10000000000 : ℝ)|^4675 ≤ (39977472313311/100000000000000 : ℝ)^3651
        have hw : |(4886891299/10000000000 : ℝ)|=(4886891299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2730720197/5000000000 : ℝ)*x 0 + (4886891187/10000000000 : ℝ)*x 1 + (-1072582377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2730720197/5000000000 : ℝ)^4675 ≤ (4609241442389/10000000000000 : ℝ)^3651 := by
    have hnat : (2730720197 : ℕ)^4675*10000000000000^3651 ≤ 4609241442389^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730720197 5000000000 4609241442389 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4886891187/10000000000 : ℝ)^4675 ≤ (7995494228023/20000000000000 : ℝ)^3651 := by
    have hnat : (4886891187 : ℕ)^4675*20000000000000^3651 ≤ 7995494228023^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886891187 10000000000 7995494228023 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072582377/5000000000 : ℝ)^4675 ≤ (6965057215651/50000000000000 : ℝ)^3651 := by
    have hnat : (1072582377 : ℕ)^4675*50000000000000^3651 ≤ 6965057215651^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072582377 5000000000 6965057215651 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2730720197/5000000000 : ℝ), (4886891187/10000000000 : ℝ), (-1072582377/5000000000 : ℝ)] ![(4609241442389/10000000000000 : ℝ), (7995494228023/20000000000000 : ℝ), (6965057215651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2730720197/5000000000 : ℝ)|^4675 ≤ (4609241442389/10000000000000 : ℝ)^3651
        have hw : |(2730720197/5000000000 : ℝ)|=(2730720197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4886891187/10000000000 : ℝ)|^4675 ≤ (7995494228023/20000000000000 : ℝ)^3651
        have hw : |(4886891187/10000000000 : ℝ)|=(4886891187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1072582377/5000000000 : ℝ)|^4675 ≤ (6965057215651/50000000000000 : ℝ)^3651
        have hw : |(-1072582377/5000000000 : ℝ)|=(1072582377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2062490307/5000000000 : ℝ)*x 0 + (3094351641/10000000000 : ℝ)*x 1 + (5411517277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062490307/5000000000 : ℝ)^4675 ≤ (16088993466007/50000000000000 : ℝ)^3651 := by
    have hnat : (2062490307 : ℕ)^4675*50000000000000^3651 ≤ 16088993466007^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062490307 5000000000 16088993466007 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3094351641/10000000000 : ℝ)^4675 ≤ (22268408364793/100000000000000 : ℝ)^3651 := by
    have hnat : (3094351641 : ℕ)^4675*100000000000000^3651 ≤ 22268408364793^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094351641 10000000000 22268408364793 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411517277/10000000000 : ℝ)^4675 ≤ (45553604692263/100000000000000 : ℝ)^3651 := by
    have hnat : (5411517277 : ℕ)^4675*100000000000000^3651 ≤ 45553604692263^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411517277 10000000000 45553604692263 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2062490307/5000000000 : ℝ), (3094351641/10000000000 : ℝ), (5411517277/10000000000 : ℝ)] ![(16088993466007/50000000000000 : ℝ), (22268408364793/100000000000000 : ℝ), (45553604692263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2062490307/5000000000 : ℝ)|^4675 ≤ (16088993466007/50000000000000 : ℝ)^3651
        have hw : |(2062490307/5000000000 : ℝ)|=(2062490307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3094351641/10000000000 : ℝ)|^4675 ≤ (22268408364793/100000000000000 : ℝ)^3651
        have hw : |(3094351641/10000000000 : ℝ)|=(3094351641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411517277/10000000000 : ℝ)|^4675 ≤ (45553604692263/100000000000000 : ℝ)^3651
        have hw : |(5411517277/10000000000 : ℝ)|=(5411517277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402509217/2500000000 : ℝ)*x 0 + (4911207161/10000000000 : ℝ)*x 1 + (364423733/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402509217/2500000000 : ℝ)^4675 ≤ (1929328518349/20000000000000 : ℝ)^3651 := by
    have hnat : (402509217 : ℕ)^4675*20000000000000^3651 ≤ 1929328518349^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402509217 2500000000 1929328518349 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4911207161/10000000000 : ℝ)^4675 ≤ (40232357547959/100000000000000 : ℝ)^3651 := by
    have hnat : (4911207161 : ℕ)^4675*100000000000000^3651 ≤ 40232357547959^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911207161 10000000000 40232357547959 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364423733/625000000 : ℝ)^4675 ≤ (25060499921679/50000000000000 : ℝ)^3651 := by
    have hnat : (364423733 : ℕ)^4675*50000000000000^3651 ≤ 25060499921679^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364423733 625000000 25060499921679 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402509217/2500000000 : ℝ), (4911207161/10000000000 : ℝ), (364423733/625000000 : ℝ)] ![(1929328518349/20000000000000 : ℝ), (40232357547959/100000000000000 : ℝ), (25060499921679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402509217/2500000000 : ℝ)|^4675 ≤ (1929328518349/20000000000000 : ℝ)^3651
        have hw : |(-402509217/2500000000 : ℝ)|=(402509217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4911207161/10000000000 : ℝ)|^4675 ≤ (40232357547959/100000000000000 : ℝ)^3651
        have hw : |(4911207161/10000000000 : ℝ)|=(4911207161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(364423733/625000000 : ℝ)|^4675 ≤ (25060499921679/50000000000000 : ℝ)^3651
        have hw : |(364423733/625000000 : ℝ)|=(364423733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196506281/10000000000 : ℝ)*x 0 + (-600637927/5000000000 : ℝ)*x 1 + (2915389911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196506281/10000000000 : ℝ)^4675 ≤ (4324906620171/10000000000000 : ℝ)^3651 := by
    have hnat : (5196506281 : ℕ)^4675*10000000000000^3651 ≤ 4324906620171^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196506281 10000000000 4324906620171 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600637927/5000000000 : ℝ)^4675 ≤ (6629932903577/100000000000000 : ℝ)^3651 := by
    have hnat : (600637927 : ℕ)^4675*100000000000000^3651 ≤ 6629932903577^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600637927 5000000000 6629932903577 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2915389911/5000000000 : ℝ)^4675 ≤ (25060500439001/50000000000000 : ℝ)^3651 := by
    have hnat : (2915389911 : ℕ)^4675*50000000000000^3651 ≤ 25060500439001^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2915389911 5000000000 25060500439001 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196506281/10000000000 : ℝ), (-600637927/5000000000 : ℝ), (2915389911/5000000000 : ℝ)] ![(4324906620171/10000000000000 : ℝ), (6629932903577/100000000000000 : ℝ), (25060500439001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196506281/10000000000 : ℝ)|^4675 ≤ (4324906620171/10000000000000 : ℝ)^3651
        have hw : |(5196506281/10000000000 : ℝ)|=(5196506281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-600637927/5000000000 : ℝ)|^4675 ≤ (6629932903577/100000000000000 : ℝ)^3651
        have hw : |(-600637927/5000000000 : ℝ)|=(600637927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2915389911/5000000000 : ℝ)|^4675 ≤ (25060500439001/50000000000000 : ℝ)^3651
        have hw : |(2915389911/5000000000 : ℝ)|=(2915389911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039301251/2000000000 : ℝ)*x 0 + (5830779719/10000000000 : ℝ)*x 1 + (-240255211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039301251/2000000000 : ℝ)^4675 ≤ (10812266481157/25000000000000 : ℝ)^3651 := by
    have hnat : (1039301251 : ℕ)^4675*25000000000000^3651 ≤ 10812266481157^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039301251 2000000000 10812266481157 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5830779719/10000000000 : ℝ)^4675 ≤ (50120999744297/100000000000000 : ℝ)^3651 := by
    have hnat : (5830779719 : ℕ)^4675*100000000000000^3651 ≤ 50120999744297^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5830779719 10000000000 50120999744297 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240255211/2000000000 : ℝ)^4675 ≤ (414370895253/6250000000000 : ℝ)^3651 := by
    have hnat : (240255211 : ℕ)^4675*6250000000000^3651 ≤ 414370895253^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240255211 2000000000 414370895253 6250000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039301251/2000000000 : ℝ), (5830779719/10000000000 : ℝ), (-240255211/2000000000 : ℝ)] ![(10812266481157/25000000000000 : ℝ), (50120999744297/100000000000000 : ℝ), (414370895253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039301251/2000000000 : ℝ)|^4675 ≤ (10812266481157/25000000000000 : ℝ)^3651
        have hw : |(1039301251/2000000000 : ℝ)|=(1039301251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5830779719/10000000000 : ℝ)|^4675 ≤ (50120999744297/100000000000000 : ℝ)^3651
        have hw : |(5830779719/10000000000 : ℝ)|=(5830779719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240255211/2000000000 : ℝ)|^4675 ≤ (414370895253/6250000000000 : ℝ)^3651
        have hw : |(-240255211/2000000000 : ℝ)|=(240255211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s0_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131948717/10000000000 : ℝ)*x 0 + (66917181/125000000 : ℝ)*x 1 + (197158851/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131948717/10000000000 : ℝ)^4675 ≤ (80619013367/250000000000 : ℝ)^3651 := by
    have hnat : (4131948717 : ℕ)^4675*250000000000^3651 ≤ 80619013367^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131948717 10000000000 80619013367 250000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66917181/125000000 : ℝ)^4675 ≤ (44927837417227/100000000000000 : ℝ)^3651 := by
    have hnat : (66917181 : ℕ)^4675*100000000000000^3651 ≤ 44927837417227^3651*125000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66917181 125000000 44927837417227 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197158851/625000000 : ℝ)^4675 ≤ (4564911443737/20000000000000 : ℝ)^3651 := by
    have hnat : (197158851 : ℕ)^4675*20000000000000^3651 ≤ 4564911443737^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197158851 625000000 4564911443737 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131948717/10000000000 : ℝ), (66917181/125000000 : ℝ), (197158851/625000000 : ℝ)] ![(80619013367/250000000000 : ℝ), (44927837417227/100000000000000 : ℝ), (4564911443737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131948717/10000000000 : ℝ)|^4675 ≤ (80619013367/250000000000 : ℝ)^3651
        have hw : |(4131948717/10000000000 : ℝ)|=(4131948717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66917181/125000000 : ℝ)|^4675 ≤ (44927837417227/100000000000000 : ℝ)^3651
        have hw : |(66917181/125000000 : ℝ)|=(66917181/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197158851/625000000 : ℝ)|^4675 ≤ (4564911443737/20000000000000 : ℝ)^3651
        have hw : |(197158851/625000000 : ℝ)|=(197158851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3767/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6131/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4673/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4673 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4673*1^1024 ≤ 0^1024*1^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4673/1024 : ℝ) ≤ (763800786924594683/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4673 ≤ (763800786924594683/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4673*50000000000000000000^1024 ≤ 763800786924594683^1024*5^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 763800786924594683 50000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (763800786924594683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4673 := by
      have hnat : (1 : ℕ)^1024*1^4673 ≤ 1^4673*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50763800786924594683/50000000000000000000 : ℝ) ≤ (5016638326717381/5000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (50763800786924594683/50000000000000000000 : ℝ)^1024 ≤ (5016638326717381/5000000000000000 : ℝ)^4673 := by
      have hnat : (50763800786924594683 : ℕ)^1024*5000000000000000^4673 ≤ 5016638326717381^4673*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50763800786924594683 50000000000000000000 5016638326717381 5000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016638326717381/5000000000000000 : ℝ)) (X := (50763800786924594683/50000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25763800786924594683/25000000000000000000 : ℝ) ≤ (2516638326717381/2500000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (25763800786924594683/25000000000000000000 : ℝ)^1024 ≤ (2516638326717381/2500000000000000 : ℝ)^4673 := by
      have hnat : (25763800786924594683 : ℕ)^1024*2500000000000000^4673 ≤ 2516638326717381^4673*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25763800786924594683 25000000000000000000 2516638326717381 2500000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2516638326717381/2500000000000000 : ℝ)) (X := (25763800786924594683/25000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(16638326717381/2000000000000000 : ℝ)*(0 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16638326717381/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(763800786924594683/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(16638326717381/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (1 : ℝ)+(16638326717381/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5016638326717381/5000000000000000 : ℝ) by norm_num, show 1+(763800786924594683/50000000000000000000 : ℝ)+(0 : ℝ)=(50763800786924594683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(763800786924594683/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(16638326717381/2000000000000000 : ℝ)*(2/5 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16638326717381/2000000000000000 : ℝ)*(2/5 : ℝ)=(2516638326717381/2500000000000000 : ℝ) by norm_num, show 1+2*(763800786924594683/50000000000000000000 : ℝ)=(25763800786924594683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(16638326717381/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16638326717381/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(16638326717381/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16638326717381/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(16638326717381/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16638326717381/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1607122953/10000000000 : ℝ)*X 0 0+(5855951877/10000000000 : ℝ)*X 0 1+(4886891459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((682680041/1250000000 : ℝ)*X 1 0+(-1072582349/5000000000 : ℝ)*X 1 1+(4886891299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2730720197/5000000000 : ℝ)*X 2 0+(4886891187/10000000000 : ℝ)*X 2 1+(-1072582377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2062490307/5000000000 : ℝ)*X 0 0+(3094351641/10000000000 : ℝ)*X 0 1+(5411517277/10000000000 : ℝ)*X 0 2+(2062490307/5000000000 : ℝ)*X 1 0+(3094351641/10000000000 : ℝ)*X 1 1+(5411517277/10000000000 : ℝ)*X 1 2+(2062490307/5000000000 : ℝ)*X 2 0+(3094351641/10000000000 : ℝ)*X 2 1+(5411517277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-402509217/2500000000 : ℝ)*X 0 0+(4911207161/10000000000 : ℝ)*X 0 1+(364423733/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196506281/10000000000 : ℝ)*X 1 0+(-600637927/5000000000 : ℝ)*X 1 1+(2915389911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039301251/2000000000 : ℝ)*X 2 0+(5830779719/10000000000 : ℝ)*X 2 1+(-240255211/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4131948717/10000000000 : ℝ)*X 0 0+(66917181/125000000 : ℝ)*X 0 1+(197158851/625000000 : ℝ)*X 0 2+(4131948717/10000000000 : ℝ)*X 1 0+(66917181/125000000 : ℝ)*X 1 1+(197158851/625000000 : ℝ)*X 1 2+(4131948717/10000000000 : ℝ)*X 2 0+(66917181/125000000 : ℝ)*X 2 1+(197158851/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35789883512182180575951/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20607283/100000000000000 : ℝ)*(base1) + (443301789/100000000000000 : ℝ)*(base19) + (227886189/50000000000000 : ℝ)*(base23) + (28893143/50000000000000 : ℝ)*(upper3) + (43978071/100000000000000 : ℝ)*(upper5) + (182936705698343/25000000000000 : ℝ)*(major0) + (182936705698343/25000000000000 : ℝ)*(major1) + (182936705698343/25000000000000 : ℝ)*(major2) + (1031928922088039/100000000000000 : ℝ)*(sp0) + (1031929965744007/100000000000000 : ℝ)*(sp1) + (515964976636709/50000000000000 : ℝ)*(sp2) + (431562380985511/100000000000000 : ℝ)*(sp3) + (18844563/1250000000000 : ℝ)*(sp4) + (36975423/5000000000000 : ℝ)*(sp7) + (86312628220251/20000000000000 : ℝ)*(f.failure) + (257982602261449/25000000000000 : ℝ)*(f.sum) + (2215008824683/25000000000000000000000000000 : ℝ)*base65 + (128828151299683/50000000000000000000000000000 : ℝ)*base67 + (124068754599683/50000000000000000000000000000 : ℝ)*base69 + (107782207499683/50000000000000000000000000000 : ℝ)*base71 + (33303335625317/25000000000000000000000000000 : ℝ)*base74 + (236017400999683/50000000000000000000000000000 : ℝ)*base75 + (145905587699683/50000000000000000000000000000 : ℝ)*base77 + (160677325149683/50000000000000000000000000000 : ℝ)*base79 + (52098992375317/25000000000000000000000000000 : ℝ)*base82 + (9543053/2000000000000000000000 : ℝ)*base89 + (9543053/2000000000000000000000 : ℝ)*base91 + (9543053/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18706735988756139850509/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (655708687/100000000000000 : ℝ)*(base19) + (652515151/100000000000000 : ℝ)*(base23) + (85451561/100000000000000 : ℝ)*(base32) + (109225939/100000000000000 : ℝ)*(upper3) + (18700151/50000000000000 : ℝ)*(upper5) + (192780985953937/25000000000000 : ℝ)*(major0) + (192780985953937/25000000000000 : ℝ)*(major1) + (192780985953937/25000000000000 : ℝ)*(major2) + (28865893/1562500000000 : ℝ)*(sp1) + (189149821/10000000000000 : ℝ)*(sp2) + (271865289527017/25000000000000 : ℝ)*(sp4) + (271864663745557/25000000000000 : ℝ)*(sp5) + (543729307047353/50000000000000 : ℝ)*(sp6) + (227393272151299/50000000000000 : ℝ)*(sp7) + (454786629754159/100000000000000 : ℝ)*(f.failure) + (271865289527017/25000000000000 : ℝ)*(f.sum) + (19833689728997/25000000000000000000000000000 : ℝ)*base65 + (26055383878997/50000000000000000000000000000 : ℝ)*base67 + (400495889678997/50000000000000000000000000000 : ℝ)*base69 + (452126748778997/50000000000000000000000000000 : ℝ)*base71 + (140857822521003/25000000000000000000000000000 : ℝ)*base74 + (660719971678997/50000000000000000000000000000 : ℝ)*base75 + (259776706478997/50000000000000000000000000000 : ℝ)*base77 + (766461987078997/50000000000000000000000000000 : ℝ)*base79 + (68230003328997/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (46926823/10000000000000000000000 : ℝ)*base90 + (46926823/10000000000000000000000 : ℝ)*base92 + (46926823/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1589_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6131/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1589_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1589_s1_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740985897/10000000000 : ℝ)*x 0 + (5524315551/10000000000 : ℝ)*x 1 + (2566078511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740985897/10000000000 : ℝ)^4675 ≤ (426501193723/4000000000000 : ℝ)^3651 := by
    have hnat : (1740985897 : ℕ)^4675*4000000000000^3651 ≤ 426501193723^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740985897 10000000000 426501193723 4000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524315551/10000000000 : ℝ)^4675 ≤ (46772979707257/100000000000000 : ℝ)^3651 := by
    have hnat : (5524315551 : ℕ)^4675*100000000000000^3651 ≤ 46772979707257^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524315551 10000000000 46772979707257 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566078511/5000000000 : ℝ)^4675 ≤ (42564490436871/100000000000000 : ℝ)^3651 := by
    have hnat : (2566078511 : ℕ)^4675*100000000000000^3651 ≤ 42564490436871^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566078511 5000000000 42564490436871 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740985897/10000000000 : ℝ), (5524315551/10000000000 : ℝ), (2566078511/5000000000 : ℝ)] ![(426501193723/4000000000000 : ℝ), (46772979707257/100000000000000 : ℝ), (42564490436871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740985897/10000000000 : ℝ)|^4675 ≤ (426501193723/4000000000000 : ℝ)^3651
        have hw : |(-1740985897/10000000000 : ℝ)|=(1740985897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524315551/10000000000 : ℝ)|^4675 ≤ (46772979707257/100000000000000 : ℝ)^3651
        have hw : |(5524315551/10000000000 : ℝ)|=(5524315551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566078511/5000000000 : ℝ)|^4675 ≤ (42564490436871/100000000000000 : ℝ)^3651
        have hw : |(2566078511/5000000000 : ℝ)|=(2566078511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373267227/10000000000 : ℝ)*x 0 + (-486428209/2500000000 : ℝ)*x 1 + (5132156613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373267227/10000000000 : ℝ)^4675 ≤ (4514172150931/10000000000000 : ℝ)^3651 := by
    have hnat : (5373267227 : ℕ)^4675*10000000000000^3651 ≤ 4514172150931^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373267227 10000000000 4514172150931 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486428209/2500000000 : ℝ)^4675 ≤ (6146896192631/50000000000000 : ℝ)^3651 := by
    have hnat : (486428209 : ℕ)^4675*50000000000000^3651 ≤ 6146896192631^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486428209 2500000000 6146896192631 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132156613/10000000000 : ℝ)^4675 ≤ (42564486093363/100000000000000 : ℝ)^3651 := by
    have hnat : (5132156613 : ℕ)^4675*100000000000000^3651 ≤ 42564486093363^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132156613 10000000000 42564486093363 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373267227/10000000000 : ℝ), (-486428209/2500000000 : ℝ), (5132156613/10000000000 : ℝ)] ![(4514172150931/10000000000000 : ℝ), (6146896192631/50000000000000 : ℝ), (42564486093363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373267227/10000000000 : ℝ)|^4675 ≤ (4514172150931/10000000000000 : ℝ)^3651
        have hw : |(5373267227/10000000000 : ℝ)|=(5373267227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486428209/2500000000 : ℝ)|^4675 ≤ (6146896192631/50000000000000 : ℝ)^3651
        have hw : |(-486428209/2500000000 : ℝ)|=(486428209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5132156613/10000000000 : ℝ)|^4675 ≤ (42564486093363/100000000000000 : ℝ)^3651
        have hw : |(5132156613/10000000000 : ℝ)|=(5132156613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373266683/10000000000 : ℝ)*x 0 + (2566078557/5000000000 : ℝ)*x 1 + (-1945712901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373266683/10000000000 : ℝ)^4675 ≤ (9028343131451/20000000000000 : ℝ)^3651 := by
    have hnat : (5373266683 : ℕ)^4675*20000000000000^3651 ≤ 9028343131451^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373266683 10000000000 9028343131451 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566078557/5000000000 : ℝ)^4675 ≤ (8512898282779/20000000000000 : ℝ)^3651 := by
    have hnat : (2566078557 : ℕ)^4675*20000000000000^3651 ≤ 8512898282779^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566078557 5000000000 8512898282779 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945712901/10000000000 : ℝ)^4675 ≤ (6146896455573/50000000000000 : ℝ)^3651 := by
    have hnat : (1945712901 : ℕ)^4675*50000000000000^3651 ≤ 6146896455573^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945712901 10000000000 6146896455573 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373266683/10000000000 : ℝ), (2566078557/5000000000 : ℝ), (-1945712901/10000000000 : ℝ)] ![(9028343131451/20000000000000 : ℝ), (8512898282779/20000000000000 : ℝ), (6146896455573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373266683/10000000000 : ℝ)|^4675 ≤ (9028343131451/20000000000000 : ℝ)^3651
        have hw : |(5373266683/10000000000 : ℝ)|=(5373266683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566078557/5000000000 : ℝ)|^4675 ≤ (8512898282779/20000000000000 : ℝ)^3651
        have hw : |(2566078557/5000000000 : ℝ)|=(2566078557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945712901/10000000000 : ℝ)|^4675 ≤ (6146896455573/50000000000000 : ℝ)^3651
        have hw : |(-1945712901/10000000000 : ℝ)|=(1945712901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33772447/80000000 : ℝ)*x 0 + (3773382217/10000000000 : ℝ)*x 1 + (2355545501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33772447/80000000 : ℝ)^4675 ≤ (33145792878491/100000000000000 : ℝ)^3651 := by
    have hnat : (33772447 : ℕ)^4675*100000000000000^3651 ≤ 33145792878491^3651*80000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33772447 80000000 33145792878491 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3773382217/10000000000 : ℝ)^4675 ≤ (2870886467849/10000000000000 : ℝ)^3651 := by
    have hnat : (3773382217 : ℕ)^4675*10000000000000^3651 ≤ 2870886467849^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3773382217 10000000000 2870886467849 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2355545501/5000000000 : ℝ)^4675 ≤ (1525813696939/4000000000000 : ℝ)^3651 := by
    have hnat : (2355545501 : ℕ)^4675*4000000000000^3651 ≤ 1525813696939^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355545501 5000000000 1525813696939 4000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33772447/80000000 : ℝ), (3773382217/10000000000 : ℝ), (2355545501/5000000000 : ℝ)] ![(33145792878491/100000000000000 : ℝ), (2870886467849/10000000000000 : ℝ), (1525813696939/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33772447/80000000 : ℝ)|^4675 ≤ (33145792878491/100000000000000 : ℝ)^3651
        have hw : |(33772447/80000000 : ℝ)|=(33772447/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3773382217/10000000000 : ℝ)|^4675 ≤ (2870886467849/10000000000000 : ℝ)^3651
        have hw : |(3773382217/10000000000 : ℝ)|=(3773382217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2355545501/5000000000 : ℝ)|^4675 ≤ (1525813696939/4000000000000 : ℝ)^3651
        have hw : |(2355545501/5000000000 : ℝ)|=(2355545501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1741174413/10000000000 : ℝ)*x 0 + (5136099857/10000000000 : ℝ)*x 1 + (5520316121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1741174413/10000000000 : ℝ)^4675 ≤ (10664008235061/100000000000000 : ℝ)^3651 := by
    have hnat : (1741174413 : ℕ)^4675*100000000000000^3651 ≤ 10664008235061^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741174413 10000000000 10664008235061 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136099857/10000000000 : ℝ)^4675 ≤ (42606367157733/100000000000000 : ℝ)^3651 := by
    have hnat : (5136099857 : ℕ)^4675*100000000000000^3651 ≤ 42606367157733^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136099857 10000000000 42606367157733 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520316121/10000000000 : ℝ)^4675 ≤ (23364812296243/50000000000000 : ℝ)^3651 := by
    have hnat : (5520316121 : ℕ)^4675*50000000000000^3651 ≤ 23364812296243^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520316121 10000000000 23364812296243 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1741174413/10000000000 : ℝ), (5136099857/10000000000 : ℝ), (5520316121/10000000000 : ℝ)] ![(10664008235061/100000000000000 : ℝ), (42606367157733/100000000000000 : ℝ), (23364812296243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1741174413/10000000000 : ℝ)|^4675 ≤ (10664008235061/100000000000000 : ℝ)^3651
        have hw : |(-1741174413/10000000000 : ℝ)|=(1741174413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136099857/10000000000 : ℝ)|^4675 ≤ (42606367157733/100000000000000 : ℝ)^3651
        have hw : |(5136099857/10000000000 : ℝ)|=(5136099857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520316121/10000000000 : ℝ)|^4675 ≤ (23364812296243/50000000000000 : ℝ)^3651
        have hw : |(5520316121/10000000000 : ℝ)|=(5520316121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5269129449/10000000000 : ℝ)*x 0 + (-1557553353/10000000000 : ℝ)*x 1 + (220812679/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5269129449/10000000000 : ℝ)^4675 ≤ (44024523231563/100000000000000 : ℝ)^3651 := by
    have hnat : (5269129449 : ℕ)^4675*100000000000000^3651 ≤ 44024523231563^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269129449 10000000000 44024523231563 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557553353/10000000000 : ℝ)^4675 ≤ (1155730362373/12500000000000 : ℝ)^3651 := by
    have hnat : (1557553353 : ℕ)^4675*12500000000000^3651 ≤ 1155730362373^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557553353 10000000000 1155730362373 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220812679/400000000 : ℝ)^4675 ≤ (23364816924591/50000000000000 : ℝ)^3651 := by
    have hnat : (220812679 : ℕ)^4675*50000000000000^3651 ≤ 23364816924591^3651*400000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220812679 400000000 23364816924591 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5269129449/10000000000 : ℝ), (-1557553353/10000000000 : ℝ), (220812679/400000000 : ℝ)] ![(44024523231563/100000000000000 : ℝ), (1155730362373/12500000000000 : ℝ), (23364816924591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5269129449/10000000000 : ℝ)|^4675 ≤ (44024523231563/100000000000000 : ℝ)^3651
        have hw : |(5269129449/10000000000 : ℝ)|=(5269129449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1557553353/10000000000 : ℝ)|^4675 ≤ (1155730362373/12500000000000 : ℝ)^3651
        have hw : |(-1557553353/10000000000 : ℝ)|=(1557553353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220812679/400000000 : ℝ)|^4675 ≤ (23364816924591/50000000000000 : ℝ)^3651
        have hw : |(220812679/400000000 : ℝ)|=(220812679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329320523/625000000 : ℝ)*x 0 + (5520317413/10000000000 : ℝ)*x 1 + (-6230217/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329320523/625000000 : ℝ)^4675 ≤ (44024511666413/100000000000000 : ℝ)^3651 := by
    have hnat : (329320523 : ℕ)^4675*100000000000000^3651 ≤ 44024511666413^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329320523 625000000 44024511666413 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520317413/10000000000 : ℝ)^4675 ≤ (23364819298381/50000000000000 : ℝ)^3651 := by
    have hnat : (5520317413 : ℕ)^4675*50000000000000^3651 ≤ 23364819298381^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520317413 10000000000 23364819298381 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6230217/40000000 : ℝ)^4675 ≤ (9245849717123/100000000000000 : ℝ)^3651 := by
    have hnat : (6230217 : ℕ)^4675*100000000000000^3651 ≤ 9245849717123^3651*40000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6230217 40000000 9245849717123 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329320523/625000000 : ℝ), (5520317413/10000000000 : ℝ), (-6230217/40000000 : ℝ)] ![(44024511666413/100000000000000 : ℝ), (23364819298381/50000000000000 : ℝ), (9245849717123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329320523/625000000 : ℝ)|^4675 ≤ (44024511666413/100000000000000 : ℝ)^3651
        have hw : |(329320523/625000000 : ℝ)|=(329320523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520317413/10000000000 : ℝ)|^4675 ≤ (23364819298381/50000000000000 : ℝ)^3651
        have hw : |(5520317413/10000000000 : ℝ)|=(5520317413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6230217/40000000 : ℝ)|^4675 ≤ (9245849717123/100000000000000 : ℝ)^3651
        have hw : |(-6230217/40000000 : ℝ)|=(6230217/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s1_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105550143/250000000 : ℝ)*x 0 + (470166451/1000000000 : ℝ)*x 1 + (3782943707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105550143/250000000 : ℝ)^4675 ≤ (6630063109989/20000000000000 : ℝ)^3651 := by
    have hnat : (105550143 : ℕ)^4675*20000000000000^3651 ≤ 6630063109989^3651*250000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105550143 250000000 6630063109989 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470166451/1000000000 : ℝ)^4675 ≤ (38047637157443/100000000000000 : ℝ)^3651 := by
    have hnat : (470166451 : ℕ)^4675*100000000000000^3651 ≤ 38047637157443^3651*1000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470166451 1000000000 38047637157443 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3782943707/10000000000 : ℝ)^4675 ≤ (28802047269359/100000000000000 : ℝ)^3651 := by
    have hnat : (3782943707 : ℕ)^4675*100000000000000^3651 ≤ 28802047269359^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3782943707 10000000000 28802047269359 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105550143/250000000 : ℝ), (470166451/1000000000 : ℝ), (3782943707/10000000000 : ℝ)] ![(6630063109989/20000000000000 : ℝ), (38047637157443/100000000000000 : ℝ), (28802047269359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105550143/250000000 : ℝ)|^4675 ≤ (6630063109989/20000000000000 : ℝ)^3651
        have hw : |(105550143/250000000 : ℝ)|=(105550143/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(470166451/1000000000 : ℝ)|^4675 ≤ (38047637157443/100000000000000 : ℝ)^3651
        have hw : |(470166451/1000000000 : ℝ)|=(470166451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3782943707/10000000000 : ℝ)|^4675 ≤ (28802047269359/100000000000000 : ℝ)^3651
        have hw : |(3782943707/10000000000 : ℝ)|=(3782943707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6131/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8793/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6131/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6131/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6131/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6131/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6131/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6131/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3767/100000 : ℝ) ^ (4673/1024 : ℝ) ≤ (247958738533/781250000000000000 : ℝ) := by
    have hpowers : (3767/100000 : ℝ)^4673 ≤ (247958738533/781250000000000000 : ℝ)^1024 := by
      have hnat : (3767 : ℕ)^4673*781250000000000000^1024 ≤ 247958738533^1024*100000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3767 100000 247958738533 781250000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3767/100000 : ℝ)) (X := (247958738533/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6131/25000 : ℝ) ^ (4673/1024 : ℝ) ≤ (32767569835666913/20000000000000000000 : ℝ) := by
    have hpowers : (6131/25000 : ℝ)^4673 ≤ (32767569835666913/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6131 : ℕ)^4673*20000000000000000000^1024 ≤ 32767569835666913^1024*25000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6131 25000 32767569835666913 20000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6131/25000 : ℝ)) (X := (32767569835666913/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (390625247958738533/390625000000000000 : ℝ) ≤ (10000001390988219/10000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (390625247958738533/390625000000000000 : ℝ)^1024 ≤ (10000001390988219/10000000000000000 : ℝ)^4673 := by
      have hnat : (390625247958738533 : ℕ)^1024*10000000000000000^4673 ≤ 10000001390988219^4673*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390625247958738533 390625000000000000 10000001390988219 10000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001390988219/10000000000000000 : ℝ)) (X := (390625247958738533/390625000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100163869587896866789/100000000000000000000 : ℝ) ≤ (2500897149592151/2500000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (100163869587896866789/100000000000000000000 : ℝ)^1024 ≤ (2500897149592151/2500000000000000 : ℝ)^4673 := by
      have hnat : (100163869587896866789 : ℕ)^1024*2500000000000000^4673 ≤ 2500897149592151^4673*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100163869587896866789 100000000000000000000 2500897149592151 2500000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500897149592151/2500000000000000 : ℝ)) (X := (100163869587896866789/100000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10032767569835666913/10000000000000000000 : ℝ) ≤ (10007175805748989/10000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (10032767569835666913/10000000000000000000 : ℝ)^1024 ≤ (10007175805748989/10000000000000000 : ℝ)^4673 := by
      have hnat : (10032767569835666913 : ℕ)^1024*10000000000000000^4673 ≤ 10007175805748989^4673*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10032767569835666913 10000000000000000000 10007175805748989 10000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007175805748989/10000000000000000 : ℝ)) (X := (10032767569835666913/10000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(247958738533/781250000000000000 : ℝ) ≤ ((207543002852338641193/207570000000000000000 : ℝ)+2*(717441476077/415140000000000 : ℝ)*(3767/100000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (207543002852338641193/207570000000000000000 : ℝ)+2*(717441476077/415140000000000 : ℝ)*(3767/100000 : ℝ)=(10000001390988219/10000000000000000 : ℝ) by norm_num, show 1+2*(247958738533/781250000000000000 : ℝ)=(390625247958738533/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32767569835666913/20000000000000000000 : ℝ)+(247958738533/781250000000000000 : ℝ) ≤ ((207543002852338641193/207570000000000000000 : ℝ)+(717441476077/415140000000000 : ℝ)*((6131/25000 : ℝ)+(3767/100000 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (207543002852338641193/207570000000000000000 : ℝ)+(717441476077/415140000000000 : ℝ)*((6131/25000 : ℝ)+(3767/100000 : ℝ))=(2500897149592151/2500000000000000 : ℝ) by norm_num, show 1+(32767569835666913/20000000000000000000 : ℝ)+(247958738533/781250000000000000 : ℝ)=(100163869587896866789/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32767569835666913/20000000000000000000 : ℝ) ≤ ((207543002852338641193/207570000000000000000 : ℝ)+2*(717441476077/415140000000000 : ℝ)*(6131/25000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (207543002852338641193/207570000000000000000 : ℝ)+2*(717441476077/415140000000000 : ℝ)*(6131/25000 : ℝ)=(10007175805748989/10000000000000000 : ℝ) by norm_num, show 1+2*(32767569835666913/20000000000000000000 : ℝ)=(10032767569835666913/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (207543002852338641193/207570000000000000000 : ℝ)*(X 1 0+X 2 0)+(717441476077/415140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (3767/100000 : ℝ)) (hi := (6131/25000 : ℝ)) (c := (207543002852338641193/207570000000000000000 : ℝ)) (alpha := (717441476077/415140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (207543002852338641193/207570000000000000000 : ℝ)*(X 0 1+X 2 1)+(717441476077/415140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (3767/100000 : ℝ)) (hi := (6131/25000 : ℝ)) (c := (207543002852338641193/207570000000000000000 : ℝ)) (alpha := (717441476077/415140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (207543002852338641193/207570000000000000000 : ℝ)*(X 0 2+X 1 2)+(717441476077/415140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (3767/100000 : ℝ)) (hi := (6131/25000 : ℝ)) (c := (207543002852338641193/207570000000000000000 : ℝ)) (alpha := (717441476077/415140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1740985897/10000000000 : ℝ)*X 0 0+(5524315551/10000000000 : ℝ)*X 0 1+(2566078511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373267227/10000000000 : ℝ)*X 1 0+(-486428209/2500000000 : ℝ)*X 1 1+(5132156613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373266683/10000000000 : ℝ)*X 2 0+(2566078557/5000000000 : ℝ)*X 2 1+(-1945712901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33772447/80000000 : ℝ)*X 0 0+(3773382217/10000000000 : ℝ)*X 0 1+(2355545501/5000000000 : ℝ)*X 0 2+(33772447/80000000 : ℝ)*X 1 0+(3773382217/10000000000 : ℝ)*X 1 1+(2355545501/5000000000 : ℝ)*X 1 2+(33772447/80000000 : ℝ)*X 2 0+(3773382217/10000000000 : ℝ)*X 2 1+(2355545501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1741174413/10000000000 : ℝ)*X 0 0+(5136099857/10000000000 : ℝ)*X 0 1+(5520316121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5269129449/10000000000 : ℝ)*X 1 0+(-1557553353/10000000000 : ℝ)*X 1 1+(220812679/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329320523/625000000 : ℝ)*X 2 0+(5520317413/10000000000 : ℝ)*X 2 1+(-6230217/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105550143/250000000 : ℝ)*X 0 0+(470166451/1000000000 : ℝ)*X 0 1+(3782943707/10000000000 : ℝ)*X 0 2+(105550143/250000000 : ℝ)*X 1 0+(470166451/1000000000 : ℝ)*X 1 1+(3782943707/10000000000 : ℝ)*X 1 2+(105550143/250000000 : ℝ)*X 2 0+(470166451/1000000000 : ℝ)*X 2 1+(3782943707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379200526864435724657401941/1729750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4634503/500000000000 : ℝ)*(base19) + (186008089/25000000000000 : ℝ)*(base23) + (41670327/50000000000000 : ℝ)*(upper2) + (6184887/20000000000000 : ℝ)*(upper3) + (2680019/6250000000000 : ℝ)*(upper4) + (904111061665363/50000000000000 : ℝ)*(major0) + (904111061665363/50000000000000 : ℝ)*(major1) + (904111061665363/50000000000000 : ℝ)*(major2) + (63749972931011/2500000000000 : ℝ)*(sp0) + (2550006130841303/100000000000000 : ℝ)*(sp1) + (1275003156854773/50000000000000 : ℝ)*(sp2) + (8331509753959/781250000000 : ℝ)*(sp3) + (4070250731/50000000000000 : ℝ)*(sp4) + (393310537/10000000000000 : ℝ)*(sp7) + (533218590806061/50000000000000 : ℝ)*(f.failure) + (1275003528870951/50000000000000 : ℝ)*(f.sum) + (7467960975251/5189250000000000000000000000 : ℝ)*base65 + (1155224179255018123/314500000000000000000000000000000 : ℝ)*base67 + (1931199647294018123/314500000000000000000000000000000 : ℝ)*base69 + (88521973471518123/314500000000000000000000000000000 : ℝ)*base71 + (1470543751187/2075700000000000000000000000 : ℝ)*base73 + (1759127048082481877/314500000000000000000000000000000 : ℝ)*base76 + (638909965114981877/314500000000000000000000000000000 : ℝ)*base78 + (322102083640018123/314500000000000000000000000000000 : ℝ)*base79 + (32476819563433/10378500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (786517/5000000000000000000000 : ℝ)*base90 + (786517/5000000000000000000000 : ℝ)*base92 + (786517/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (443220894348362406963/157250000000000000000000000 : ℝ) := by norm_num
    linear_combination (468263109/100000000000000 : ℝ)*(base19) + (63675789/20000000000000 : ℝ)*(base23) + (214412747/100000000000000 : ℝ)*(upper2) + (1831527/800000000000 : ℝ)*(upper3) + (922790845375531/50000000000000 : ℝ)*(major0) + (922790845375531/50000000000000 : ℝ)*(major1) + (922790845375531/50000000000000 : ℝ)*(major2) + (327017059/6250000000000 : ℝ)*(sp1) + (81526383/2000000000000 : ℝ)*(sp2) + (967583/312500000000 : ℝ)*(sp3) + (325336564015781/12500000000000 : ℝ)*(sp4) + (520537362318039/20000000000000 : ℝ)*(sp5) + (325336014678519/12500000000000 : ℝ)*(sp6) + (217694093159363/20000000000000 : ℝ)*(sp7) + (68029423463961/6250000000000 : ℝ)*(f.failure) + (325336564015781/12500000000000 : ℝ)*(f.sum) + (823625958461/943500000000000000000000000 : ℝ)*base65 + (520817597471919651/314500000000000000000000000000000 : ℝ)*base67 + (1292395867719580349/314500000000000000000000000000000 : ℝ)*base70 + (901544800214580349/314500000000000000000000000000000 : ℝ)*base72 + (5756370332497/1887000000000000000000000000 : ℝ)*base73 + (18983728860080349/314500000000000000000000000000000 : ℝ)*base76 + (618516557011919651/314500000000000000000000000000000 : ℝ)*base77 + (1228380534041919651/314500000000000000000000000000000 : ℝ)*base79 + (2766286697209/1887000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7357183/625000000000000000000 : ℝ)*base89 + (7357183/625000000000000000000 : ℝ)*base91 + (7357183/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1589_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6131/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8793/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1589_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1589_s2_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-878970827/5000000000 : ℝ)*x 0 + (679603751/1250000000 : ℝ)*x 1 + (5208572073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (878970827/5000000000 : ℝ)^4675 ≤ (2698920127033/25000000000000 : ℝ)^3651 := by
    have hnat : (878970827 : ℕ)^4675*25000000000000^3651 ≤ 2698920127033^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878970827 5000000000 2698920127033 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679603751/1250000000 : ℝ)^4675 ≤ (45826626258463/100000000000000 : ℝ)^3651 := by
    have hnat : (679603751 : ℕ)^4675*100000000000000^3651 ≤ 45826626258463^3651*1250000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679603751 1250000000 45826626258463 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208572073/10000000000 : ℝ)^4675 ≤ (43377693220937/100000000000000 : ℝ)^3651 := by
    have hnat : (5208572073 : ℕ)^4675*100000000000000^3651 ≤ 43377693220937^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208572073 10000000000 43377693220937 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-878970827/5000000000 : ℝ), (679603751/1250000000 : ℝ), (5208572073/10000000000 : ℝ)] ![(2698920127033/25000000000000 : ℝ), (45826626258463/100000000000000 : ℝ), (43377693220937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-878970827/5000000000 : ℝ)|^4675 ≤ (2698920127033/25000000000000 : ℝ)^3651
        have hw : |(-878970827/5000000000 : ℝ)|=(878970827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679603751/1250000000 : ℝ)|^4675 ≤ (45826626258463/100000000000000 : ℝ)^3651
        have hw : |(679603751/1250000000 : ℝ)|=(679603751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5208572073/10000000000 : ℝ)|^4675 ≤ (43377693220937/100000000000000 : ℝ)^3651
        have hw : |(5208572073/10000000000 : ℝ)|=(5208572073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675282667/5000000000 : ℝ)*x 0 + (-117187681/625000000 : ℝ)*x 1 + (1041714453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675282667/5000000000 : ℝ)^4675 ≤ (22448825901411/50000000000000 : ℝ)^3651 := by
    have hnat : (2675282667 : ℕ)^4675*50000000000000^3651 ≤ 22448825901411^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675282667 5000000000 22448825901411 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117187681/625000000 : ℝ)^4675 ≤ (586232645933/5000000000000 : ℝ)^3651 := by
    have hnat : (117187681 : ℕ)^4675*5000000000000^3651 ≤ 586232645933^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117187681 625000000 586232645933 5000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041714453/2000000000 : ℝ)^4675 ≤ (43377695268413/100000000000000 : ℝ)^3651 := by
    have hnat : (1041714453 : ℕ)^4675*100000000000000^3651 ≤ 43377695268413^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041714453 2000000000 43377695268413 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675282667/5000000000 : ℝ), (-117187681/625000000 : ℝ), (1041714453/2000000000 : ℝ)] ![(22448825901411/50000000000000 : ℝ), (586232645933/5000000000000 : ℝ), (43377695268413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675282667/5000000000 : ℝ)|^4675 ≤ (22448825901411/50000000000000 : ℝ)^3651
        have hw : |(2675282667/5000000000 : ℝ)|=(2675282667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117187681/625000000 : ℝ)|^4675 ≤ (586232645933/5000000000000 : ℝ)^3651
        have hw : |(-117187681/625000000 : ℝ)|=(117187681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041714453/2000000000 : ℝ)|^4675 ≤ (43377695268413/100000000000000 : ℝ)^3651
        have hw : |(1041714453/2000000000 : ℝ)|=(1041714453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535056543/1000000000 : ℝ)*x 0 + (1041714321/2000000000 : ℝ)*x 1 + (-937501823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535056543/1000000000 : ℝ)^4675 ≤ (5612206604289/12500000000000 : ℝ)^3651 := by
    have hnat : (535056543 : ℕ)^4675*12500000000000^3651 ≤ 5612206604289^3651*1000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535056543 1000000000 5612206604289 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041714321/2000000000 : ℝ)^4675 ≤ (8675537646043/20000000000000 : ℝ)^3651 := by
    have hnat : (1041714321 : ℕ)^4675*20000000000000^3651 ≤ 8675537646043^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041714321 2000000000 8675537646043 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937501823/5000000000 : ℝ)^4675 ≤ (11724658923883/100000000000000 : ℝ)^3651 := by
    have hnat : (937501823 : ℕ)^4675*100000000000000^3651 ≤ 11724658923883^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937501823 5000000000 11724658923883 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535056543/1000000000 : ℝ), (1041714321/2000000000 : ℝ), (-937501823/5000000000 : ℝ)] ![(5612206604289/12500000000000 : ℝ), (8675537646043/20000000000000 : ℝ), (11724658923883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535056543/1000000000 : ℝ)|^4675 ≤ (5612206604289/12500000000000 : ℝ)^3651
        have hw : |(535056543/1000000000 : ℝ)|=(535056543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041714321/2000000000 : ℝ)|^4675 ≤ (8675537646043/20000000000000 : ℝ)^3651
        have hw : |(1041714321/2000000000 : ℝ)|=(1041714321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937501823/5000000000 : ℝ)|^4675 ≤ (11724658923883/100000000000000 : ℝ)^3651
        have hw : |(-937501823/5000000000 : ℝ)|=(937501823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529235001/1250000000 : ℝ)*x 0 + (793598843/2000000000 : ℝ)*x 1 + (2256895733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529235001/1250000000 : ℝ)^4675 ≤ (8317436656847/25000000000000 : ℝ)^3651 := by
    have hnat : (529235001 : ℕ)^4675*25000000000000^3651 ≤ 8317436656847^3651*1250000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529235001 1250000000 8317436656847 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793598843/2000000000 : ℝ)^4675 ≤ (15309175736857/50000000000000 : ℝ)^3651 := by
    have hnat : (793598843 : ℕ)^4675*50000000000000^3651 ≤ 15309175736857^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793598843 2000000000 15309175736857 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256895733/5000000000 : ℝ)^4675 ≤ (9027975471783/25000000000000 : ℝ)^3651 := by
    have hnat : (2256895733 : ℕ)^4675*25000000000000^3651 ≤ 9027975471783^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256895733 5000000000 9027975471783 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529235001/1250000000 : ℝ), (793598843/2000000000 : ℝ), (2256895733/5000000000 : ℝ)] ![(8317436656847/25000000000000 : ℝ), (15309175736857/50000000000000 : ℝ), (9027975471783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529235001/1250000000 : ℝ)|^4675 ≤ (8317436656847/25000000000000 : ℝ)^3651
        have hw : |(529235001/1250000000 : ℝ)|=(529235001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(793598843/2000000000 : ℝ)|^4675 ≤ (15309175736857/50000000000000 : ℝ)^3651
        have hw : |(793598843/2000000000 : ℝ)|=(793598843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256895733/5000000000 : ℝ)|^4675 ≤ (9027975471783/25000000000000 : ℝ)^3651
        have hw : |(2256895733/5000000000 : ℝ)|=(2256895733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1757978563/10000000000 : ℝ)*x 0 + (260495789/500000000 : ℝ)*x 1 + (2717737691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757978563/10000000000 : ℝ)^4675 ≤ (5397985371273/50000000000000 : ℝ)^3651 := by
    have hnat : (1757978563 : ℕ)^4675*50000000000000^3651 ≤ 5397985371273^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757978563 10000000000 5397985371273 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260495789/500000000 : ℝ)^4675 ≤ (5424002868207/12500000000000 : ℝ)^3651 := by
    have hnat : (260495789 : ℕ)^4675*12500000000000^3651 ≤ 5424002868207^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260495789 500000000 5424002868207 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717737691/5000000000 : ℝ)^4675 ≤ (45812006299787/100000000000000 : ℝ)^3651 := by
    have hnat : (2717737691 : ℕ)^4675*100000000000000^3651 ≤ 45812006299787^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717737691 5000000000 45812006299787 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1757978563/10000000000 : ℝ), (260495789/500000000 : ℝ), (2717737691/5000000000 : ℝ)] ![(5397985371273/50000000000000 : ℝ), (5424002868207/12500000000000 : ℝ), (45812006299787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1757978563/10000000000 : ℝ)|^4675 ≤ (5397985371273/50000000000000 : ℝ)^3651
        have hw : |(-1757978563/10000000000 : ℝ)|=(1757978563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260495789/500000000 : ℝ)|^4675 ≤ (5424002868207/12500000000000 : ℝ)^3651
        have hw : |(260495789/500000000 : ℝ)|=(260495789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717737691/5000000000 : ℝ)|^4675 ≤ (45812006299787/100000000000000 : ℝ)^3651
        have hw : |(2717737691/5000000000 : ℝ)|=(2717737691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290039289/10000000000 : ℝ)*x 0 + (-1648099703/10000000000 : ℝ)*x 1 + (5435476899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290039289/10000000000 : ℝ)^4675 ≤ (22124176456329/50000000000000 : ℝ)^3651 := by
    have hnat : (5290039289 : ℕ)^4675*50000000000000^3651 ≤ 22124176456329^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290039289 10000000000 22124176456329 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1648099703/10000000000 : ℝ)^4675 ≤ (9939624405631/100000000000000 : ℝ)^3651 := by
    have hnat : (1648099703 : ℕ)^4675*100000000000000^3651 ≤ 9939624405631^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648099703 10000000000 9939624405631 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435476899/10000000000 : ℝ)^4675 ≤ (22906011335807/50000000000000 : ℝ)^3651 := by
    have hnat : (5435476899 : ℕ)^4675*50000000000000^3651 ≤ 22906011335807^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435476899 10000000000 22906011335807 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290039289/10000000000 : ℝ), (-1648099703/10000000000 : ℝ), (5435476899/10000000000 : ℝ)] ![(22124176456329/50000000000000 : ℝ), (9939624405631/100000000000000 : ℝ), (22906011335807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290039289/10000000000 : ℝ)|^4675 ≤ (22124176456329/50000000000000 : ℝ)^3651
        have hw : |(5290039289/10000000000 : ℝ)|=(5290039289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1648099703/10000000000 : ℝ)|^4675 ≤ (9939624405631/100000000000000 : ℝ)^3651
        have hw : |(-1648099703/10000000000 : ℝ)|=(1648099703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435476899/10000000000 : ℝ)|^4675 ≤ (22906011335807/50000000000000 : ℝ)^3651
        have hw : |(5435476899/10000000000 : ℝ)|=(5435476899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290039671/10000000000 : ℝ)*x 0 + (2717738907/5000000000 : ℝ)*x 1 + (-824048947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290039671/10000000000 : ℝ)^4675 ≤ (11062089251013/25000000000000 : ℝ)^3651 := by
    have hnat : (5290039671 : ℕ)^4675*25000000000000^3651 ≤ 11062089251013^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290039671 10000000000 11062089251013 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717738907/5000000000 : ℝ)^4675 ≤ (22906016273257/50000000000000 : ℝ)^3651 := by
    have hnat : (2717738907 : ℕ)^4675*50000000000000^3651 ≤ 22906016273257^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717738907 5000000000 22906016273257 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824048947/5000000000 : ℝ)^4675 ≤ (9939610435683/100000000000000 : ℝ)^3651 := by
    have hnat : (824048947 : ℕ)^4675*100000000000000^3651 ≤ 9939610435683^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824048947 5000000000 9939610435683 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290039671/10000000000 : ℝ), (2717738907/5000000000 : ℝ), (-824048947/5000000000 : ℝ)] ![(11062089251013/25000000000000 : ℝ), (22906016273257/50000000000000 : ℝ), (9939610435683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290039671/10000000000 : ℝ)|^4675 ≤ (11062089251013/25000000000000 : ℝ)^3651
        have hw : |(5290039671/10000000000 : ℝ)|=(5290039671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717738907/5000000000 : ℝ)|^4675 ≤ (22906016273257/50000000000000 : ℝ)^3651
        have hw : |(2717738907/5000000000 : ℝ)|=(2717738907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-824048947/5000000000 : ℝ)|^4675 ≤ (9939610435683/100000000000000 : ℝ)^3651
        have hw : |(-824048947/5000000000 : ℝ)|=(824048947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s2_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (846793751/2000000000 : ℝ)*x 0 + (4510579987/10000000000 : ℝ)*x 1 + (198561641/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846793751/2000000000 : ℝ)^4675 ≤ (415882994937/1250000000000 : ℝ)^3651 := by
    have hnat : (846793751 : ℕ)^4675*1250000000000^3651 ≤ 415882994937^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846793751 2000000000 415882994937 1250000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510579987/10000000000 : ℝ)^4675 ≤ (36079006091253/100000000000000 : ℝ)^3651 := by
    have hnat : (4510579987 : ℕ)^4675*100000000000000^3651 ≤ 36079006091253^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510579987 10000000000 36079006091253 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198561641/500000000 : ℝ)^4675 ≤ (3065035429261/10000000000000 : ℝ)^3651 := by
    have hnat : (198561641 : ℕ)^4675*10000000000000^3651 ≤ 3065035429261^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198561641 500000000 3065035429261 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(846793751/2000000000 : ℝ), (4510579987/10000000000 : ℝ), (198561641/500000000 : ℝ)] ![(415882994937/1250000000000 : ℝ), (36079006091253/100000000000000 : ℝ), (3065035429261/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(846793751/2000000000 : ℝ)|^4675 ≤ (415882994937/1250000000000 : ℝ)^3651
        have hw : |(846793751/2000000000 : ℝ)|=(846793751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510579987/10000000000 : ℝ)|^4675 ≤ (36079006091253/100000000000000 : ℝ)^3651
        have hw : |(4510579987/10000000000 : ℝ)|=(4510579987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198561641/500000000 : ℝ)|^4675 ≤ (3065035429261/10000000000000 : ℝ)^3651
        have hw : |(198561641/500000000 : ℝ)|=(198561641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8793/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5461/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3941/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8793/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8793/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8793/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8793/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8793/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8793/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9277/100000 : ℝ) ^ (4673/1024 : ℝ) ≤ (1939941286387483/100000000000000000000 : ℝ) := by
    have hpowers : (9277/100000 : ℝ)^4673 ≤ (1939941286387483/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9277 : ℕ)^4673*100000000000000000000^1024 ≤ 1939941286387483^1024*100000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9277 100000 1939941286387483 100000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9277/100000 : ℝ)) (X := (1939941286387483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8793/50000 : ℝ) ^ (4673/1024 : ℝ) ≤ (17960053015260803/50000000000000000000 : ℝ) := by
    have hpowers : (8793/50000 : ℝ)^4673 ≤ (17960053015260803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8793 : ℕ)^4673*50000000000000000000^1024 ≤ 17960053015260803^1024*50000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8793 50000 17960053015260803 50000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8793/50000 : ℝ)) (X := (17960053015260803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001939941286387483/50000000000000000000 : ℝ) ≤ (1250010627379551/1250000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (50001939941286387483/50000000000000000000 : ℝ)^1024 ≤ (1250010627379551/1250000000000000 : ℝ)^4673 := by
      have hnat : (50001939941286387483 : ℕ)^1024*1250000000000000^4673 ≤ 1250010627379551^4673*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001939941286387483 50000000000000000000 1250010627379551 1250000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250010627379551/1250000000000000 : ℝ)) (X := (50001939941286387483/50000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037860047316909089/100000000000000000000 : ℝ) ≤ (2000165901814701/2000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (100037860047316909089/100000000000000000000 : ℝ)^1024 ≤ (2000165901814701/2000000000000000 : ℝ)^4673 := by
      have hnat : (100037860047316909089 : ℕ)^1024*2000000000000000^4673 ≤ 2000165901814701^4673*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037860047316909089 100000000000000000000 2000165901814701 2000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000165901814701/2000000000000000 : ℝ)) (X := (100037860047316909089/100000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017960053015260803/25000000000000000000 : ℝ) ≤ (5000786999555301/5000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (25017960053015260803/25000000000000000000 : ℝ)^1024 ≤ (5000786999555301/5000000000000000 : ℝ)^4673 := by
      have hnat : (25017960053015260803 : ℕ)^1024*5000000000000000^4673 ≤ 5000786999555301^4673*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017960053015260803 25000000000000000000 5000786999555301 5000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000786999555301/5000000000000000 : ℝ)) (X := (25017960053015260803/25000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1939941286387483/100000000000000000000 : ℝ) ≤ ((41538446577512608167/41545000000000000000 : ℝ)+2*(744490037097/830900000000000 : ℝ)*(9277/100000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (41538446577512608167/41545000000000000000 : ℝ)+2*(744490037097/830900000000000 : ℝ)*(9277/100000 : ℝ)=(1250010627379551/1250000000000000 : ℝ) by norm_num, show 1+2*(1939941286387483/100000000000000000000 : ℝ)=(50001939941286387483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17960053015260803/50000000000000000000 : ℝ)+(1939941286387483/100000000000000000000 : ℝ) ≤ ((41538446577512608167/41545000000000000000 : ℝ)+(744490037097/830900000000000 : ℝ)*((8793/50000 : ℝ)+(9277/100000 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (41538446577512608167/41545000000000000000 : ℝ)+(744490037097/830900000000000 : ℝ)*((8793/50000 : ℝ)+(9277/100000 : ℝ))=(2000165901814701/2000000000000000 : ℝ) by norm_num, show 1+(17960053015260803/50000000000000000000 : ℝ)+(1939941286387483/100000000000000000000 : ℝ)=(100037860047316909089/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17960053015260803/50000000000000000000 : ℝ) ≤ ((41538446577512608167/41545000000000000000 : ℝ)+2*(744490037097/830900000000000 : ℝ)*(8793/50000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (41538446577512608167/41545000000000000000 : ℝ)+2*(744490037097/830900000000000 : ℝ)*(8793/50000 : ℝ)=(5000786999555301/5000000000000000 : ℝ) by norm_num, show 1+2*(17960053015260803/50000000000000000000 : ℝ)=(25017960053015260803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41538446577512608167/41545000000000000000 : ℝ)*(X 1 0+X 2 0)+(744490037097/830900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (9277/100000 : ℝ)) (hi := (8793/50000 : ℝ)) (c := (41538446577512608167/41545000000000000000 : ℝ)) (alpha := (744490037097/830900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41538446577512608167/41545000000000000000 : ℝ)*(X 0 1+X 2 1)+(744490037097/830900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (9277/100000 : ℝ)) (hi := (8793/50000 : ℝ)) (c := (41538446577512608167/41545000000000000000 : ℝ)) (alpha := (744490037097/830900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41538446577512608167/41545000000000000000 : ℝ)*(X 0 2+X 1 2)+(744490037097/830900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (9277/100000 : ℝ)) (hi := (8793/50000 : ℝ)) (c := (41538446577512608167/41545000000000000000 : ℝ)) (alpha := (744490037097/830900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-878970827/5000000000 : ℝ)*X 0 0+(679603751/1250000000 : ℝ)*X 0 1+(5208572073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675282667/5000000000 : ℝ)*X 1 0+(-117187681/625000000 : ℝ)*X 1 1+(1041714453/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535056543/1000000000 : ℝ)*X 2 0+(1041714321/2000000000 : ℝ)*X 2 1+(-937501823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((529235001/1250000000 : ℝ)*X 0 0+(793598843/2000000000 : ℝ)*X 0 1+(2256895733/5000000000 : ℝ)*X 0 2+(529235001/1250000000 : ℝ)*X 1 0+(793598843/2000000000 : ℝ)*X 1 1+(2256895733/5000000000 : ℝ)*X 1 2+(529235001/1250000000 : ℝ)*X 2 0+(793598843/2000000000 : ℝ)*X 2 1+(2256895733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1757978563/10000000000 : ℝ)*X 0 0+(260495789/500000000 : ℝ)*X 0 1+(2717737691/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290039289/10000000000 : ℝ)*X 1 0+(-1648099703/10000000000 : ℝ)*X 1 1+(5435476899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290039671/10000000000 : ℝ)*X 2 0+(2717738907/5000000000 : ℝ)*X 2 1+(-824048947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((846793751/2000000000 : ℝ)*X 0 0+(4510579987/10000000000 : ℝ)*X 0 1+(198561641/500000000 : ℝ)*X 0 2+(846793751/2000000000 : ℝ)*X 1 0+(4510579987/10000000000 : ℝ)*X 1 1+(198561641/500000000 : ℝ)*X 1 2+(846793751/2000000000 : ℝ)*X 2 0+(4510579987/10000000000 : ℝ)*X 2 1+(198561641/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1427000733008330793344064351/207725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (976840417/100000000000000 : ℝ)*(base19) + (976266723/100000000000000 : ℝ)*(base23) + (116160647/100000000000000 : ℝ)*(upper3) + (6911891/25000000000000 : ℝ)*(lower4) + (621324821489851/20000000000000 : ℝ)*(major0) + (621324821489851/20000000000000 : ℝ)*(major1) + (621324821489851/20000000000000 : ℝ)*(major2) + (547628950049833/12500000000000 : ℝ)*(sp0) + (1095262459714999/25000000000000 : ℝ)*(sp1) + (438103827202801/10000000000000 : ℝ)*(sp2) + (1832189172891751/100000000000000 : ℝ)*(sp3) + (19215301749/100000000000000 : ℝ)*(sp4) + (144592571/1250000000000 : ℝ)*(sp6) + (7997317577/100000000000000 : ℝ)*(sp7) + (114512323138083/6250000000000 : ℝ)*(f.failure) + (4381050815700413/100000000000000 : ℝ)*(f.sum) + (56562825980753/8309000000000000000000000000 : ℝ)*base66 + (15575675731163117/830900000000000000000000000000000 : ℝ)*base67 + (1805812960748836883/830900000000000000000000000000000 : ℝ)*base70 + (2780185802328736883/830900000000000000000000000000000 : ℝ)*base72 + (3473588455557/1661800000000000000000000000 : ℝ)*base74 + (4311522652863836883/830900000000000000000000000000000 : ℝ)*base76 + (5581521044833136883/830900000000000000000000000000000 : ℝ)*base78 + (5844953993743036883/830900000000000000000000000000000 : ℝ)*base80 + (14749844328787/8309000000000000000000000000 : ℝ)*base82 + (6320149/625000000000000000000 : ℝ)*base89 + (6320149/625000000000000000000 : ℝ)*base91 + (6320149/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243819417446213351083491/20772500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5460513/5000000000000 : ℝ)*(base15) + (111522597/50000000000000 : ℝ)*(lower2) + (3560491/4000000000000 : ℝ)*(upper3) + (37889067/50000000000000 : ℝ)*(upper4) + (1571880973290293/50000000000000 : ℝ)*(major0) + (1571880973290293/50000000000000 : ℝ)*(major1) + (1571880973290293/50000000000000 : ℝ)*(major2) + (23101206773/100000000000000 : ℝ)*(sp1) + (52990103433/100000000000000 : ℝ)*(sp2) + (300698457/20000000000000 : ℝ)*(sp3) + (4433423506827753/100000000000000 : ℝ)*(sp4) + (27708751852567/625000000000 : ℝ)*(sp5) + (27708565729527/625000000000 : ℝ)*(sp6) + (4635246228969/250000000000 : ℝ)*(sp7) + (370819999015977/20000000000000 : ℝ)*(f.failure) + (4433423506827753/100000000000000 : ℝ)*(f.sum) + (257200493066997/41545000000000000000000000000 : ℝ)*base65 + (3591571479565922931/2077250000000000000000000000000000 : ℝ)*base67 + (10530433256201327069/2077250000000000000000000000000000 : ℝ)*base70 + (22910356410905172931/2077250000000000000000000000000000 : ℝ)*base71 + (130698279381527/41545000000000000000000000000 : ℝ)*base73 + (3692191645954077069/2077250000000000000000000000000000 : ℝ)*base76 + (7924414561652827069/2077250000000000000000000000000000 : ℝ)*base78 + (11164364779954672931/2077250000000000000000000000000000 : ℝ)*base79 + (99301556107651/20772500000000000000000000000 : ℝ)*base81 + (5969969/2000000000000000000000 : ℝ)*base90 + (5969969/2000000000000000000000 : ℝ)*base92 + (5969969/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1589_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8793/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1589_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1589_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1589_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1589_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1589_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1589_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
