-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1769_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:31:22.408331+00:00
-- url     : https://prove2.me/submissions/f6c802ee-c1fd-47f2-99de-90dffefe5a0e

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
theorem support_rectangle_w1769_box_0 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-766369271/10000000000 : ℝ)*x 0 + (1351397379/2500000000 : ℝ)*x 1 + (1351397731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (766369271/10000000000 : ℝ)^6079 ≤ (2277334368521/50000000000000 : ℝ)^5055 := by
    have hnat : (766369271 : ℕ)^6079*50000000000000^5055 ≤ 2277334368521^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766369271 10000000000 2277334368521 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351397379/2500000000 : ℝ)^6079 ≤ (47722658150289/100000000000000 : ℝ)^5055 := by
    have hnat : (1351397379 : ℕ)^6079*100000000000000^5055 ≤ 47722658150289^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351397379 2500000000 47722658150289 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351397731/2500000000 : ℝ)^6079 ≤ (23861336549353/50000000000000 : ℝ)^5055 := by
    have hnat : (1351397731 : ℕ)^6079*50000000000000^5055 ≤ 23861336549353^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351397731 2500000000 23861336549353 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-766369271/10000000000 : ℝ), (1351397379/2500000000 : ℝ), (1351397731/2500000000 : ℝ)] ![(2277334368521/50000000000000 : ℝ), (47722658150289/100000000000000 : ℝ), (23861336549353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-766369271/10000000000 : ℝ)|^6079 ≤ (2277334368521/50000000000000 : ℝ)^5055
        have hw : |(-766369271/10000000000 : ℝ)|=(766369271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351397379/2500000000 : ℝ)|^6079 ≤ (47722658150289/100000000000000 : ℝ)^5055
        have hw : |(1351397379/2500000000 : ℝ)|=(1351397379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351397731/2500000000 : ℝ)|^6079 ≤ (23861336549353/50000000000000 : ℝ)^5055
        have hw : |(1351397731/2500000000 : ℝ)|=(1351397731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_1 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1297996281/2500000000 : ℝ)*x 0 + (-535607531/5000000000 : ℝ)*x 1 + (5405590039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297996281/2500000000 : ℝ)^6079 ≤ (11366010576819/25000000000000 : ℝ)^5055 := by
    have hnat : (1297996281 : ℕ)^6079*25000000000000^5055 ≤ 11366010576819^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297996281 2500000000 11366010576819 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535607531/5000000000 : ℝ)^6079 ≤ (6813293969493/100000000000000 : ℝ)^5055 := by
    have hnat : (535607531 : ℕ)^6079*100000000000000^5055 ≤ 6813293969493^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535607531 5000000000 6813293969493 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405590039/10000000000 : ℝ)^6079 ≤ (23861331851431/50000000000000 : ℝ)^5055 := by
    have hnat : (5405590039 : ℕ)^6079*50000000000000^5055 ≤ 23861331851431^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405590039 10000000000 23861331851431 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1297996281/2500000000 : ℝ), (-535607531/5000000000 : ℝ), (5405590039/10000000000 : ℝ)] ![(11366010576819/25000000000000 : ℝ), (6813293969493/100000000000000 : ℝ), (23861331851431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1297996281/2500000000 : ℝ)|^6079 ≤ (11366010576819/25000000000000 : ℝ)^5055
        have hw : |(1297996281/2500000000 : ℝ)|=(1297996281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535607531/5000000000 : ℝ)|^6079 ≤ (6813293969493/100000000000000 : ℝ)^5055
        have hw : |(-535607531/5000000000 : ℝ)|=(535607531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405590039/10000000000 : ℝ)|^6079 ≤ (23861331851431/50000000000000 : ℝ)^5055
        have hw : |(5405590039/10000000000 : ℝ)|=(5405590039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_2 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038396961/2000000000 : ℝ)*x 0 + (5405590669/10000000000 : ℝ)*x 1 + (-1071214627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038396961/2000000000 : ℝ)^6079 ≤ (45464038948073/100000000000000 : ℝ)^5055 := by
    have hnat : (1038396961 : ℕ)^6079*100000000000000^5055 ≤ 45464038948073^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038396961 2000000000 45464038948073 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405590669/10000000000 : ℝ)^6079 ≤ (47722670391429/100000000000000 : ℝ)^5055 := by
    have hnat : (5405590669 : ℕ)^6079*100000000000000^5055 ≤ 47722670391429^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405590669 10000000000 47722670391429 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071214627/10000000000 : ℝ)^6079 ≤ (6813290642279/100000000000000 : ℝ)^5055 := by
    have hnat : (1071214627 : ℕ)^6079*100000000000000^5055 ≤ 6813290642279^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071214627 10000000000 6813290642279 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038396961/2000000000 : ℝ), (5405590669/10000000000 : ℝ), (-1071214627/10000000000 : ℝ)] ![(45464038948073/100000000000000 : ℝ), (47722670391429/100000000000000 : ℝ), (6813290642279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038396961/2000000000 : ℝ)|^6079 ≤ (45464038948073/100000000000000 : ℝ)^5055
        have hw : |(1038396961/2000000000 : ℝ)|=(1038396961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405590669/10000000000 : ℝ)|^6079 ≤ (47722670391429/100000000000000 : ℝ)^5055
        have hw : |(5405590669/10000000000 : ℝ)|=(5405590669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071214627/10000000000 : ℝ)|^6079 ≤ (6813290642279/100000000000000 : ℝ)^5055
        have hw : |(-1071214627/10000000000 : ℝ)|=(1071214627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_3 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1126767289/2500000000 : ℝ)*x 0 + (14680727/39062500 : ℝ)*x 1 + (3758267603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126767289/2500000000 : ℝ)^6079 ≤ (3835155541063/10000000000000 : ℝ)^5055 := by
    have hnat : (1126767289 : ℕ)^6079*10000000000000^5055 ≤ 3835155541063^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126767289 2500000000 3835155541063 10000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14680727/39062500 : ℝ)^6079 ≤ (6164842986289/20000000000000 : ℝ)^5055 := by
    have hnat : (14680727 : ℕ)^6079*20000000000000^5055 ≤ 6164842986289^5055*39062500^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14680727 39062500 6164842986289 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3758267603/10000000000 : ℝ)^6079 ≤ (30824229637397/100000000000000 : ℝ)^5055 := by
    have hnat : (3758267603 : ℕ)^6079*100000000000000^5055 ≤ 30824229637397^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758267603 10000000000 30824229637397 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126767289/2500000000 : ℝ), (14680727/39062500 : ℝ), (3758267603/10000000000 : ℝ)] ![(3835155541063/10000000000000 : ℝ), (6164842986289/20000000000000 : ℝ), (30824229637397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126767289/2500000000 : ℝ)|^6079 ≤ (3835155541063/10000000000000 : ℝ)^5055
        have hw : |(1126767289/2500000000 : ℝ)|=(1126767289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14680727/39062500 : ℝ)|^6079 ≤ (6164842986289/20000000000000 : ℝ)^5055
        have hw : |(14680727/39062500 : ℝ)|=(14680727/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3758267603/10000000000 : ℝ)|^6079 ≤ (30824229637397/100000000000000 : ℝ)^5055
        have hw : |(3758267603/10000000000 : ℝ)|=(3758267603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_4 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1519991933/10000000000 : ℝ)*x 0 + (5129903897/10000000000 : ℝ)*x 1 + (2564952193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1519991933/10000000000 : ℝ)^6079 ≤ (5188902090503/50000000000000 : ℝ)^5055 := by
    have hnat : (1519991933 : ℕ)^6079*50000000000000^5055 ≤ 5188902090503^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519991933 10000000000 5188902090503 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129903897/10000000000 : ℝ)^6079 ≤ (44811095334413/100000000000000 : ℝ)^5055 := by
    have hnat : (5129903897 : ℕ)^6079*100000000000000^5055 ≤ 44811095334413^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129903897 10000000000 44811095334413 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564952193/5000000000 : ℝ)^6079 ≤ (22405550235627/50000000000000 : ℝ)^5055 := by
    have hnat : (2564952193 : ℕ)^6079*50000000000000^5055 ≤ 22405550235627^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564952193 5000000000 22405550235627 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1519991933/10000000000 : ℝ), (5129903897/10000000000 : ℝ), (2564952193/5000000000 : ℝ)] ![(5188902090503/50000000000000 : ℝ), (44811095334413/100000000000000 : ℝ), (22405550235627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1519991933/10000000000 : ℝ)|^6079 ≤ (5188902090503/50000000000000 : ℝ)^5055
        have hw : |(-1519991933/10000000000 : ℝ)|=(1519991933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129903897/10000000000 : ℝ)|^6079 ≤ (44811095334413/100000000000000 : ℝ)^5055
        have hw : |(5129903897/10000000000 : ℝ)|=(5129903897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564952193/5000000000 : ℝ)|^6079 ≤ (22405550235627/50000000000000 : ℝ)^5055
        have hw : |(2564952193/5000000000 : ℝ)|=(2564952193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_5 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687553287/5000000000 : ℝ)*x 0 + (-14967601/125000000 : ℝ)*x 1 + (1282476039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687553287/5000000000 : ℝ)^6079 ≤ (5924901598611/12500000000000 : ℝ)^5055 := by
    have hnat : (2687553287 : ℕ)^6079*12500000000000^5055 ≤ 5924901598611^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687553287 5000000000 5924901598611 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14967601/125000000 : ℝ)^6079 ≤ (778968913281/10000000000000 : ℝ)^5055 := by
    have hnat : (14967601 : ℕ)^6079*10000000000000^5055 ≤ 778968913281^5055*125000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14967601 125000000 778968913281 10000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282476039/2500000000 : ℝ)^6079 ≤ (44811098055153/100000000000000 : ℝ)^5055 := by
    have hnat : (1282476039 : ℕ)^6079*100000000000000^5055 ≤ 44811098055153^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282476039 2500000000 44811098055153 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687553287/5000000000 : ℝ), (-14967601/125000000 : ℝ), (1282476039/2500000000 : ℝ)] ![(5924901598611/12500000000000 : ℝ), (778968913281/10000000000000 : ℝ), (44811098055153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687553287/5000000000 : ℝ)|^6079 ≤ (5924901598611/12500000000000 : ℝ)^5055
        have hw : |(2687553287/5000000000 : ℝ)|=(2687553287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14967601/125000000 : ℝ)|^6079 ≤ (778968913281/10000000000000 : ℝ)^5055
        have hw : |(-14967601/125000000 : ℝ)|=(14967601/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282476039/2500000000 : ℝ)|^6079 ≤ (44811098055153/100000000000000 : ℝ)^5055
        have hw : |(1282476039/2500000000 : ℝ)|=(1282476039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_6 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537510659/1000000000 : ℝ)*x 0 + (512990421/1000000000 : ℝ)*x 1 + (-1197407987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537510659/1000000000 : ℝ)^6079 ≤ (23699606479281/50000000000000 : ℝ)^5055 := by
    have hnat : (537510659 : ℕ)^6079*50000000000000^5055 ≤ 23699606479281^5055*1000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537510659 1000000000 23699606479281 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512990421/1000000000 : ℝ)^6079 ≤ (11202774655603/25000000000000 : ℝ)^5055 := by
    have hnat : (512990421 : ℕ)^6079*25000000000000^5055 ≤ 11202774655603^5055*1000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512990421 1000000000 11202774655603 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197407987/10000000000 : ℝ)^6079 ≤ (1557937681049/20000000000000 : ℝ)^5055 := by
    have hnat : (1197407987 : ℕ)^6079*20000000000000^5055 ≤ 1557937681049^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197407987 10000000000 1557937681049 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537510659/1000000000 : ℝ), (512990421/1000000000 : ℝ), (-1197407987/10000000000 : ℝ)] ![(23699606479281/50000000000000 : ℝ), (11202774655603/25000000000000 : ℝ), (1557937681049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537510659/1000000000 : ℝ)|^6079 ≤ (23699606479281/50000000000000 : ℝ)^5055
        have hw : |(537510659/1000000000 : ℝ)|=(537510659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512990421/1000000000 : ℝ)|^6079 ≤ (11202774655603/25000000000000 : ℝ)^5055
        have hw : |(512990421/1000000000 : ℝ)|=(512990421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1197407987/10000000000 : ℝ)|^6079 ≤ (1557937681049/20000000000000 : ℝ)^5055
        have hw : |(-1197407987/10000000000 : ℝ)|=(1197407987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_7 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341993993/1000000000 : ℝ)*x 0 + (268738669/625000000 : ℝ)*x 1 + (4299819127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341993993/1000000000 : ℝ)^6079 ≤ (27518439566669/100000000000000 : ℝ)^5055 := by
    have hnat : (341993993 : ℕ)^6079*100000000000000^5055 ≤ 27518439566669^5055*1000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341993993 1000000000 27518439566669 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268738669/625000000 : ℝ)^6079 ≤ (9060194515463/25000000000000 : ℝ)^5055 := by
    have hnat : (268738669 : ℕ)^6079*25000000000000^5055 ≤ 9060194515463^5055*625000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268738669 625000000 9060194515463 25000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4299819127/10000000000 : ℝ)^6079 ≤ (36240782349299/100000000000000 : ℝ)^5055 := by
    have hnat : (4299819127 : ℕ)^6079*100000000000000^5055 ≤ 36240782349299^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299819127 10000000000 36240782349299 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341993993/1000000000 : ℝ), (268738669/625000000 : ℝ), (4299819127/10000000000 : ℝ)] ![(27518439566669/100000000000000 : ℝ), (9060194515463/25000000000000 : ℝ), (36240782349299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341993993/1000000000 : ℝ)|^6079 ≤ (27518439566669/100000000000000 : ℝ)^5055
        have hw : |(341993993/1000000000 : ℝ)|=(341993993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268738669/625000000 : ℝ)|^6079 ≤ (9060194515463/25000000000000 : ℝ)^5055
        have hw : |(268738669/625000000 : ℝ)|=(268738669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4299819127/10000000000 : ℝ)|^6079 ≤ (36240782349299/100000000000000 : ℝ)^5055
        have hw : |(4299819127/10000000000 : ℝ)|=(4299819127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_8 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338928809/2500000000 : ℝ)*x 0 + (4918206367/10000000000 : ℝ)*x 1 + (546547303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338928809/2500000000 : ℝ)^6079 ≤ (452210210923/5000000000000 : ℝ)^5055 := by
    have hnat : (338928809 : ℕ)^6079*5000000000000^5055 ≤ 452210210923^5055*2500000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338928809 2500000000 452210210923 5000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4918206367/10000000000 : ℝ)^6079 ≤ (21298328320699/50000000000000 : ℝ)^5055 := by
    have hnat : (4918206367 : ℕ)^6079*50000000000000^5055 ≤ 21298328320699^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918206367 10000000000 21298328320699 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546547303/1000000000 : ℝ)^6079 ≤ (48359139121857/100000000000000 : ℝ)^5055 := by
    have hnat : (546547303 : ℕ)^6079*100000000000000^5055 ≤ 48359139121857^5055*1000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546547303 1000000000 48359139121857 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338928809/2500000000 : ℝ), (4918206367/10000000000 : ℝ), (546547303/1000000000 : ℝ)] ![(452210210923/5000000000000 : ℝ), (21298328320699/50000000000000 : ℝ), (48359139121857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338928809/2500000000 : ℝ)|^6079 ≤ (452210210923/5000000000000 : ℝ)^5055
        have hw : |(-338928809/2500000000 : ℝ)|=(338928809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4918206367/10000000000 : ℝ)|^6079 ≤ (21298328320699/50000000000000 : ℝ)^5055
        have hw : |(4918206367/10000000000 : ℝ)|=(4918206367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546547303/1000000000 : ℝ)|^6079 ≤ (48359139121857/100000000000000 : ℝ)^5055
        have hw : |(546547303/1000000000 : ℝ)|=(546547303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_9 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576144753/5000000000 : ℝ)*x 0 + (-521265927/5000000000 : ℝ)*x 1 + (5465473363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576144753/5000000000 : ℝ)^6079 ≤ (45046355238351/100000000000000 : ℝ)^5055 := by
    have hnat : (2576144753 : ℕ)^6079*100000000000000^5055 ≤ 45046355238351^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576144753 5000000000 45046355238351 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521265927/5000000000 : ℝ)^6079 ≤ (6594502079509/100000000000000 : ℝ)^5055 := by
    have hnat : (521265927 : ℕ)^6079*100000000000000^5055 ≤ 6594502079509^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521265927 5000000000 6594502079509 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465473363/10000000000 : ℝ)^6079 ≤ (24179571332571/50000000000000 : ℝ)^5055 := by
    have hnat : (5465473363 : ℕ)^6079*50000000000000^5055 ≤ 24179571332571^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465473363 10000000000 24179571332571 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576144753/5000000000 : ℝ), (-521265927/5000000000 : ℝ), (5465473363/10000000000 : ℝ)] ![(45046355238351/100000000000000 : ℝ), (6594502079509/100000000000000 : ℝ), (24179571332571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576144753/5000000000 : ℝ)|^6079 ≤ (45046355238351/100000000000000 : ℝ)^5055
        have hw : |(2576144753/5000000000 : ℝ)|=(2576144753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521265927/5000000000 : ℝ)|^6079 ≤ (6594502079509/100000000000000 : ℝ)^5055
        have hw : |(-521265927/5000000000 : ℝ)|=(521265927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465473363/10000000000 : ℝ)|^6079 ≤ (24179571332571/50000000000000 : ℝ)^5055
        have hw : |(5465473363/10000000000 : ℝ)|=(5465473363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_10 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (322018101/625000000 : ℝ)*x 0 + (1093094667/2000000000 : ℝ)*x 1 + (-521265871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322018101/625000000 : ℝ)^6079 ≤ (45046356394897/100000000000000 : ℝ)^5055 := by
    have hnat : (322018101 : ℕ)^6079*100000000000000^5055 ≤ 45046356394897^5055*625000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322018101 625000000 45046356394897 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093094667/2000000000 : ℝ)^6079 ≤ (6044892795901/12500000000000 : ℝ)^5055 := by
    have hnat : (1093094667 : ℕ)^6079*12500000000000^5055 ≤ 6044892795901^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093094667 2000000000 6044892795901 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521265871/5000000000 : ℝ)^6079 ≤ (824312653443/12500000000000 : ℝ)^5055 := by
    have hnat : (521265871 : ℕ)^6079*12500000000000^5055 ≤ 824312653443^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521265871 5000000000 824312653443 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(322018101/625000000 : ℝ), (1093094667/2000000000 : ℝ), (-521265871/5000000000 : ℝ)] ![(45046356394897/100000000000000 : ℝ), (6044892795901/12500000000000 : ℝ), (824312653443/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(322018101/625000000 : ℝ)|^6079 ≤ (45046356394897/100000000000000 : ℝ)^5055
        have hw : |(322018101/625000000 : ℝ)|=(322018101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093094667/2000000000 : ℝ)|^6079 ≤ (6044892795901/12500000000000 : ℝ)^5055
        have hw : |(1093094667/2000000000 : ℝ)|=(1093094667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521265871/5000000000 : ℝ)|^6079 ≤ (824312653443/12500000000000 : ℝ)^5055
        have hw : |(-521265871/5000000000 : ℝ)|=(521265871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_11 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4732815209/10000000000 : ℝ)*x 0 + (728039333/2000000000 : ℝ)*x 1 + (3640197139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4732815209/10000000000 : ℝ)^6079 ≤ (40673164091281/100000000000000 : ℝ)^5055 := by
    have hnat : (4732815209 : ℕ)^6079*100000000000000^5055 ≤ 40673164091281^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4732815209 10000000000 40673164091281 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (728039333/2000000000 : ℝ)^6079 ≤ (29663415620563/100000000000000 : ℝ)^5055 := by
    have hnat : (728039333 : ℕ)^6079*100000000000000^5055 ≤ 29663415620563^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728039333 2000000000 29663415620563 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3640197139/10000000000 : ℝ)^6079 ≤ (14831710132781/50000000000000 : ℝ)^5055 := by
    have hnat : (3640197139 : ℕ)^6079*50000000000000^5055 ≤ 14831710132781^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640197139 10000000000 14831710132781 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4732815209/10000000000 : ℝ), (728039333/2000000000 : ℝ), (3640197139/10000000000 : ℝ)] ![(40673164091281/100000000000000 : ℝ), (29663415620563/100000000000000 : ℝ), (14831710132781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4732815209/10000000000 : ℝ)|^6079 ≤ (40673164091281/100000000000000 : ℝ)^5055
        have hw : |(4732815209/10000000000 : ℝ)|=(4732815209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(728039333/2000000000 : ℝ)|^6079 ≤ (29663415620563/100000000000000 : ℝ)^5055
        have hw : |(728039333/2000000000 : ℝ)|=(728039333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3640197139/10000000000 : ℝ)|^6079 ≤ (14831710132781/50000000000000 : ℝ)^5055
        have hw : |(3640197139/10000000000 : ℝ)|=(3640197139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_12 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-916011243/10000000000 : ℝ)*x 0 + (1121112809/2000000000 : ℝ)*x 1 + (318779289/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (916011243/10000000000 : ℝ)^6079 ≤ (2822157699359/50000000000000 : ℝ)^5055 := by
    have hnat : (916011243 : ℕ)^6079*50000000000000^5055 ≤ 2822157699359^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916011243 10000000000 2822157699359 50000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121112809/2000000000 : ℝ)^6079 ≤ (6231702573003/12500000000000 : ℝ)^5055 := by
    have hnat : (1121112809 : ℕ)^6079*12500000000000^5055 ≤ 6231702573003^5055*2000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121112809 2000000000 6231702573003 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318779289/625000000 : ℝ)^6079 ≤ (44502063997329/100000000000000 : ℝ)^5055 := by
    have hnat : (318779289 : ℕ)^6079*100000000000000^5055 ≤ 44502063997329^5055*625000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318779289 625000000 44502063997329 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-916011243/10000000000 : ℝ), (1121112809/2000000000 : ℝ), (318779289/625000000 : ℝ)] ![(2822157699359/50000000000000 : ℝ), (6231702573003/12500000000000 : ℝ), (44502063997329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-916011243/10000000000 : ℝ)|^6079 ≤ (2822157699359/50000000000000 : ℝ)^5055
        have hw : |(-916011243/10000000000 : ℝ)|=(916011243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121112809/2000000000 : ℝ)|^6079 ≤ (6231702573003/12500000000000 : ℝ)^5055
        have hw : |(1121112809/2000000000 : ℝ)|=(1121112809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318779289/625000000 : ℝ)|^6079 ≤ (44502063997329/100000000000000 : ℝ)^5055
        have hw : |(318779289/625000000 : ℝ)|=(318779289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_13 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674341999/1250000000 : ℝ)*x 0 + (-1210280019/10000000000 : ℝ)*x 1 + (102009343/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674341999/1250000000 : ℝ)^6079 ≤ (2975465762011/6250000000000 : ℝ)^5055 := by
    have hnat : (674341999 : ℕ)^6079*6250000000000^5055 ≤ 2975465762011^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674341999 1250000000 2975465762011 6250000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210280019/10000000000 : ℝ)^6079 ≤ (986312407437/12500000000000 : ℝ)^5055 := by
    have hnat : (1210280019 : ℕ)^6079*12500000000000^5055 ≤ 986312407437^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210280019 10000000000 986312407437 12500000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102009343/200000000 : ℝ)^6079 ≤ (4450204853131/10000000000000 : ℝ)^5055 := by
    have hnat : (102009343 : ℕ)^6079*10000000000000^5055 ≤ 4450204853131^5055*200000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102009343 200000000 4450204853131 10000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674341999/1250000000 : ℝ), (-1210280019/10000000000 : ℝ), (102009343/200000000 : ℝ)] ![(2975465762011/6250000000000 : ℝ), (986312407437/12500000000000 : ℝ), (4450204853131/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674341999/1250000000 : ℝ)|^6079 ≤ (2975465762011/6250000000000 : ℝ)^5055
        have hw : |(674341999/1250000000 : ℝ)|=(674341999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1210280019/10000000000 : ℝ)|^6079 ≤ (986312407437/12500000000000 : ℝ)^5055
        have hw : |(-1210280019/10000000000 : ℝ)|=(1210280019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102009343/200000000 : ℝ)|^6079 ≤ (4450204853131/10000000000000 : ℝ)^5055
        have hw : |(102009343/200000000 : ℝ)|=(102009343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_14 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394735169/10000000000 : ℝ)*x 0 + (2550233643/5000000000 : ℝ)*x 1 + (-151285119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394735169/10000000000 : ℝ)^6079 ≤ (2975465216133/6250000000000 : ℝ)^5055 := by
    have hnat : (5394735169 : ℕ)^6079*6250000000000^5055 ≤ 2975465216133^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394735169 10000000000 2975465216133 6250000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2550233643/5000000000 : ℝ)^6079 ≤ (44502049958297/100000000000000 : ℝ)^5055 := by
    have hnat : (2550233643 : ℕ)^6079*100000000000000^5055 ≤ 44502049958297^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550233643 5000000000 44502049958297 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151285119/1250000000 : ℝ)^6079 ≤ (1578101314889/20000000000000 : ℝ)^5055 := by
    have hnat : (151285119 : ℕ)^6079*20000000000000^5055 ≤ 1578101314889^5055*1250000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151285119 1250000000 1578101314889 20000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394735169/10000000000 : ℝ), (2550233643/5000000000 : ℝ), (-151285119/1250000000 : ℝ)] ![(2975465216133/6250000000000 : ℝ), (44502049958297/100000000000000 : ℝ), (1578101314889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394735169/10000000000 : ℝ)|^6079 ≤ (2975465216133/6250000000000 : ℝ)^5055
        have hw : |(5394735169/10000000000 : ℝ)|=(5394735169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2550233643/5000000000 : ℝ)|^6079 ≤ (44502049958297/100000000000000 : ℝ)^5055
        have hw : |(2550233643/5000000000 : ℝ)|=(2550233643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151285119/1250000000 : ℝ)|^6079 ≤ (1578101314889/20000000000000 : ℝ)^5055
        have hw : |(-151285119/1250000000 : ℝ)|=(151285119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1769_box_15 (p : ℝ) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1649345169/5000000000 : ℝ)*x 0 + (136168969/312500000 : ℝ)*x 1 + (4357410071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649345169/5000000000 : ℝ)^6079 ≤ (26349426773229/100000000000000 : ℝ)^5055 := by
    have hnat : (1649345169 : ℕ)^6079*100000000000000^5055 ≤ 26349426773229^5055*5000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649345169 5000000000 26349426773229 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136168969/312500000 : ℝ)^6079 ≤ (36825271039361/100000000000000 : ℝ)^5055 := by
    have hnat : (136168969 : ℕ)^6079*100000000000000^5055 ≤ 36825271039361^5055*312500000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136168969 312500000 36825271039361 100000000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4357410071/10000000000 : ℝ)^6079 ≤ (294602417353/800000000000 : ℝ)^5055 := by
    have hnat : (4357410071 : ℕ)^6079*800000000000^5055 ≤ 294602417353^5055*10000000000^6079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357410071 10000000000 294602417353 800000000000 6079 5055 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6079/1024 : ℝ)) 6079 5055 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1649345169/5000000000 : ℝ), (136168969/312500000 : ℝ), (4357410071/10000000000 : ℝ)] ![(26349426773229/100000000000000 : ℝ), (36825271039361/100000000000000 : ℝ), (294602417353/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1649345169/5000000000 : ℝ)|^6079 ≤ (26349426773229/100000000000000 : ℝ)^5055
        have hw : |(1649345169/5000000000 : ℝ)|=(1649345169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136168969/312500000 : ℝ)|^6079 ≤ (36825271039361/100000000000000 : ℝ)^5055
        have hw : |(136168969/312500000 : ℝ)|=(136168969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4357410071/10000000000 : ℝ)|^6079 ≤ (294602417353/800000000000 : ℝ)^5055
        have hw : |(4357410071/10000000000 : ℝ)|=(4357410071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1769_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(69293/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11807/20000 : ℝ) ∧ (41301/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (46619/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17611/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17611/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17611/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17611/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17611/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17611/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9241/100000 : ℝ) ^ (6063/1024 : ℝ) ≤ (37592141896441/50000000000000000000 : ℝ) := by
    have hpowers : (9241/100000 : ℝ)^6063 ≤ (37592141896441/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9241 : ℕ)^6063*50000000000000000000^1024 ≤ 37592141896441^1024*100000^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9241 100000 37592141896441 50000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9241/100000 : ℝ)) (X := (37592141896441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17611/100000 : ℝ) ^ (6063/1024 : ℝ) ≤ (68453200916749/2000000000000000000 : ℝ) := by
    have hpowers : (17611/100000 : ℝ)^6063 ≤ (68453200916749/2000000000000000000 : ℝ)^1024 := by
      have hnat : (17611 : ℕ)^6063*2000000000000000000^1024 ≤ 68453200916749^1024*100000^6063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17611 100000 68453200916749 2000000000000000000 6063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17611/100000 : ℝ)) (X := (68453200916749/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000037592141896441/25000000000000000000 : ℝ) ≤ (500000126981129/500000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (25000037592141896441/25000000000000000000 : ℝ)^1024 ≤ (500000126981129/500000000000000 : ℝ)^6063 := by
      have hnat : (25000037592141896441 : ℕ)^1024*500000000000000^6063 ≤ 500000126981129^6063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000037592141896441 25000000000000000000 500000126981129 500000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000126981129/500000000000000 : ℝ)) (X := (25000037592141896441/25000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25000874461082407583/25000000000000000000 : ℝ) ≤ (10000059075383999/10000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (25000874461082407583/25000000000000000000 : ℝ)^1024 ≤ (10000059075383999/10000000000000000 : ℝ)^6063 := by
      have hnat : (25000874461082407583 : ℕ)^1024*10000000000000000^6063 ≤ 10000059075383999^6063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000874461082407583 25000000000000000000 10000059075383999 10000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000059075383999/10000000000000000 : ℝ)) (X := (25000874461082407583/25000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000068453200916749/1000000000000000000 : ℝ) ≤ (5000057805572709/5000000000000000 : ℝ) ^ (6063/1024 : ℝ) := by
    have hpowers : (1000068453200916749/1000000000000000000 : ℝ)^1024 ≤ (5000057805572709/5000000000000000 : ℝ)^6063 := by
      have hnat : (1000068453200916749 : ℕ)^1024*5000000000000000^6063 ≤ 5000057805572709^6063*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000068453200916749 1000000000000000000 5000057805572709 5000000000000000 1024 6063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000057805572709/5000000000000000 : ℝ)) (X := (1000068453200916749/1000000000000000000 : ℝ)) (by norm_num) 6063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(37592141896441/50000000000000000000 : ℝ) ≤ ((41849488181349224321/41850000000000000000 : ℝ)+2*(56535761419/837000000000000 : ℝ)*(9241/100000 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (41849488181349224321/41850000000000000000 : ℝ)+2*(56535761419/837000000000000 : ℝ)*(9241/100000 : ℝ)=(500000126981129/500000000000000 : ℝ) by norm_num, show 1+2*(37592141896441/50000000000000000000 : ℝ)=(25000037592141896441/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(68453200916749/2000000000000000000 : ℝ)+(37592141896441/50000000000000000000 : ℝ) ≤ ((41849488181349224321/41850000000000000000 : ℝ)+(56535761419/837000000000000 : ℝ)*((17611/100000 : ℝ)+(9241/100000 : ℝ)))^(6063/1024 : ℝ) := by
    rw [show (41849488181349224321/41850000000000000000 : ℝ)+(56535761419/837000000000000 : ℝ)*((17611/100000 : ℝ)+(9241/100000 : ℝ))=(10000059075383999/10000000000000000 : ℝ) by norm_num, show 1+(68453200916749/2000000000000000000 : ℝ)+(37592141896441/50000000000000000000 : ℝ)=(25000874461082407583/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(68453200916749/2000000000000000000 : ℝ) ≤ ((41849488181349224321/41850000000000000000 : ℝ)+2*(56535761419/837000000000000 : ℝ)*(17611/100000 : ℝ))^(6063/1024 : ℝ) := by
    rw [show (41849488181349224321/41850000000000000000 : ℝ)+2*(56535761419/837000000000000 : ℝ)*(17611/100000 : ℝ)=(5000057805572709/5000000000000000 : ℝ) by norm_num, show 1+2*(68453200916749/2000000000000000000 : ℝ)=(1000068453200916749/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41849488181349224321/41850000000000000000 : ℝ)*(X 1 0+X 2 0)+(56535761419/837000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (9241/100000 : ℝ)) (hi := (17611/100000 : ℝ)) (c := (41849488181349224321/41850000000000000000 : ℝ)) (alpha := (56535761419/837000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41849488181349224321/41850000000000000000 : ℝ)*(X 0 1+X 2 1)+(56535761419/837000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (9241/100000 : ℝ)) (hi := (17611/100000 : ℝ)) (c := (41849488181349224321/41850000000000000000 : ℝ)) (alpha := (56535761419/837000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41849488181349224321/41850000000000000000 : ℝ)*(X 0 2+X 1 2)+(56535761419/837000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6063/1024 : ℝ)) (lo := (9241/100000 : ℝ)) (hi := (17611/100000 : ℝ)) (c := (41849488181349224321/41850000000000000000 : ℝ)) (alpha := (56535761419/837000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-766369271/10000000000 : ℝ)*X 0 0+(1351397379/2500000000 : ℝ)*X 0 1+(1351397731/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1297996281/2500000000 : ℝ)*X 1 0+(-535607531/5000000000 : ℝ)*X 1 1+(5405590039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1038396961/2000000000 : ℝ)*X 2 0+(5405590669/10000000000 : ℝ)*X 2 1+(-1071214627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1126767289/2500000000 : ℝ)*X 0 0+(14680727/39062500 : ℝ)*X 0 1+(3758267603/10000000000 : ℝ)*X 0 2+(1126767289/2500000000 : ℝ)*X 1 0+(14680727/39062500 : ℝ)*X 1 1+(3758267603/10000000000 : ℝ)*X 1 2+(1126767289/2500000000 : ℝ)*X 2 0+(14680727/39062500 : ℝ)*X 2 1+(3758267603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1519991933/10000000000 : ℝ)*X 0 0+(5129903897/10000000000 : ℝ)*X 0 1+(2564952193/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687553287/5000000000 : ℝ)*X 1 0+(-14967601/125000000 : ℝ)*X 1 1+(1282476039/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537510659/1000000000 : ℝ)*X 2 0+(512990421/1000000000 : ℝ)*X 2 1+(-1197407987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((341993993/1000000000 : ℝ)*X 0 0+(268738669/625000000 : ℝ)*X 0 1+(4299819127/10000000000 : ℝ)*X 0 2+(341993993/1000000000 : ℝ)*X 1 0+(268738669/625000000 : ℝ)*X 1 1+(4299819127/10000000000 : ℝ)*X 1 2+(341993993/1000000000 : ℝ)*X 2 0+(268738669/625000000 : ℝ)*X 2 1+(4299819127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-338928809/2500000000 : ℝ)*X 0 0+(4918206367/10000000000 : ℝ)*X 0 1+(546547303/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576144753/5000000000 : ℝ)*X 1 0+(-521265927/5000000000 : ℝ)*X 1 1+(5465473363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((322018101/625000000 : ℝ)*X 2 0+(1093094667/2000000000 : ℝ)*X 2 1+(-521265871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4732815209/10000000000 : ℝ)*X 0 0+(728039333/2000000000 : ℝ)*X 0 1+(3640197139/10000000000 : ℝ)*X 0 2+(4732815209/10000000000 : ℝ)*X 1 0+(728039333/2000000000 : ℝ)*X 1 1+(3640197139/10000000000 : ℝ)*X 1 2+(4732815209/10000000000 : ℝ)*X 2 0+(728039333/2000000000 : ℝ)*X 2 1+(3640197139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-916011243/10000000000 : ℝ)*X 0 0+(1121112809/2000000000 : ℝ)*X 0 1+(318779289/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((674341999/1250000000 : ℝ)*X 1 0+(-1210280019/10000000000 : ℝ)*X 1 1+(102009343/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5394735169/10000000000 : ℝ)*X 2 0+(2550233643/5000000000 : ℝ)*X 2 1+(-151285119/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1649345169/5000000000 : ℝ)*X 0 0+(136168969/312500000 : ℝ)*X 0 1+(4357410071/10000000000 : ℝ)*X 0 2+(1649345169/5000000000 : ℝ)*X 1 0+(136168969/312500000 : ℝ)*X 1 1+(4357410071/10000000000 : ℝ)*X 1 2+(1649345169/5000000000 : ℝ)*X 2 0+(136168969/312500000 : ℝ)*X 2 1+(4357410071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1769_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-69293/100000 : ℝ) ≤ (-10740073541179230904573427724979/15500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13038359/100000000000000 : ℝ)*(lower3) + (39653/5000000000000 : ℝ)*(lower4) + (26591003/100000000000000 : ℝ)*(upper5) + (222894535879897/20000000000000 : ℝ)*(major0) + (222894535879897/20000000000000 : ℝ)*(major1) + (222894535879897/20000000000000 : ℝ)*(major2) + (108317159/12500000000000 : ℝ)*(sp1) + (106372817/10000000000000 : ℝ)*(sp2) + (183125147/50000000000000 : ℝ)*(sp3) + (440306625456977/25000000000000 : ℝ)*(sp4) + (880613425862871/50000000000000 : ℝ)*(sp5) + (440306663633711/25000000000000 : ℝ)*(sp6) + (490814206632277/100000000000000 : ℝ)*(sp7) + (608217553/50000000000000 : ℝ)*(sp12) + (122703643220643/25000000000000 : ℝ)*(f.failure) + (880613859131507/50000000000000 : ℝ)*(f.sum) + (50539166743603/8370000000000000000000000000 : ℝ)*base65 + (2105898007525524937/837000000000000000000000000000000 : ℝ)*base67 + (4863780439018524937/837000000000000000000000000000000 : ℝ)*base69 + (5915541232789524937/837000000000000000000000000000000 : ℝ)*base71 + (594789504403/8370000000000000000000000000 : ℝ)*base73 + (3146341203682524937/837000000000000000000000000000000 : ℝ)*base75 + (2588709654151524937/837000000000000000000000000000000 : ℝ)*base77 + (5629820572537524937/837000000000000000000000000000000 : ℝ)*base79 + (70744712587933/8370000000000000000000000000 : ℝ)*base81 + (16213633/2500000000000000000000 : ℝ)*base89 + (16213633/2500000000000000000000 : ℝ)*base91 + (16213633/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11807/20000 : ℝ) ≤ (22876844200269313354939757486131/38750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41886991/50000000000000 : ℝ)*(upper2) + (61917321/100000000000000 : ℝ)*(upper4) + (27487919/20000000000000 : ℝ)*(upper5) + (1249361145715501/100000000000000 : ℝ)*(major0) + (1249361145715501/100000000000000 : ℝ)*(major1) + (1249361145715501/100000000000000 : ℝ)*(major2) + (60275620559473/3125000000000 : ℝ)*(sp0) + (964407491553669/50000000000000 : ℝ)*(sp1) + (964411732725169/50000000000000 : ℝ)*(sp2) + (550217000179849/100000000000000 : ℝ)*(sp3) + (134676023/50000000000000 : ℝ)*(sp6) + (4375847523/50000000000000 : ℝ)*(sp9) + (1275342547/50000000000000 : ℝ)*(sp11) + (242306203/6250000000000 : ℝ)*(sp12) + (550219550864943/100000000000000 : ℝ)*(f.failure) + (120551483425149/6250000000000 : ℝ)*(f.sum) + (39896700738581/41850000000000000000000000000 : ℝ)*base66 + (19630182472901849821/4185000000000000000000000000000000 : ℝ)*base67 + (5777993616326849821/4185000000000000000000000000000000 : ℝ)*base69 + (37142690183261849821/4185000000000000000000000000000000 : ℝ)*base71 + (43534815273619/41850000000000000000000000000 : ℝ)*base73 + (5331314069486849821/4185000000000000000000000000000000 : ℝ)*base75 + (2420081942508150179/4185000000000000000000000000000000 : ℝ)*base78 + (5644961041391849821/4185000000000000000000000000000000 : ℝ)*base79 + (34612707811331/41850000000000000000000000000 : ℝ)*base82 + (37556933/10000000000000000000000 : ℝ)*base89 + (37556933/10000000000000000000000 : ℝ)*base91 + (37556933/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (41301/50000 : ℝ) ≤ (640187532263622696490552249/775000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31055369/100000000000000 : ℝ)*(upper0) + (2039063/100000000000000 : ℝ)*(lower1) + (8159687/100000000000000 : ℝ)*(lower3) + (6421931/25000000000000 : ℝ)*(upper4) + (594639128958663/50000000000000 : ℝ)*(major0) + (594639128958663/50000000000000 : ℝ)*(major1) + (594639128958663/50000000000000 : ℝ)*(major2) + (11183157899/100000000000000 : ℝ)*(sp1) + (1259096453/10000000000000 : ℝ)*(sp2) + (1159557663/50000000000000 : ℝ)*(sp3) + (913631282261897/50000000000000 : ℝ)*(sp8) + (365450276273179/20000000000000 : ℝ)*(sp9) + (57101561673727/3125000000000 : ℝ)*(sp10) + (130939171142821/25000000000000 : ℝ)*(sp11) + (52375900368661/10000000000000 : ℝ)*(f.failure) + (913631282261897/50000000000000 : ℝ)*(f.sum) + (11741088942701/6975000000000000000000000000 : ℝ)*base66 + (1448473731146030941/697500000000000000000000000000000 : ℝ)*base67 + (3037993156106030941/697500000000000000000000000000000 : ℝ)*base69 + (1224303573483969059/697500000000000000000000000000000 : ℝ)*base72 + (24480148562801/6975000000000000000000000000 : ℝ)*base74 + (1270776214278969059/697500000000000000000000000000000 : ℝ)*base76 + (2391622269236030941/697500000000000000000000000000000 : ℝ)*base77 + (3809559998223969059/697500000000000000000000000000000 : ℝ)*base80 + (24307137538001/6975000000000000000000000000 : ℝ)*base82 + (6811609/1000000000000000000000 : ℝ)*base90 + (6811609/1000000000000000000000 : ℝ)*base92 + (6811609/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-46619/50000 : ℝ) ≤ (-10838689818387469742508925069703/11625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52924191/50000000000000 : ℝ)*(upper3) + (133841157/50000000000000 : ℝ)*(lower4) + (158384393/100000000000000 : ℝ)*(upper5) + (62476188035943/5000000000000 : ℝ)*(major0) + (62476188035943/5000000000000 : ℝ)*(major1) + (62476188035943/5000000000000 : ℝ)*(major2) + (8504886101/100000000000000 : ℝ)*(sp4) + (143598451083/100000000000000 : ℝ)*(sp5) + (98483260683/50000000000000 : ℝ)*(sp6) + (56167024149/100000000000000 : ℝ)*(sp7) + (1979826530404583/100000000000000 : ℝ)*(sp12) + (1979691436839601/100000000000000 : ℝ)*(sp13) + (989819034384659/50000000000000 : ℝ)*(sp14) + (275117499802857/50000000000000 : ℝ)*(sp15) + (550291166629863/100000000000000 : ℝ)*(f.failure) + (494958758822671/25000000000000 : ℝ)*(f.sum) + (404359388539/697500000000000000000000000 : ℝ)*base65 + (125979643534539901/69750000000000000000000000000000 : ℝ)*base67 + (364705578173289901/69750000000000000000000000000000 : ℝ)*base69 + (466504772638539901/69750000000000000000000000000000 : ℝ)*base71 + (2529422128777/1395000000000000000000000000 : ℝ)*base74 + (295209097103289901/69750000000000000000000000000000 : ℝ)*base75 + (366845425240539901/69750000000000000000000000000000 : ℝ)*base77 + (376463892208539901/69750000000000000000000000000000 : ℝ)*base79 + (1099364740673/1395000000000000000000000000 : ℝ)*base81 + (25502547/10000000000000000000000 : ℝ)*base90 + (25502547/10000000000000000000000 : ℝ)*base92 + (25502547/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1769_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69293/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11807/20000 : ℝ) else (41301/50000 : ℝ) ≤ X j i ∧ X j i ≤ (46619/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1769_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1769_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69293/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11807/20000 : ℝ) else (41301/50000 : ℝ) ≤ X j i ∧ X j i ≤ (46619/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1769_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6063/1024 : ℝ) ≤ p) (hpb : p ≤ (6079/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227065931/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17611/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69293/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11807/20000 : ℝ) else (41301/50000 : ℝ) ≤ X j i ∧ X j i ≤ (46619/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1769_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
