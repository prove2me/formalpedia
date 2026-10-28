-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1183_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:20.995035+00:00
-- url     : https://prove2.me/submissions/2dd13cd4-d6ce-45f8-8c80-906bba4bab43

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
theorem support_rectangle_w1183_s0_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878901901/10000000000 : ℝ)*x 0 + (6044902399/10000000000 : ℝ)*x 1 + (4785635719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878901901/10000000000 : ℝ)^1047 ≤ (5468645069211/50000000000000 : ℝ)^791 := by
    have hnat : (1878901901 : ℕ)^1047*50000000000000^791 ≤ 5468645069211^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878901901 10000000000 5468645069211 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6044902399/10000000000 : ℝ)^1047 ≤ (51361525451809/100000000000000 : ℝ)^791 := by
    have hnat : (6044902399 : ℕ)^1047*100000000000000^791 ≤ 51361525451809^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6044902399 10000000000 51361525451809 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785635719/10000000000 : ℝ)^1047 ≤ (18850592194133/50000000000000 : ℝ)^791 := by
    have hnat : (4785635719 : ℕ)^1047*50000000000000^791 ≤ 18850592194133^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785635719 10000000000 18850592194133 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878901901/10000000000 : ℝ), (6044902399/10000000000 : ℝ), (4785635719/10000000000 : ℝ)] ![(5468645069211/50000000000000 : ℝ), (51361525451809/100000000000000 : ℝ), (18850592194133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878901901/10000000000 : ℝ)|^1047 ≤ (5468645069211/50000000000000 : ℝ)^791
        have hw : |(-1878901901/10000000000 : ℝ)|=(1878901901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6044902399/10000000000 : ℝ)|^1047 ≤ (51361525451809/100000000000000 : ℝ)^791
        have hw : |(6044902399/10000000000 : ℝ)|=(6044902399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785635719/10000000000 : ℝ)|^1047 ≤ (18850592194133/50000000000000 : ℝ)^791
        have hw : |(4785635719/10000000000 : ℝ)|=(4785635719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2757241847/5000000000 : ℝ)*x 0 + (-2600423479/10000000000 : ℝ)*x 1 + (4785635719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757241847/5000000000 : ℝ)^1047 ≤ (45482595532897/100000000000000 : ℝ)^791 := by
    have hnat : (2757241847 : ℕ)^1047*100000000000000^791 ≤ 45482595532897^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757241847 5000000000 45482595532897 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600423479/10000000000 : ℝ)^1047 ≤ (3363244013413/20000000000000 : ℝ)^791 := by
    have hnat : (2600423479 : ℕ)^1047*20000000000000^791 ≤ 3363244013413^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600423479 10000000000 3363244013413 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785635719/10000000000 : ℝ)^1047 ≤ (18850592194133/50000000000000 : ℝ)^791 := by
    have hnat : (4785635719 : ℕ)^1047*50000000000000^791 ≤ 18850592194133^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785635719 10000000000 18850592194133 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757241847/5000000000 : ℝ), (-2600423479/10000000000 : ℝ), (4785635719/10000000000 : ℝ)] ![(45482595532897/100000000000000 : ℝ), (3363244013413/20000000000000 : ℝ), (18850592194133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757241847/5000000000 : ℝ)|^1047 ≤ (45482595532897/100000000000000 : ℝ)^791
        have hw : |(2757241847/5000000000 : ℝ)|=(2757241847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2600423479/10000000000 : ℝ)|^1047 ≤ (3363244013413/20000000000000 : ℝ)^791
        have hw : |(-2600423479/10000000000 : ℝ)|=(2600423479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785635719/10000000000 : ℝ)|^1047 ≤ (18850592194133/50000000000000 : ℝ)^791
        have hw : |(4785635719/10000000000 : ℝ)|=(4785635719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1378620919/2500000000 : ℝ)*x 0 + (191425429/400000000 : ℝ)*x 1 + (-520084699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378620919/2500000000 : ℝ)^1047 ≤ (11370648834097/25000000000000 : ℝ)^791 := by
    have hnat : (1378620919 : ℕ)^1047*25000000000000^791 ≤ 11370648834097^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378620919 2500000000 11370648834097 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191425429/400000000 : ℝ)^1047 ≤ (37701184450831/100000000000000 : ℝ)^791 := by
    have hnat : (191425429 : ℕ)^1047*100000000000000^791 ≤ 37701184450831^791*400000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191425429 400000000 37701184450831 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520084699/2000000000 : ℝ)^1047 ≤ (16816220204019/100000000000000 : ℝ)^791 := by
    have hnat : (520084699 : ℕ)^1047*100000000000000^791 ≤ 16816220204019^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520084699 2000000000 16816220204019 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378620919/2500000000 : ℝ), (191425429/400000000 : ℝ), (-520084699/2000000000 : ℝ)] ![(11370648834097/25000000000000 : ℝ), (37701184450831/100000000000000 : ℝ), (16816220204019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378620919/2500000000 : ℝ)|^1047 ≤ (11370648834097/25000000000000 : ℝ)^791
        have hw : |(1378620919/2500000000 : ℝ)|=(1378620919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191425429/400000000 : ℝ)|^1047 ≤ (37701184450831/100000000000000 : ℝ)^791
        have hw : |(191425429/400000000 : ℝ)|=(191425429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520084699/2000000000 : ℝ)|^1047 ≤ (16816220204019/100000000000000 : ℝ)^791
        have hw : |(-520084699/2000000000 : ℝ)|=(520084699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2098847549/5000000000 : ℝ)*x 0 + (3119254873/10000000000 : ℝ)*x 1 + (5644696461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098847549/5000000000 : ℝ)^1047 ≤ (31695803986881/100000000000000 : ℝ)^791 := by
    have hnat : (2098847549 : ℕ)^1047*100000000000000^791 ≤ 31695803986881^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098847549 5000000000 31695803986881 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119254873/10000000000 : ℝ)^1047 ≤ (10697320344683/50000000000000 : ℝ)^791 := by
    have hnat : (3119254873 : ℕ)^1047*50000000000000^791 ≤ 10697320344683^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119254873 10000000000 10697320344683 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644696461/10000000000 : ℝ)^1047 ≤ (46909555309101/100000000000000 : ℝ)^791 := by
    have hnat : (5644696461 : ℕ)^1047*100000000000000^791 ≤ 46909555309101^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644696461 10000000000 46909555309101 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098847549/5000000000 : ℝ), (3119254873/10000000000 : ℝ), (5644696461/10000000000 : ℝ)] ![(31695803986881/100000000000000 : ℝ), (10697320344683/50000000000000 : ℝ), (46909555309101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098847549/5000000000 : ℝ)|^1047 ≤ (31695803986881/100000000000000 : ℝ)^791
        have hw : |(2098847549/5000000000 : ℝ)|=(2098847549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119254873/10000000000 : ℝ)|^1047 ≤ (10697320344683/50000000000000 : ℝ)^791
        have hw : |(3119254873/10000000000 : ℝ)|=(3119254873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5644696461/10000000000 : ℝ)|^1047 ≤ (46909555309101/100000000000000 : ℝ)^791
        have hw : |(5644696461/10000000000 : ℝ)|=(5644696461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-235490993/1250000000 : ℝ)*x 0 + (96361989/200000000 : ℝ)*x 1 + (601129437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235490993/1250000000 : ℝ)^1047 ≤ (2744008209157/25000000000000 : ℝ)^791 := by
    have hnat : (235490993 : ℕ)^1047*25000000000000^791 ≤ 2744008209157^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235490993 1250000000 2744008209157 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96361989/200000000 : ℝ)^1047 ≤ (38040075152111/100000000000000 : ℝ)^791 := by
    have hnat : (96361989 : ℕ)^1047*100000000000000^791 ≤ 38040075152111^791*200000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96361989 200000000 38040075152111 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601129437/1000000000 : ℝ)^1047 ≤ (3186493249381/6250000000000 : ℝ)^791 := by
    have hnat : (601129437 : ℕ)^1047*6250000000000^791 ≤ 3186493249381^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601129437 1000000000 3186493249381 6250000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235490993/1250000000 : ℝ), (96361989/200000000 : ℝ), (601129437/1000000000 : ℝ)] ![(2744008209157/25000000000000 : ℝ), (38040075152111/100000000000000 : ℝ), (3186493249381/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235490993/1250000000 : ℝ)|^1047 ≤ (2744008209157/25000000000000 : ℝ)^791
        have hw : |(-235490993/1250000000 : ℝ)|=(235490993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96361989/200000000 : ℝ)|^1047 ≤ (38040075152111/100000000000000 : ℝ)^791
        have hw : |(96361989/200000000 : ℝ)|=(96361989/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601129437/1000000000 : ℝ)|^1047 ≤ (3186493249381/6250000000000 : ℝ)^791
        have hw : |(601129437/1000000000 : ℝ)|=(601129437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2586059151/5000000000 : ℝ)*x 0 + (-687382527/5000000000 : ℝ)*x 1 + (6011294067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586059151/5000000000 : ℝ)^1047 ≤ (41783020499967/100000000000000 : ℝ)^791 := by
    have hnat : (2586059151 : ℕ)^1047*100000000000000^791 ≤ 41783020499967^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586059151 5000000000 41783020499967 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687382527/5000000000 : ℝ)^1047 ≤ (1808272723157/25000000000000 : ℝ)^791 := by
    have hnat : (687382527 : ℕ)^1047*25000000000000^791 ≤ 1808272723157^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687382527 5000000000 1808272723157 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6011294067/10000000000 : ℝ)^1047 ≤ (25491944294269/50000000000000 : ℝ)^791 := by
    have hnat : (6011294067 : ℕ)^1047*50000000000000^791 ≤ 25491944294269^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011294067 10000000000 25491944294269 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586059151/5000000000 : ℝ), (-687382527/5000000000 : ℝ), (6011294067/10000000000 : ℝ)] ![(41783020499967/100000000000000 : ℝ), (1808272723157/25000000000000 : ℝ), (25491944294269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586059151/5000000000 : ℝ)|^1047 ≤ (41783020499967/100000000000000 : ℝ)^791
        have hw : |(2586059151/5000000000 : ℝ)|=(2586059151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-687382527/5000000000 : ℝ)|^1047 ≤ (1808272723157/25000000000000 : ℝ)^791
        have hw : |(-687382527/5000000000 : ℝ)|=(687382527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6011294067/10000000000 : ℝ)|^1047 ≤ (25491944294269/50000000000000 : ℝ)^791
        have hw : |(6011294067/10000000000 : ℝ)|=(6011294067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1293029561/2500000000 : ℝ)*x 0 + (6011294229/10000000000 : ℝ)*x 1 + (-687382441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293029561/2500000000 : ℝ)^1047 ≤ (4178301987977/10000000000000 : ℝ)^791 := by
    have hnat : (1293029561 : ℕ)^1047*10000000000000^791 ≤ 4178301987977^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293029561 2500000000 4178301987977 10000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6011294229/10000000000 : ℝ)^1047 ≤ (50983890407193/100000000000000 : ℝ)^791 := by
    have hnat : (6011294229 : ℕ)^1047*100000000000000^791 ≤ 50983890407193^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011294229 10000000000 50983890407193 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687382441/5000000000 : ℝ)^1047 ≤ (7233089694801/100000000000000 : ℝ)^791 := by
    have hnat : (687382441 : ℕ)^1047*100000000000000^791 ≤ 7233089694801^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687382441 5000000000 7233089694801 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293029561/2500000000 : ℝ), (6011294229/10000000000 : ℝ), (-687382441/5000000000 : ℝ)] ![(4178301987977/10000000000000 : ℝ), (50983890407193/100000000000000 : ℝ), (7233089694801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293029561/2500000000 : ℝ)|^1047 ≤ (4178301987977/10000000000000 : ℝ)^791
        have hw : |(1293029561/2500000000 : ℝ)|=(1293029561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6011294229/10000000000 : ℝ)|^1047 ≤ (50983890407193/100000000000000 : ℝ)^791
        have hw : |(6011294229/10000000000 : ℝ)|=(6011294229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-687382441/5000000000 : ℝ)|^1047 ≤ (7233089694801/100000000000000 : ℝ)^791
        have hw : |(-687382441/5000000000 : ℝ)|=(687382441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s0_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2103887411/5000000000 : ℝ)*x 0 + (1115918099/2000000000 : ℝ)*x 1 + (637331129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103887411/5000000000 : ℝ)^1047 ≤ (6359316982907/20000000000000 : ℝ)^791 := by
    have hnat : (2103887411 : ℕ)^1047*20000000000000^791 ≤ 6359316982907^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103887411 5000000000 6359316982907 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115918099/2000000000 : ℝ)^1047 ≤ (23097366379257/50000000000000 : ℝ)^791 := by
    have hnat : (1115918099 : ℕ)^1047*50000000000000^791 ≤ 23097366379257^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115918099 2000000000 23097366379257 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637331129/2000000000 : ℝ)^1047 ≤ (687771322163/3125000000000 : ℝ)^791 := by
    have hnat : (637331129 : ℕ)^1047*3125000000000^791 ≤ 687771322163^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637331129 2000000000 687771322163 3125000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103887411/5000000000 : ℝ), (1115918099/2000000000 : ℝ), (637331129/2000000000 : ℝ)] ![(6359316982907/20000000000000 : ℝ), (23097366379257/50000000000000 : ℝ), (687771322163/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103887411/5000000000 : ℝ)|^1047 ≤ (6359316982907/20000000000000 : ℝ)^791
        have hw : |(2103887411/5000000000 : ℝ)|=(2103887411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115918099/2000000000 : ℝ)|^1047 ≤ (23097366379257/50000000000000 : ℝ)^791
        have hw : |(1115918099/2000000000 : ℝ)|=(1115918099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637331129/2000000000 : ℝ)|^1047 ≤ (687771322163/3125000000000 : ℝ)^791
        have hw : |(637331129/2000000000 : ℝ)|=(637331129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (581/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27659/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8375/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8375 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8375*1^2048 ≤ 0^2048*1^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8375/2048 : ℝ) ≤ (294843706638203401/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8375 ≤ (294843706638203401/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8375*12500000000000000000^2048 ≤ 294843706638203401^2048*5^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 294843706638203401 12500000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (294843706638203401/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8375 := by
      have hnat : (1 : ℕ)^2048*1^8375 ≤ 1^8375*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12794843706638203401/12500000000000000000 : ℝ) ≤ (2011434658926957/2000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (12794843706638203401/12500000000000000000 : ℝ)^2048 ≤ (2011434658926957/2000000000000000 : ℝ)^8375 := by
      have hnat : (12794843706638203401 : ℕ)^2048*2000000000000000^8375 ≤ 2011434658926957^8375*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12794843706638203401 12500000000000000000 2011434658926957 2000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011434658926957/2000000000000000 : ℝ)) (X := (12794843706638203401/12500000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6544843706638203401/6250000000000000000 : ℝ) ≤ (1011434658926957/1000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (6544843706638203401/6250000000000000000 : ℝ)^2048 ≤ (1011434658926957/1000000000000000 : ℝ)^8375 := by
      have hnat : (6544843706638203401 : ℕ)^2048*1000000000000000^8375 ≤ 1011434658926957^8375*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6544843706638203401 6250000000000000000 1011434658926957 1000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011434658926957/1000000000000000 : ℝ)) (X := (6544843706638203401/6250000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11434658926957/800000000000000 : ℝ)*(0 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11434658926957/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(294843706638203401/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11434658926957/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11434658926957/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011434658926957/2000000000000000 : ℝ) by norm_num, show 1+(294843706638203401/12500000000000000000 : ℝ)+(0 : ℝ)=(12794843706638203401/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(294843706638203401/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11434658926957/800000000000000 : ℝ)*(2/5 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11434658926957/800000000000000 : ℝ)*(2/5 : ℝ)=(1011434658926957/1000000000000000 : ℝ) by norm_num, show 1+2*(294843706638203401/12500000000000000000 : ℝ)=(6544843706638203401/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11434658926957/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11434658926957/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11434658926957/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11434658926957/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11434658926957/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11434658926957/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1878901901/10000000000 : ℝ)*X 0 0+(6044902399/10000000000 : ℝ)*X 0 1+(4785635719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757241847/5000000000 : ℝ)*X 1 0+(-2600423479/10000000000 : ℝ)*X 1 1+(4785635719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378620919/2500000000 : ℝ)*X 2 0+(191425429/400000000 : ℝ)*X 2 1+(-520084699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098847549/5000000000 : ℝ)*X 0 0+(3119254873/10000000000 : ℝ)*X 0 1+(5644696461/10000000000 : ℝ)*X 0 2+(2098847549/5000000000 : ℝ)*X 1 0+(3119254873/10000000000 : ℝ)*X 1 1+(5644696461/10000000000 : ℝ)*X 1 2+(2098847549/5000000000 : ℝ)*X 2 0+(3119254873/10000000000 : ℝ)*X 2 1+(5644696461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235490993/1250000000 : ℝ)*X 0 0+(96361989/200000000 : ℝ)*X 0 1+(601129437/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586059151/5000000000 : ℝ)*X 1 0+(-687382527/5000000000 : ℝ)*X 1 1+(6011294067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293029561/2500000000 : ℝ)*X 2 0+(6011294229/10000000000 : ℝ)*X 2 1+(-687382441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103887411/5000000000 : ℝ)*X 0 0+(1115918099/2000000000 : ℝ)*X 0 1+(637331129/2000000000 : ℝ)*X 0 2+(2103887411/5000000000 : ℝ)*X 1 0+(1115918099/2000000000 : ℝ)*X 1 1+(637331129/2000000000 : ℝ)*X 1 2+(2103887411/5000000000 : ℝ)*X 2 0+(1115918099/2000000000 : ℝ)*X 2 1+(637331129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101862712511156081506119/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10783109/20000000000000 : ℝ)*(base1) + (312611147/25000000000000 : ℝ)*(base19) + (581415521/50000000000000 : ℝ)*(base23) + (42510719/50000000000000 : ℝ)*(base24) + (72026113/25000000000000 : ℝ)*(upper3) + (595046977935563/100000000000000 : ℝ)*(major0) + (595046977935563/100000000000000 : ℝ)*(major1) + (595046977935563/100000000000000 : ℝ)*(major2) + (794117187099951/100000000000000 : ℝ)*(sp0) + (794118641427087/100000000000000 : ℝ)*(sp1) + (158823728803839/20000000000000 : ℝ)*(sp2) + (395971641320913/100000000000000 : ℝ)*(sp3) + (2758687269/100000000000000 : ℝ)*(sp4) + (1099495901/50000000000000 : ℝ)*(sp7) + (19798694711413/5000000000000 : ℝ)*(f.failure) + (31764795674867/4000000000000 : ℝ)*(f.sum) + (71449007568209/40000000000000000000000000000 : ℝ)*base66 + (265352573368209/80000000000000000000000000000 : ℝ)*base68 + (600534248888209/80000000000000000000000000000 : ℝ)*base70 + (180444378008209/80000000000000000000000000000 : ℝ)*base72 + (87643544968209/40000000000000000000000000000 : ℝ)*base74 + (634309869208209/80000000000000000000000000000 : ℝ)*base76 + (316983693368209/80000000000000000000000000000 : ℝ)*base78 + (108085123448209/80000000000000000000000000000 : ℝ)*base80 + (18308316648209/40000000000000000000000000000 : ℝ)*base82 + (405767/100000000000000000000 : ℝ)*base89 + (405767/100000000000000000000 : ℝ)*base91 + (405767/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79683755872687479528567/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10838107/12500000000000 : ℝ)*(base1) + (499835927/25000000000000 : ℝ)*(base19) + (498275031/25000000000000 : ℝ)*(base23) + (27078557/12500000000000 : ℝ)*(upper3) + (238229893/100000000000000 : ℝ)*(upper5) + (156997907101141/25000000000000 : ℝ)*(major0) + (156997907101141/25000000000000 : ℝ)*(major1) + (156997907101141/25000000000000 : ℝ)*(major2) + (2053329569/50000000000000 : ℝ)*(sp1) + (4154316281/100000000000000 : ℝ)*(sp2) + (104760771563689/12500000000000 : ℝ)*(sp4) + (838079979801809/100000000000000 : ℝ)*(sp5) + (3352319753553/400000000000 : ℝ)*(sp6) + (41789681868709/10000000000000 : ℝ)*(sp7) + (208948452695973/50000000000000 : ℝ)*(f.failure) + (52380380362791/6250000000000 : ℝ)*(f.sum) + (6359083837937/10000000000000000000000000000 : ℝ)*base65 + (95113971357937/20000000000000000000000000000 : ℝ)*base67 + (34165879442063/20000000000000000000000000000 : ℝ)*base70 + (100174488957937/20000000000000000000000000000 : ℝ)*base71 + (25928272737937/10000000000000000000000000000 : ℝ)*base73 + (114012720857937/20000000000000000000000000000 : ℝ)*base75 + (93833331637937/20000000000000000000000000000 : ℝ)*base77 + (191070379857937/20000000000000000000000000000 : ℝ)*base79 + (15105114192063/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1617193/1000000000000000000000 : ℝ)*base90 + (1617193/1000000000000000000000 : ℝ)*base92 + (1617193/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1183_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (581/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27659/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1183_s1_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080595373/10000000000 : ℝ)*x 0 + (2845348943/5000000000 : ℝ)*x 1 + (1002145661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080595373/10000000000 : ℝ)^1047 ≤ (625885977481/5000000000000 : ℝ)^791 := by
    have hnat : (2080595373 : ℕ)^1047*5000000000000^791 ≤ 625885977481^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080595373 10000000000 625885977481 5000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2845348943/5000000000 : ℝ)^1047 ≤ (474162350149/1000000000000 : ℝ)^791 := by
    have hnat : (2845348943 : ℕ)^1047*1000000000000^791 ≤ 474162350149^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845348943 5000000000 474162350149 1000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002145661/2000000000 : ℝ)^1047 ≤ (40066045426041/100000000000000 : ℝ)^791 := by
    have hnat : (1002145661 : ℕ)^1047*100000000000000^791 ≤ 40066045426041^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002145661 2000000000 40066045426041 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080595373/10000000000 : ℝ), (2845348943/5000000000 : ℝ), (1002145661/2000000000 : ℝ)] ![(625885977481/5000000000000 : ℝ), (474162350149/1000000000000 : ℝ), (40066045426041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080595373/10000000000 : ℝ)|^1047 ≤ (625885977481/5000000000000 : ℝ)^791
        have hw : |(-2080595373/10000000000 : ℝ)|=(2080595373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2845348943/5000000000 : ℝ)|^1047 ≤ (474162350149/1000000000000 : ℝ)^791
        have hw : |(2845348943/5000000000 : ℝ)|=(2845348943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002145661/2000000000 : ℝ)|^1047 ≤ (40066045426041/100000000000000 : ℝ)^791
        have hw : |(1002145661/2000000000 : ℝ)|=(1002145661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5416877371/10000000000 : ℝ)*x 0 + (-1223392531/5000000000 : ℝ)*x 1 + (1252682131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416877371/10000000000 : ℝ)^1047 ≤ (11105018452179/25000000000000 : ℝ)^791 := by
    have hnat : (5416877371 : ℕ)^1047*25000000000000^791 ≤ 11105018452179^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416877371 10000000000 11105018452179 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1223392531/5000000000 : ℝ)^1047 ≤ (7756939221633/50000000000000 : ℝ)^791 := by
    have hnat : (1223392531 : ℕ)^1047*50000000000000^791 ≤ 7756939221633^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223392531 5000000000 7756939221633 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252682131/2500000000 : ℝ)^1047 ≤ (8013209548783/20000000000000 : ℝ)^791 := by
    have hnat : (1252682131 : ℕ)^1047*20000000000000^791 ≤ 8013209548783^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252682131 2500000000 8013209548783 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416877371/10000000000 : ℝ), (-1223392531/5000000000 : ℝ), (1252682131/2500000000 : ℝ)] ![(11105018452179/25000000000000 : ℝ), (7756939221633/50000000000000 : ℝ), (8013209548783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416877371/10000000000 : ℝ)|^1047 ≤ (11105018452179/25000000000000 : ℝ)^791
        have hw : |(5416877371/10000000000 : ℝ)|=(5416877371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1223392531/5000000000 : ℝ)|^1047 ≤ (7756939221633/50000000000000 : ℝ)^791
        have hw : |(-1223392531/5000000000 : ℝ)|=(1223392531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252682131/2500000000 : ℝ)|^1047 ≤ (8013209548783/20000000000000 : ℝ)^791
        have hw : |(1252682131/2500000000 : ℝ)|=(1252682131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2708438277/5000000000 : ℝ)*x 0 + (2505364537/5000000000 : ℝ)*x 1 + (-2446785423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708438277/5000000000 : ℝ)^1047 ≤ (2221003247039/5000000000000 : ℝ)^791 := by
    have hnat : (2708438277 : ℕ)^1047*5000000000000^791 ≤ 2221003247039^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708438277 5000000000 2221003247039 5000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2505364537/5000000000 : ℝ)^1047 ≤ (20033026782531/50000000000000 : ℝ)^791 := by
    have hnat : (2505364537 : ℕ)^1047*50000000000000^791 ≤ 20033026782531^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505364537 5000000000 20033026782531 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2446785423/10000000000 : ℝ)^1047 ≤ (15513881472983/100000000000000 : ℝ)^791 := by
    have hnat : (2446785423 : ℕ)^1047*100000000000000^791 ≤ 15513881472983^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446785423 10000000000 15513881472983 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708438277/5000000000 : ℝ), (2505364537/5000000000 : ℝ), (-2446785423/10000000000 : ℝ)] ![(2221003247039/5000000000000 : ℝ), (20033026782531/50000000000000 : ℝ), (15513881472983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708438277/5000000000 : ℝ)|^1047 ≤ (2221003247039/5000000000000 : ℝ)^791
        have hw : |(2708438277/5000000000 : ℝ)|=(2708438277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2505364537/5000000000 : ℝ)|^1047 ≤ (20033026782531/50000000000000 : ℝ)^791
        have hw : |(2505364537/5000000000 : ℝ)|=(2505364537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2446785423/10000000000 : ℝ)|^1047 ≤ (15513881472983/100000000000000 : ℝ)^791
        have hw : |(-2446785423/10000000000 : ℝ)|=(2446785423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2156971309/5000000000 : ℝ)*x 0 + (28786429/78125000 : ℝ)*x 1 + (5048332433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156971309/5000000000 : ℝ)^1047 ≤ (6572562854827/20000000000000 : ℝ)^791 := by
    have hnat : (2156971309 : ℕ)^1047*20000000000000^791 ≤ 6572562854827^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156971309 5000000000 6572562854827 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28786429/78125000 : ℝ)^1047 ≤ (26672659348553/100000000000000 : ℝ)^791 := by
    have hnat : (28786429 : ℕ)^1047*100000000000000^791 ≤ 26672659348553^791*78125000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28786429 78125000 26672659348553 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5048332433/10000000000 : ℝ)^1047 ≤ (10116131591069/25000000000000 : ℝ)^791 := by
    have hnat : (5048332433 : ℕ)^1047*25000000000000^791 ≤ 10116131591069^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5048332433 10000000000 10116131591069 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156971309/5000000000 : ℝ), (28786429/78125000 : ℝ), (5048332433/10000000000 : ℝ)] ![(6572562854827/20000000000000 : ℝ), (26672659348553/100000000000000 : ℝ), (10116131591069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156971309/5000000000 : ℝ)|^1047 ≤ (6572562854827/20000000000000 : ℝ)^791
        have hw : |(2156971309/5000000000 : ℝ)|=(2156971309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28786429/78125000 : ℝ)|^1047 ≤ (26672659348553/100000000000000 : ℝ)^791
        have hw : |(28786429/78125000 : ℝ)|=(28786429/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5048332433/10000000000 : ℝ)|^1047 ≤ (10116131591069/25000000000000 : ℝ)^791
        have hw : |(5048332433/10000000000 : ℝ)|=(5048332433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1040673393/5000000000 : ℝ)*x 0 + (313741781/625000000 : ℝ)*x 1 + (5681378817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040673393/5000000000 : ℝ)^1047 ≤ (100189630633/800000000000 : ℝ)^791 := by
    have hnat : (1040673393 : ℕ)^1047*800000000000^791 ≤ 100189630633^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040673393 5000000000 100189630633 800000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313741781/625000000 : ℝ)^1047 ≤ (1004070321459/2500000000000 : ℝ)^791 := by
    have hnat : (313741781 : ℕ)^1047*2500000000000^791 ≤ 1004070321459^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313741781 625000000 1004070321459 2500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5681378817/10000000000 : ℝ)^1047 ≤ (9462696658149/20000000000000 : ℝ)^791 := by
    have hnat : (5681378817 : ℕ)^1047*20000000000000^791 ≤ 9462696658149^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681378817 10000000000 9462696658149 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1040673393/5000000000 : ℝ), (313741781/625000000 : ℝ), (5681378817/10000000000 : ℝ)] ![(100189630633/800000000000 : ℝ), (1004070321459/2500000000000 : ℝ), (9462696658149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1040673393/5000000000 : ℝ)|^1047 ≤ (100189630633/800000000000 : ℝ)^791
        have hw : |(-1040673393/5000000000 : ℝ)|=(1040673393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313741781/625000000 : ℝ)|^1047 ≤ (1004070321459/2500000000000 : ℝ)^791
        have hw : |(313741781/625000000 : ℝ)|=(313741781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5681378817/10000000000 : ℝ)|^1047 ≤ (9462696658149/20000000000000 : ℝ)^791
        have hw : |(5681378817/10000000000 : ℝ)|=(5681378817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2621095493/5000000000 : ℝ)*x 0 + (-888066693/5000000000 : ℝ)*x 1 + (5681380439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621095493/5000000000 : ℝ)^1047 ≤ (85067897833/200000000000 : ℝ)^791 := by
    have hnat : (2621095493 : ℕ)^1047*200000000000^791 ≤ 85067897833^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621095493 5000000000 85067897833 200000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888066693/5000000000 : ℝ)^1047 ≤ (10152549898549/100000000000000 : ℝ)^791 := by
    have hnat : (888066693 : ℕ)^1047*100000000000000^791 ≤ 10152549898549^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888066693 5000000000 10152549898549 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5681380439/10000000000 : ℝ)^1047 ≤ (11828375292529/25000000000000 : ℝ)^791 := by
    have hnat : (5681380439 : ℕ)^1047*25000000000000^791 ≤ 11828375292529^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681380439 10000000000 11828375292529 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621095493/5000000000 : ℝ), (-888066693/5000000000 : ℝ), (5681380439/10000000000 : ℝ)] ![(85067897833/200000000000 : ℝ), (10152549898549/100000000000000 : ℝ), (11828375292529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621095493/5000000000 : ℝ)|^1047 ≤ (85067897833/200000000000 : ℝ)^791
        have hw : |(2621095493/5000000000 : ℝ)|=(2621095493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888066693/5000000000 : ℝ)|^1047 ≤ (10152549898549/100000000000000 : ℝ)^791
        have hw : |(-888066693/5000000000 : ℝ)|=(888066693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5681380439/10000000000 : ℝ)|^1047 ≤ (11828375292529/25000000000000 : ℝ)^791
        have hw : |(5681380439/10000000000 : ℝ)|=(5681380439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2621095331/5000000000 : ℝ)*x 0 + (5681381339/10000000000 : ℝ)*x 1 + (-355226507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621095331/5000000000 : ℝ)^1047 ≤ (4253394543683/10000000000000 : ℝ)^791 := by
    have hnat : (2621095331 : ℕ)^1047*10000000000000^791 ≤ 4253394543683^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621095331 5000000000 4253394543683 10000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5681381339/10000000000 : ℝ)^1047 ≤ (47313511090853/100000000000000 : ℝ)^791 := by
    have hnat : (5681381339 : ℕ)^1047*100000000000000^791 ≤ 47313511090853^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681381339 10000000000 47313511090853 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355226507/2000000000 : ℝ)^1047 ≤ (10152543459833/100000000000000 : ℝ)^791 := by
    have hnat : (355226507 : ℕ)^1047*100000000000000^791 ≤ 10152543459833^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355226507 2000000000 10152543459833 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621095331/5000000000 : ℝ), (5681381339/10000000000 : ℝ), (-355226507/2000000000 : ℝ)] ![(4253394543683/10000000000000 : ℝ), (47313511090853/100000000000000 : ℝ), (10152543459833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621095331/5000000000 : ℝ)|^1047 ≤ (4253394543683/10000000000000 : ℝ)^791
        have hw : |(2621095331/5000000000 : ℝ)|=(2621095331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5681381339/10000000000 : ℝ)|^1047 ≤ (47313511090853/100000000000000 : ℝ)^791
        have hw : |(5681381339/10000000000 : ℝ)|=(5681381339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355226507/2000000000 : ℝ)|^1047 ≤ (10152543459833/100000000000000 : ℝ)^791
        have hw : |(-355226507/2000000000 : ℝ)|=(355226507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s1_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2157723421/5000000000 : ℝ)*x 0 + (5030002559/10000000000 : ℝ)*x 1 + (3703348921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157723421/5000000000 : ℝ)^1047 ≤ (32877982598339/100000000000000 : ℝ)^791 := by
    have hnat : (2157723421 : ℕ)^1047*100000000000000^791 ≤ 32877982598339^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157723421 5000000000 32877982598339 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030002559/10000000000 : ℝ)^1047 ≤ (251688556981/625000000000 : ℝ)^791 := by
    have hnat : (5030002559 : ℕ)^1047*625000000000^791 ≤ 251688556981^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030002559 10000000000 251688556981 625000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3703348921/10000000000 : ℝ)^1047 ≤ (26851848269379/100000000000000 : ℝ)^791 := by
    have hnat : (3703348921 : ℕ)^1047*100000000000000^791 ≤ 26851848269379^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703348921 10000000000 26851848269379 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157723421/5000000000 : ℝ), (5030002559/10000000000 : ℝ), (3703348921/10000000000 : ℝ)] ![(32877982598339/100000000000000 : ℝ), (251688556981/625000000000 : ℝ), (26851848269379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157723421/5000000000 : ℝ)|^1047 ≤ (32877982598339/100000000000000 : ℝ)^791
        have hw : |(2157723421/5000000000 : ℝ)|=(2157723421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030002559/10000000000 : ℝ)|^1047 ≤ (251688556981/625000000000 : ℝ)^791
        have hw : |(5030002559/10000000000 : ℝ)|=(5030002559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3703348921/10000000000 : ℝ)|^1047 ≤ (26851848269379/100000000000000 : ℝ)^791
        have hw : |(3703348921/10000000000 : ℝ)|=(3703348921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27659/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1469/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10127/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27659/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (581/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27659/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (581/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27659/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (581/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27659/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (581/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27659/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (581/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27659/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (581/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (581/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (71931884759/100000000000000000000 : ℝ) := by
    have hpowers : (581/100000 : ℝ)^8375 ≤ (71931884759/100000000000000000000 : ℝ)^2048 := by
      have hnat : (581 : ℕ)^8375*100000000000000000000^2048 ≤ 71931884759^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        581 100000 71931884759 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (581/100000 : ℝ)) (X := (71931884759/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27659/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (260880091499552611/50000000000000000000 : ℝ) := by
    have hpowers : (27659/100000 : ℝ)^8375 ≤ (260880091499552611/50000000000000000000 : ℝ)^2048 := by
      have hnat : (27659 : ℕ)^8375*50000000000000000000^2048 ≤ 260880091499552611^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27659 100000 260880091499552611 50000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27659/100000 : ℝ)) (X := (260880091499552611/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000071931884759/50000000000000000000 : ℝ) ≤ (5000000001759003/5000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50000000071931884759/50000000000000000000 : ℝ)^2048 ≤ (5000000001759003/5000000000000000 : ℝ)^8375 := by
      have hnat : (50000000071931884759 : ℕ)^2048*5000000000000000^8375 ≤ 5000000001759003^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000071931884759 50000000000000000000 5000000001759003 5000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000001759003/5000000000000000 : ℝ)) (X := (50000000071931884759/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100521760254930989981/100000000000000000000 : ℝ) ≤ (2002546783105359/2000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (100521760254930989981/100000000000000000000 : ℝ)^2048 ≤ (2002546783105359/2000000000000000 : ℝ)^8375 := by
      have hnat : (100521760254930989981 : ℕ)^2048*2000000000000000^8375 ≤ 2002546783105359^8375*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100521760254930989981 100000000000000000000 2002546783105359 2000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002546783105359/2000000000000000 : ℝ)) (X := (100521760254930989981/100000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25260880091499552611/25000000000000000000 : ℝ) ≤ (313295869610487/312500000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (25260880091499552611/25000000000000000000 : ℝ)^2048 ≤ (313295869610487/312500000000000 : ℝ)^8375 := by
      have hnat : (25260880091499552611 : ℕ)^2048*312500000000000^8375 ≤ 313295869610487^8375*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25260880091499552611 25000000000000000000 313295869610487 312500000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313295869610487/312500000000000 : ℝ)) (X := (25260880091499552611/25000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(71931884759/100000000000000000000 : ℝ) ≤ ((1805101355263375691/1805200000000000000 : ℝ)+2*(4244637336263/902600000000000 : ℝ)*(581/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (1805101355263375691/1805200000000000000 : ℝ)+2*(4244637336263/902600000000000 : ℝ)*(581/100000 : ℝ)=(5000000001759003/5000000000000000 : ℝ) by norm_num, show 1+2*(71931884759/100000000000000000000 : ℝ)=(50000000071931884759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(260880091499552611/50000000000000000000 : ℝ)+(71931884759/100000000000000000000 : ℝ) ≤ ((1805101355263375691/1805200000000000000 : ℝ)+(4244637336263/902600000000000 : ℝ)*((27659/100000 : ℝ)+(581/100000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (1805101355263375691/1805200000000000000 : ℝ)+(4244637336263/902600000000000 : ℝ)*((27659/100000 : ℝ)+(581/100000 : ℝ))=(2002546783105359/2000000000000000 : ℝ) by norm_num, show 1+(260880091499552611/50000000000000000000 : ℝ)+(71931884759/100000000000000000000 : ℝ)=(100521760254930989981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(260880091499552611/50000000000000000000 : ℝ) ≤ ((1805101355263375691/1805200000000000000 : ℝ)+2*(4244637336263/902600000000000 : ℝ)*(27659/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (1805101355263375691/1805200000000000000 : ℝ)+2*(4244637336263/902600000000000 : ℝ)*(27659/100000 : ℝ)=(313295869610487/312500000000000 : ℝ) by norm_num, show 1+2*(260880091499552611/50000000000000000000 : ℝ)=(25260880091499552611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1805101355263375691/1805200000000000000 : ℝ)*(X 1 0+X 2 0)+(4244637336263/902600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (581/100000 : ℝ)) (hi := (27659/100000 : ℝ)) (c := (1805101355263375691/1805200000000000000 : ℝ)) (alpha := (4244637336263/902600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1805101355263375691/1805200000000000000 : ℝ)*(X 0 1+X 2 1)+(4244637336263/902600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (581/100000 : ℝ)) (hi := (27659/100000 : ℝ)) (c := (1805101355263375691/1805200000000000000 : ℝ)) (alpha := (4244637336263/902600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1805101355263375691/1805200000000000000 : ℝ)*(X 0 2+X 1 2)+(4244637336263/902600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (581/100000 : ℝ)) (hi := (27659/100000 : ℝ)) (c := (1805101355263375691/1805200000000000000 : ℝ)) (alpha := (4244637336263/902600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2080595373/10000000000 : ℝ)*X 0 0+(2845348943/5000000000 : ℝ)*X 0 1+(1002145661/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416877371/10000000000 : ℝ)*X 1 0+(-1223392531/5000000000 : ℝ)*X 1 1+(1252682131/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2708438277/5000000000 : ℝ)*X 2 0+(2505364537/5000000000 : ℝ)*X 2 1+(-2446785423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156971309/5000000000 : ℝ)*X 0 0+(28786429/78125000 : ℝ)*X 0 1+(5048332433/10000000000 : ℝ)*X 0 2+(2156971309/5000000000 : ℝ)*X 1 0+(28786429/78125000 : ℝ)*X 1 1+(5048332433/10000000000 : ℝ)*X 1 2+(2156971309/5000000000 : ℝ)*X 2 0+(28786429/78125000 : ℝ)*X 2 1+(5048332433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1040673393/5000000000 : ℝ)*X 0 0+(313741781/625000000 : ℝ)*X 0 1+(5681378817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621095493/5000000000 : ℝ)*X 1 0+(-888066693/5000000000 : ℝ)*X 1 1+(5681380439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621095331/5000000000 : ℝ)*X 2 0+(5681381339/10000000000 : ℝ)*X 2 1+(-355226507/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157723421/5000000000 : ℝ)*X 0 0+(5030002559/10000000000 : ℝ)*X 0 1+(3703348921/10000000000 : ℝ)*X 0 2+(2157723421/5000000000 : ℝ)*X 1 0+(5030002559/10000000000 : ℝ)*X 1 1+(3703348921/10000000000 : ℝ)*X 1 2+(2157723421/5000000000 : ℝ)*X 2 0+(5030002559/10000000000 : ℝ)*X 2 1+(3703348921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62382176256847624191247083/18052000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187911609/20000000000000 : ℝ)*(base19) + (708633873/100000000000000 : ℝ)*(base23) + (200272767/100000000000000 : ℝ)*(upper3) + (2467749/50000000000000 : ℝ)*(upper4) + (3211833/100000000000000 : ℝ)*(upper5) + (220398660289543/20000000000000 : ℝ)*(major0) + (220398660289543/20000000000000 : ℝ)*(major1) + (220398660289543/20000000000000 : ℝ)*(major2) + (735330389292011/50000000000000 : ℝ)*(sp0) + (294132864563827/20000000000000 : ℝ)*(sp1) + (735332276871653/50000000000000 : ℝ)*(sp2) + (91664749926377/12500000000000 : ℝ)*(sp3) + (4483793157/100000000000000 : ℝ)*(sp4) + (64518349/2000000000000 : ℝ)*(sp7) + (733321225328467/100000000000000 : ℝ)*(f.failure) + (1470665262377179/100000000000000 : ℝ)*(f.sum) + (16495025399129/9026000000000000000000000000 : ℝ)*base65 + (235942537966693213/36104000000000000000000000000000 : ℝ)*base67 + (223483089050189213/36104000000000000000000000000000 : ℝ)*base69 + (93937766460525213/36104000000000000000000000000000 : ℝ)*base71 + (25739160423737/9026000000000000000000000000 : ℝ)*base73 + (43251604743045213/36104000000000000000000000000000 : ℝ)*base75 + (242016393098869213/36104000000000000000000000000000 : ℝ)*base77 + (256391147481573213/36104000000000000000000000000000 : ℝ)*base79 + (11461895289369/9026000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4371153/2000000000000000000000 : ℝ)*base89 + (4371153/2000000000000000000000 : ℝ)*base91 + (4371153/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6477264044887016535621747/2256500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3923851/250000000000 : ℝ)*(base19) + (40897189/2000000000000 : ℝ)*(base23) + (21528769/10000000000000 : ℝ)*(upper2) + (90325017/25000000000000 : ℝ)*(upper3) + (33165257/20000000000000 : ℝ)*(upper5) + (28318324121161/2500000000000 : ℝ)*(major0) + (28318324121161/2500000000000 : ℝ)*(major1) + (28318324121161/2500000000000 : ℝ)*(major2) + (8375740777/100000000000000 : ℝ)*(sp1) + (13119266479/100000000000000 : ℝ)*(sp2) + (11810069576009/781250000000 : ℝ)*(sp4) + (60467158417919/4000000000000 : ℝ)*(sp5) + (755836870801611/50000000000000 : ℝ)*(sp6) + (30151077131227/4000000000000 : ℝ)*(sp7) + (30151077131227/4000000000000 : ℝ)*(f.failure) + (11810069576009/781250000000 : ℝ)*(f.sum) + (7954950426521/2256500000000000000000000000 : ℝ)*base66 + (9141563913037749/4513000000000000000000000000000 : ℝ)*base68 + (10375210830116251/4513000000000000000000000000000 : ℝ)*base69 + (9465777660712251/4513000000000000000000000000000 : ℝ)*base71 + (8721566090459/4513000000000000000000000000 : ℝ)*base73 + (19743698163240749/4513000000000000000000000000000 : ℝ)*base76 + (1836389987943251/4513000000000000000000000000000 : ℝ)*base77 + (12257325121906251/4513000000000000000000000000000 : ℝ)*base79 + (3576197562907/1128250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (18007/80000000000000000000 : ℝ)*base90 + (18007/80000000000000000000 : ℝ)*base92 + (18007/80000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1183_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27659/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1469/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10127/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1183_s2_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-532914379/2500000000 : ℝ)*x 0 + (5503181567/10000000000 : ℝ)*x 1 + (1291434011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532914379/2500000000 : ℝ)^1047 ≤ (201968165059/1562500000000 : ℝ)^791 := by
    have hnat : (532914379 : ℕ)^1047*1562500000000^791 ≤ 201968165059^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532914379 2500000000 201968165059 1562500000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503181567/10000000000 : ℝ)^1047 ≤ (45359249087763/100000000000000 : ℝ)^791 := by
    have hnat : (5503181567 : ℕ)^1047*100000000000000^791 ≤ 45359249087763^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503181567 10000000000 45359249087763 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291434011/2500000000 : ℝ)^1047 ≤ (10428697082513/25000000000000 : ℝ)^791 := by
    have hnat : (1291434011 : ℕ)^1047*25000000000000^791 ≤ 10428697082513^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291434011 2500000000 10428697082513 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532914379/2500000000 : ℝ), (5503181567/10000000000 : ℝ), (1291434011/2500000000 : ℝ)] ![(201968165059/1562500000000 : ℝ), (45359249087763/100000000000000 : ℝ), (10428697082513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532914379/2500000000 : ℝ)|^1047 ≤ (201968165059/1562500000000 : ℝ)^791
        have hw : |(-532914379/2500000000 : ℝ)|=(532914379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503181567/10000000000 : ℝ)|^1047 ≤ (45359249087763/100000000000000 : ℝ)^791
        have hw : |(5503181567/10000000000 : ℝ)|=(5503181567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291434011/2500000000 : ℝ)|^1047 ≤ (10428697082513/25000000000000 : ℝ)^791
        have hw : |(1291434011/2500000000 : ℝ)|=(1291434011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5372122129/10000000000 : ℝ)*x 0 + (-2306820521/10000000000 : ℝ)*x 1 + (1291434911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372122129/10000000000 : ℝ)^1047 ≤ (10983734800223/25000000000000 : ℝ)^791 := by
    have hnat : (5372122129 : ℕ)^1047*25000000000000^791 ≤ 10983734800223^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372122129 10000000000 10983734800223 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306820521/10000000000 : ℝ)^1047 ≤ (7175116991131/50000000000000 : ℝ)^791 := by
    have hnat : (2306820521 : ℕ)^1047*50000000000000^791 ≤ 7175116991131^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306820521 10000000000 7175116991131 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291434911/2500000000 : ℝ)^1047 ≤ (8342965361931/20000000000000 : ℝ)^791 := by
    have hnat : (1291434911 : ℕ)^1047*20000000000000^791 ≤ 8342965361931^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291434911 2500000000 8342965361931 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372122129/10000000000 : ℝ), (-2306820521/10000000000 : ℝ), (1291434911/2500000000 : ℝ)] ![(10983734800223/25000000000000 : ℝ), (7175116991131/50000000000000 : ℝ), (8342965361931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372122129/10000000000 : ℝ)|^1047 ≤ (10983734800223/25000000000000 : ℝ)^791
        have hw : |(5372122129/10000000000 : ℝ)|=(5372122129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2306820521/10000000000 : ℝ)|^1047 ≤ (7175116991131/50000000000000 : ℝ)^791
        have hw : |(-2306820521/10000000000 : ℝ)|=(2306820521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291434911/2500000000 : ℝ)|^1047 ≤ (8342965361931/20000000000000 : ℝ)^791
        have hw : |(1291434911/2500000000 : ℝ)|=(1291434911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (671515423/1250000000 : ℝ)*x 0 + (5165737837/10000000000 : ℝ)*x 1 + (-72088163/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671515423/1250000000 : ℝ)^1047 ≤ (43934952786469/100000000000000 : ℝ)^791 := by
    have hnat : (671515423 : ℕ)^1047*100000000000000^791 ≤ 43934952786469^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671515423 1250000000 43934952786469 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5165737837/10000000000 : ℝ)^1047 ≤ (41714807495031/100000000000000 : ℝ)^791 := by
    have hnat : (5165737837 : ℕ)^1047*100000000000000^791 ≤ 41714807495031^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165737837 10000000000 41714807495031 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72088163/312500000 : ℝ)^1047 ≤ (14350239704951/100000000000000 : ℝ)^791 := by
    have hnat : (72088163 : ℕ)^1047*100000000000000^791 ≤ 14350239704951^791*312500000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72088163 312500000 14350239704951 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671515423/1250000000 : ℝ), (5165737837/10000000000 : ℝ), (-72088163/312500000 : ℝ)] ![(43934952786469/100000000000000 : ℝ), (41714807495031/100000000000000 : ℝ), (14350239704951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671515423/1250000000 : ℝ)|^1047 ≤ (43934952786469/100000000000000 : ℝ)^791
        have hw : |(671515423/1250000000 : ℝ)|=(671515423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5165737837/10000000000 : ℝ)|^1047 ≤ (41714807495031/100000000000000 : ℝ)^791
        have hw : |(5165737837/10000000000 : ℝ)|=(5165737837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72088163/312500000 : ℝ)|^1047 ≤ (14350239704951/100000000000000 : ℝ)^791
        have hw : |(-72088163/312500000 : ℝ)|=(72088163/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (869814943/2000000000 : ℝ)*x 0 + (804725633/2000000000 : ℝ)*x 1 + (4700365949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869814943/2000000000 : ℝ)^1047 ≤ (33217526018763/100000000000000 : ℝ)^791 := by
    have hnat : (869814943 : ℕ)^1047*100000000000000^791 ≤ 33217526018763^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869814943 2000000000 33217526018763 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804725633/2000000000 : ℝ)^1047 ≤ (5993575395551/20000000000000 : ℝ)^791 := by
    have hnat : (804725633 : ℕ)^1047*20000000000000^791 ≤ 5993575395551^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804725633 2000000000 5993575395551 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4700365949/10000000000 : ℝ)^1047 ≤ (575228077901/1562500000000 : ℝ)^791 := by
    have hnat : (4700365949 : ℕ)^1047*1562500000000^791 ≤ 575228077901^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4700365949 10000000000 575228077901 1562500000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869814943/2000000000 : ℝ), (804725633/2000000000 : ℝ), (4700365949/10000000000 : ℝ)] ![(33217526018763/100000000000000 : ℝ), (5993575395551/20000000000000 : ℝ), (575228077901/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869814943/2000000000 : ℝ)|^1047 ≤ (33217526018763/100000000000000 : ℝ)^791
        have hw : |(869814943/2000000000 : ℝ)|=(869814943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804725633/2000000000 : ℝ)|^1047 ≤ (5993575395551/20000000000000 : ℝ)^791
        have hw : |(804725633/2000000000 : ℝ)|=(804725633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4700365949/10000000000 : ℝ)|^1047 ≤ (575228077901/1562500000000 : ℝ)^791
        have hw : |(4700365949/10000000000 : ℝ)|=(4700365949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131748479/10000000000 : ℝ)*x 0 + (2583998981/5000000000 : ℝ)*x 1 + (550089827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131748479/10000000000 : ℝ)^1047 ≤ (2585338533121/20000000000000 : ℝ)^791 := by
    have hnat : (2131748479 : ℕ)^1047*20000000000000^791 ≤ 2585338533121^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131748479 10000000000 2585338533121 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2583998981/5000000000 : ℝ)^1047 ≤ (20869483590453/50000000000000 : ℝ)^791 := by
    have hnat : (2583998981 : ℕ)^1047*50000000000000^791 ≤ 20869483590453^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583998981 5000000000 20869483590453 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550089827/1000000000 : ℝ)^1047 ≤ (22667170067861/50000000000000 : ℝ)^791 := by
    have hnat : (550089827 : ℕ)^1047*50000000000000^791 ≤ 22667170067861^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550089827 1000000000 22667170067861 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131748479/10000000000 : ℝ), (2583998981/5000000000 : ℝ), (550089827/1000000000 : ℝ)] ![(2585338533121/20000000000000 : ℝ), (20869483590453/50000000000000 : ℝ), (22667170067861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131748479/10000000000 : ℝ)|^1047 ≤ (2585338533121/20000000000000 : ℝ)^791
        have hw : |(-2131748479/10000000000 : ℝ)|=(2131748479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2583998981/5000000000 : ℝ)|^1047 ≤ (20869483590453/50000000000000 : ℝ)^791
        have hw : |(2583998981/5000000000 : ℝ)|=(2583998981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550089827/1000000000 : ℝ)|^1047 ≤ (22667170067861/50000000000000 : ℝ)^791
        have hw : |(550089827/1000000000 : ℝ)|=(550089827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21145089/40000000 : ℝ)*x 0 + (-492915109/2500000000 : ℝ)*x 1 + (2750449139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21145089/40000000 : ℝ)^1047 ≤ (21504006224169/50000000000000 : ℝ)^791 := by
    have hnat : (21145089 : ℕ)^1047*50000000000000^791 ≤ 21504006224169^791*40000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21145089 40000000 21504006224169 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492915109/2500000000 : ℝ)^1047 ≤ (466305892561/4000000000000 : ℝ)^791 := by
    have hnat : (492915109 : ℕ)^1047*4000000000000^791 ≤ 466305892561^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492915109 2500000000 466305892561 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750449139/5000000000 : ℝ)^1047 ≤ (4533434022299/10000000000000 : ℝ)^791 := by
    have hnat : (2750449139 : ℕ)^1047*10000000000000^791 ≤ 4533434022299^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750449139 5000000000 4533434022299 10000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21145089/40000000 : ℝ), (-492915109/2500000000 : ℝ), (2750449139/5000000000 : ℝ)] ![(21504006224169/50000000000000 : ℝ), (466305892561/4000000000000 : ℝ), (4533434022299/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21145089/40000000 : ℝ)|^1047 ≤ (21504006224169/50000000000000 : ℝ)^791
        have hw : |(21145089/40000000 : ℝ)|=(21145089/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492915109/2500000000 : ℝ)|^1047 ≤ (466305892561/4000000000000 : ℝ)^791
        have hw : |(-492915109/2500000000 : ℝ)|=(492915109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750449139/5000000000 : ℝ)|^1047 ≤ (4533434022299/10000000000000 : ℝ)^791
        have hw : |(2750449139/5000000000 : ℝ)|=(2750449139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2643136201/5000000000 : ℝ)*x 0 + (2750449141/5000000000 : ℝ)*x 1 + (-985830111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643136201/5000000000 : ℝ)^1047 ≤ (21504007042603/50000000000000 : ℝ)^791 := by
    have hnat : (2643136201 : ℕ)^1047*50000000000000^791 ≤ 21504007042603^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643136201 5000000000 21504007042603 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750449141/5000000000 : ℝ)^1047 ≤ (354174533333/781250000000 : ℝ)^791 := by
    have hnat : (2750449141 : ℕ)^1047*781250000000^791 ≤ 354174533333^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750449141 5000000000 354174533333 781250000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985830111/5000000000 : ℝ)^1047 ≤ (466305825569/4000000000000 : ℝ)^791 := by
    have hnat : (985830111 : ℕ)^1047*4000000000000^791 ≤ 466305825569^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985830111 5000000000 466305825569 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643136201/5000000000 : ℝ), (2750449141/5000000000 : ℝ), (-985830111/5000000000 : ℝ)] ![(21504007042603/50000000000000 : ℝ), (354174533333/781250000000 : ℝ), (466305825569/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643136201/5000000000 : ℝ)|^1047 ≤ (21504007042603/50000000000000 : ℝ)^791
        have hw : |(2643136201/5000000000 : ℝ)|=(2643136201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750449141/5000000000 : ℝ)|^1047 ≤ (354174533333/781250000000 : ℝ)^791
        have hw : |(2750449141/5000000000 : ℝ)|=(2750449141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985830111/5000000000 : ℝ)|^1047 ≤ (466305825569/4000000000000 : ℝ)^791
        have hw : |(-985830111/5000000000 : ℝ)|=(985830111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s2_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4349259123/10000000000 : ℝ)*x 0 + (469583233/1000000000 : ℝ)*x 1 + (4028205019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349259123/10000000000 : ℝ)^1047 ≤ (33219390351179/100000000000000 : ℝ)^791 := by
    have hnat : (4349259123 : ℕ)^1047*100000000000000^791 ≤ 33219390351179^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349259123 10000000000 33219390351179 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469583233/1000000000 : ℝ)^1047 ≤ (36767603702011/100000000000000 : ℝ)^791 := by
    have hnat : (469583233 : ℕ)^1047*100000000000000^791 ≤ 36767603702011^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469583233 1000000000 36767603702011 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028205019/10000000000 : ℝ)^1047 ≤ (30013005935893/100000000000000 : ℝ)^791 := by
    have hnat : (4028205019 : ℕ)^1047*100000000000000^791 ≤ 30013005935893^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028205019 10000000000 30013005935893 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349259123/10000000000 : ℝ), (469583233/1000000000 : ℝ), (4028205019/10000000000 : ℝ)] ![(33219390351179/100000000000000 : ℝ), (36767603702011/100000000000000 : ℝ), (30013005935893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349259123/10000000000 : ℝ)|^1047 ≤ (33219390351179/100000000000000 : ℝ)^791
        have hw : |(4349259123/10000000000 : ℝ)|=(4349259123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469583233/1000000000 : ℝ)|^1047 ≤ (36767603702011/100000000000000 : ℝ)^791
        have hw : |(469583233/1000000000 : ℝ)|=(469583233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028205019/10000000000 : ℝ)|^1047 ≤ (30013005935893/100000000000000 : ℝ)^791
        have hw : |(4028205019/10000000000 : ℝ)|=(4028205019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1469/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2313/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16383/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1469/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1469/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1469/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1469/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1469/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1469/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1469/25000 : ℝ) ^ (8375/2048 : ℝ) ≤ (925417855108971/100000000000000000000 : ℝ) := by
    have hpowers : (1469/25000 : ℝ)^8375 ≤ (925417855108971/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1469 : ℕ)^8375*100000000000000000000^2048 ≤ 925417855108971^2048*25000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1469 25000 925417855108971 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1469/25000 : ℝ)) (X := (925417855108971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10127/50000 : ℝ) ^ (8375/2048 : ℝ) ≤ (29181402858059463/20000000000000000000 : ℝ) := by
    have hpowers : (10127/50000 : ℝ)^8375 ≤ (29181402858059463/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10127 : ℕ)^8375*20000000000000000000^2048 ≤ 29181402858059463^2048*50000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10127 50000 29181402858059463 20000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10127/50000 : ℝ)) (X := (29181402858059463/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000925417855108971/50000000000000000000 : ℝ) ≤ (5000022629761401/5000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50000925417855108971/50000000000000000000 : ℝ)^2048 ≤ (5000022629761401/5000000000000000 : ℝ)^8375 := by
      have hnat : (50000925417855108971 : ℕ)^2048*5000000000000000^8375 ≤ 5000022629761401^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000925417855108971 50000000000000000000 5000022629761401 5000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000022629761401/5000000000000000 : ℝ)) (X := (50000925417855108971/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50073416216072703143/50000000000000000000 : ℝ) ≤ (10003588611094939/10000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50073416216072703143/50000000000000000000 : ℝ)^2048 ≤ (10003588611094939/10000000000000000 : ℝ)^8375 := by
      have hnat : (50073416216072703143 : ℕ)^2048*10000000000000000^8375 ≤ 10003588611094939^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073416216072703143 50000000000000000000 10003588611094939 10000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003588611094939/10000000000000000 : ℝ)) (X := (50073416216072703143/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10029181402858059463/10000000000000000000 : ℝ) ≤ (2501782990666769/2500000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (10029181402858059463/10000000000000000000 : ℝ)^2048 ≤ (2501782990666769/2500000000000000 : ℝ)^8375 := by
      have hnat : (10029181402858059463 : ℕ)^2048*2500000000000000^8375 ≤ 2501782990666769^8375*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10029181402858059463 10000000000000000000 2501782990666769 2500000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501782990666769/2500000000000000 : ℝ)) (X := (10029181402858059463/10000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(925417855108971/100000000000000000000 : ℝ) ≤ ((2764211716802751791/2765000000000000000 : ℝ)+2*(272565505549/110600000000000 : ℝ)*(1469/25000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (2764211716802751791/2765000000000000000 : ℝ)+2*(272565505549/110600000000000 : ℝ)*(1469/25000 : ℝ)=(5000022629761401/5000000000000000 : ℝ) by norm_num, show 1+2*(925417855108971/100000000000000000000 : ℝ)=(50000925417855108971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29181402858059463/20000000000000000000 : ℝ)+(925417855108971/100000000000000000000 : ℝ) ≤ ((2764211716802751791/2765000000000000000 : ℝ)+(272565505549/110600000000000 : ℝ)*((10127/50000 : ℝ)+(1469/25000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (2764211716802751791/2765000000000000000 : ℝ)+(272565505549/110600000000000 : ℝ)*((10127/50000 : ℝ)+(1469/25000 : ℝ))=(10003588611094939/10000000000000000 : ℝ) by norm_num, show 1+(29181402858059463/20000000000000000000 : ℝ)+(925417855108971/100000000000000000000 : ℝ)=(50073416216072703143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29181402858059463/20000000000000000000 : ℝ) ≤ ((2764211716802751791/2765000000000000000 : ℝ)+2*(272565505549/110600000000000 : ℝ)*(10127/50000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (2764211716802751791/2765000000000000000 : ℝ)+2*(272565505549/110600000000000 : ℝ)*(10127/50000 : ℝ)=(2501782990666769/2500000000000000 : ℝ) by norm_num, show 1+2*(29181402858059463/20000000000000000000 : ℝ)=(10029181402858059463/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2764211716802751791/2765000000000000000 : ℝ)*(X 1 0+X 2 0)+(272565505549/110600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (1469/25000 : ℝ)) (hi := (10127/50000 : ℝ)) (c := (2764211716802751791/2765000000000000000 : ℝ)) (alpha := (272565505549/110600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2764211716802751791/2765000000000000000 : ℝ)*(X 0 1+X 2 1)+(272565505549/110600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (1469/25000 : ℝ)) (hi := (10127/50000 : ℝ)) (c := (2764211716802751791/2765000000000000000 : ℝ)) (alpha := (272565505549/110600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2764211716802751791/2765000000000000000 : ℝ)*(X 0 2+X 1 2)+(272565505549/110600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (1469/25000 : ℝ)) (hi := (10127/50000 : ℝ)) (c := (2764211716802751791/2765000000000000000 : ℝ)) (alpha := (272565505549/110600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-532914379/2500000000 : ℝ)*X 0 0+(5503181567/10000000000 : ℝ)*X 0 1+(1291434011/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372122129/10000000000 : ℝ)*X 1 0+(-2306820521/10000000000 : ℝ)*X 1 1+(1291434911/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671515423/1250000000 : ℝ)*X 2 0+(5165737837/10000000000 : ℝ)*X 2 1+(-72088163/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869814943/2000000000 : ℝ)*X 0 0+(804725633/2000000000 : ℝ)*X 0 1+(4700365949/10000000000 : ℝ)*X 0 2+(869814943/2000000000 : ℝ)*X 1 0+(804725633/2000000000 : ℝ)*X 1 1+(4700365949/10000000000 : ℝ)*X 1 2+(869814943/2000000000 : ℝ)*X 2 0+(804725633/2000000000 : ℝ)*X 2 1+(4700365949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2131748479/10000000000 : ℝ)*X 0 0+(2583998981/5000000000 : ℝ)*X 0 1+(550089827/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21145089/40000000 : ℝ)*X 1 0+(-492915109/2500000000 : ℝ)*X 1 1+(2750449139/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643136201/5000000000 : ℝ)*X 2 0+(2750449141/5000000000 : ℝ)*X 2 1+(-985830111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349259123/10000000000 : ℝ)*X 0 0+(469583233/1000000000 : ℝ)*X 0 1+(4028205019/10000000000 : ℝ)*X 0 2+(4349259123/10000000000 : ℝ)*X 1 0+(469583233/1000000000 : ℝ)*X 1 1+(4028205019/10000000000 : ℝ)*X 1 2+(4349259123/10000000000 : ℝ)*X 2 0+(469583233/1000000000 : ℝ)*X 2 1+(4028205019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5073604820647886410887/1382500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3323529/6250000000000 : ℝ)*(base19) + (137758327/20000000000000 : ℝ)*(base23) + (72695133/50000000000000 : ℝ)*(upper2) + (352867771/100000000000000 : ℝ)*(upper3) + (175847797/100000000000000 : ℝ)*(upper4) + (4337090045807/195312500000 : ℝ)*(major0) + (4337090045807/195312500000 : ℝ)*(major1) + (4337090045807/195312500000 : ℝ)*(major2) + (740866691995521/25000000000000 : ℝ)*(sp0) + (740872196142219/25000000000000 : ℝ)*(sp1) + (1481744074476853/50000000000000 : ℝ)*(sp2) + (1477681997022529/100000000000000 : ℝ)*(sp3) + (22069763257/100000000000000 : ℝ)*(sp4) + (4624904631/50000000000000 : ℝ)*(sp7) + (92355702926987/6250000000000 : ℝ)*(f.failure) + (2963488837745341/100000000000000 : ℝ)*(f.sum) + (1306127129851/1382500000000000000000000000 : ℝ)*base66 + (18899371332638983/8640625000000000000000000000000 : ℝ)*base68 + (494446744107733/8640625000000000000000000000000 : ℝ)*base70 + (5387255777545233/8640625000000000000000000000000 : ℝ)*base72 + (287143169023/2765000000000000000000000000 : ℝ)*base73 + (68666679207861017/8640625000000000000000000000000 : ℝ)*base75 + (23543249420892267/8640625000000000000000000000000 : ℝ)*base77 + (10547480680173517/8640625000000000000000000000000 : ℝ)*base79 + (27124391787/2765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1579833/125000000000000000000 : ℝ)*base89 + (1579833/125000000000000000000 : ℝ)*base91 + (1579833/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24737250537202668421346067/19750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50150097/10000000000000 : ℝ)*(base19) + (734449343/100000000000000 : ℝ)*(base23) + (23049959/50000000000000 : ℝ)*(upper2) + (78463061/100000000000000 : ℝ)*(upper3) + (3826947/12500000000000 : ℝ)*(upper5) + (2250871795274953/100000000000000 : ℝ)*(major0) + (2250871795274953/100000000000000 : ℝ)*(major1) + (2250871795274953/100000000000000 : ℝ)*(major2) + (892535251/20000000000000 : ℝ)*(sp1) + (8118214267/100000000000000 : ℝ)*(sp2) + (1501950678055461/50000000000000 : ℝ)*(sp4) + (1501948195966849/50000000000000 : ℝ)*(sp5) + (187743281465457/6250000000000 : ℝ)*(sp6) + (748921096344173/50000000000000 : ℝ)*(sp7) + (748921096344173/50000000000000 : ℝ)*(f.failure) + (1501950678055461/50000000000000 : ℝ)*(f.sum) + (16869533633403/5530000000000000000000000000 : ℝ)*base66 + (118590258102884177/276500000000000000000000000000000 : ℝ)*base68 + (60817770592115823/276500000000000000000000000000000 : ℝ)*base69 + (153302291791384177/276500000000000000000000000000000 : ℝ)*base72 + (27146110019213/5530000000000000000000000000 : ℝ)*base74 + (1722999948993884177/276500000000000000000000000000000 : ℝ)*base76 + (79801833301884177/276500000000000000000000000000000 : ℝ)*base78 + (1421100683423615823/276500000000000000000000000000000 : ℝ)*base79 + (33237248193943/5530000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4986607/1000000000000000000000 : ℝ)*base89 + (4986607/1000000000000000000000 : ℝ)*base91 + (4986607/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1183_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1469/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1183_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1183_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1183_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1183_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1183_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
