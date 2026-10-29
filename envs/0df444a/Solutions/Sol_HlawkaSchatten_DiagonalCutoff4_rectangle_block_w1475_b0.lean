-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1475_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:42.872282+00:00
-- url     : https://prove2.me/submissions/4e790307-22ab-448a-a36b-ee06d5b7c0ec

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
theorem support_rectangle_w1475_s0_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69031613/400000000 : ℝ)*x 0 + (5941891039/10000000000 : ℝ)*x 1 + (967834929/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69031613/400000000 : ℝ)^4447 ≤ (318845940529/3125000000000 : ℝ)^3423 := by
    have hnat : (69031613 : ℕ)^4447*3125000000000^3423 ≤ 318845940529^3423*400000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69031613 400000000 318845940529 3125000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5941891039/10000000000 : ℝ)^4447 ≤ (10170062398773/20000000000000 : ℝ)^3423 := by
    have hnat : (5941891039 : ℕ)^4447*20000000000000^3423 ≤ 10170062398773^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5941891039 10000000000 10170062398773 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967834929/2000000000 : ℝ)^4447 ≤ (38946617895523/100000000000000 : ℝ)^3423 := by
    have hnat : (967834929 : ℕ)^4447*100000000000000^3423 ≤ 38946617895523^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967834929 2000000000 38946617895523 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69031613/400000000 : ℝ), (5941891039/10000000000 : ℝ), (967834929/2000000000 : ℝ)] ![(318845940529/3125000000000 : ℝ), (10170062398773/20000000000000 : ℝ), (38946617895523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69031613/400000000 : ℝ)|^4447 ≤ (318845940529/3125000000000 : ℝ)^3423
        have hw : |(-69031613/400000000 : ℝ)|=(69031613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5941891039/10000000000 : ℝ)|^4447 ≤ (10170062398773/20000000000000 : ℝ)^3423
        have hw : |(5941891039/10000000000 : ℝ)|=(5941891039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967834929/2000000000 : ℝ)|^4447 ≤ (38946617895523/100000000000000 : ℝ)^3423
        have hw : |(967834929/2000000000 : ℝ)|=(967834929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171439821/312500000 : ℝ)*x 0 + (-234689941/1000000000 : ℝ)*x 1 + (4839174557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171439821/312500000 : ℝ)^4447 ≤ (45841739393731/100000000000000 : ℝ)^3423 := by
    have hnat : (171439821 : ℕ)^4447*100000000000000^3423 ≤ 45841739393731^3423*312500000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171439821 312500000 45841739393731 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234689941/1000000000 : ℝ)^4447 ≤ (15211643611829/100000000000000 : ℝ)^3423 := by
    have hnat : (234689941 : ℕ)^4447*100000000000000^3423 ≤ 15211643611829^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234689941 1000000000 15211643611829 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4839174557/10000000000 : ℝ)^4447 ≤ (38946616975409/100000000000000 : ℝ)^3423 := by
    have hnat : (4839174557 : ℕ)^4447*100000000000000^3423 ≤ 38946616975409^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839174557 10000000000 38946616975409 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171439821/312500000 : ℝ), (-234689941/1000000000 : ℝ), (4839174557/10000000000 : ℝ)] ![(45841739393731/100000000000000 : ℝ), (15211643611829/100000000000000 : ℝ), (38946616975409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171439821/312500000 : ℝ)|^4447 ≤ (45841739393731/100000000000000 : ℝ)^3423
        have hw : |(171439821/312500000 : ℝ)|=(171439821/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234689941/1000000000 : ℝ)|^4447 ≤ (15211643611829/100000000000000 : ℝ)^3423
        have hw : |(-234689941/1000000000 : ℝ)|=(234689941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4839174557/10000000000 : ℝ)|^4447 ≤ (38946616975409/100000000000000 : ℝ)^3423
        have hw : |(4839174557/10000000000 : ℝ)|=(4839174557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171439827/312500000 : ℝ)*x 0 + (1209793597/2500000000 : ℝ)*x 1 + (-2346899373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171439827/312500000 : ℝ)^4447 ≤ (22920870739017/50000000000000 : ℝ)^3423 := by
    have hnat : (171439827 : ℕ)^4447*50000000000000^3423 ≤ 22920870739017^3423*312500000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171439827 312500000 22920870739017 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209793597/2500000000 : ℝ)^4447 ≤ (19473307604187/50000000000000 : ℝ)^3423 := by
    have hnat : (1209793597 : ℕ)^4447*50000000000000^3423 ≤ 19473307604187^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209793597 2500000000 19473307604187 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2346899373/10000000000 : ℝ)^4447 ≤ (3802910825067/25000000000000 : ℝ)^3423 := by
    have hnat : (2346899373 : ℕ)^4447*25000000000000^3423 ≤ 3802910825067^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2346899373 10000000000 3802910825067 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171439827/312500000 : ℝ), (1209793597/2500000000 : ℝ), (-2346899373/10000000000 : ℝ)] ![(22920870739017/50000000000000 : ℝ), (19473307604187/50000000000000 : ℝ), (3802910825067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171439827/312500000 : ℝ)|^4447 ≤ (22920870739017/50000000000000 : ℝ)^3423
        have hw : |(171439827/312500000 : ℝ)|=(171439827/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209793597/2500000000 : ℝ)|^4447 ≤ (19473307604187/50000000000000 : ℝ)^3423
        have hw : |(1209793597/2500000000 : ℝ)|=(1209793597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2346899373/10000000000 : ℝ)|^4447 ≤ (3802910825067/25000000000000 : ℝ)^3423
        have hw : |(-2346899373/10000000000 : ℝ)|=(2346899373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2077637767/5000000000 : ℝ)*x 0 + (3091600503/10000000000 : ℝ)*x 1 + (1381762813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077637767/5000000000 : ℝ)^4447 ≤ (15976178542417/50000000000000 : ℝ)^3423 := by
    have hnat : (2077637767 : ℕ)^4447*50000000000000^3423 ≤ 15976178542417^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077637767 5000000000 15976178542417 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091600503/10000000000 : ℝ)^4447 ≤ (170004466703/781250000000 : ℝ)^3423 := by
    have hnat : (3091600503 : ℕ)^4447*781250000000^3423 ≤ 170004466703^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091600503 10000000000 170004466703 781250000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381762813/2500000000 : ℝ)^4447 ≤ (46287071159411/100000000000000 : ℝ)^3423 := by
    have hnat : (1381762813 : ℕ)^4447*100000000000000^3423 ≤ 46287071159411^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381762813 2500000000 46287071159411 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2077637767/5000000000 : ℝ), (3091600503/10000000000 : ℝ), (1381762813/2500000000 : ℝ)] ![(15976178542417/50000000000000 : ℝ), (170004466703/781250000000 : ℝ), (46287071159411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2077637767/5000000000 : ℝ)|^4447 ≤ (15976178542417/50000000000000 : ℝ)^3423
        have hw : |(2077637767/5000000000 : ℝ)|=(2077637767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091600503/10000000000 : ℝ)|^4447 ≤ (170004466703/781250000000 : ℝ)^3423
        have hw : |(3091600503/10000000000 : ℝ)|=(3091600503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381762813/2500000000 : ℝ)|^4447 ≤ (46287071159411/100000000000000 : ℝ)^3423
        have hw : |(1381762813/2500000000 : ℝ)|=(1381762813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1729639971/10000000000 : ℝ)*x 0 + (4867487871/10000000000 : ℝ)*x 1 + (5912558937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1729639971/10000000000 : ℝ)^4447 ≤ (5116324043887/50000000000000 : ℝ)^3423 := by
    have hnat : (1729639971 : ℕ)^4447*50000000000000^3423 ≤ 5116324043887^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729639971 10000000000 5116324043887 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4867487871/10000000000 : ℝ)^4447 ≤ (9810728753381/25000000000000 : ℝ)^3423 := by
    have hnat : (4867487871 : ℕ)^4447*25000000000000^3423 ≤ 9810728753381^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867487871 10000000000 9810728753381 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5912558937/10000000000 : ℝ)^4447 ≤ (50524436884207/100000000000000 : ℝ)^3423 := by
    have hnat : (5912558937 : ℕ)^4447*100000000000000^3423 ≤ 50524436884207^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912558937 10000000000 50524436884207 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1729639971/10000000000 : ℝ), (4867487871/10000000000 : ℝ), (5912558937/10000000000 : ℝ)] ![(5116324043887/50000000000000 : ℝ), (9810728753381/25000000000000 : ℝ), (50524436884207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1729639971/10000000000 : ℝ)|^4447 ≤ (5116324043887/50000000000000 : ℝ)^3423
        have hw : |(-1729639971/10000000000 : ℝ)|=(1729639971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4867487871/10000000000 : ℝ)|^4447 ≤ (9810728753381/25000000000000 : ℝ)^3423
        have hw : |(4867487871/10000000000 : ℝ)|=(4867487871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5912558937/10000000000 : ℝ)|^4447 ≤ (50524436884207/100000000000000 : ℝ)^3423
        have hw : |(5912558937/10000000000 : ℝ)|=(5912558937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296254041/2500000000 : ℝ)*x 0 + (-1273514853/10000000000 : ℝ)*x 1 + (739069883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296254041/2500000000 : ℝ)^4447 ≤ (10650176967527/25000000000000 : ℝ)^3423 := by
    have hnat : (1296254041 : ℕ)^4447*25000000000000^3423 ≤ 10650176967527^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296254041 2500000000 10650176967527 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273514853/10000000000 : ℝ)^4447 ≤ (859356727997/12500000000000 : ℝ)^3423 := by
    have hnat : (1273514853 : ℕ)^4447*12500000000000^3423 ≤ 859356727997^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273514853 10000000000 859356727997 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739069883/1250000000 : ℝ)^4447 ≤ (1578888696691/3125000000000 : ℝ)^3423 := by
    have hnat : (739069883 : ℕ)^4447*3125000000000^3423 ≤ 1578888696691^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739069883 1250000000 1578888696691 3125000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296254041/2500000000 : ℝ), (-1273514853/10000000000 : ℝ), (739069883/1250000000 : ℝ)] ![(10650176967527/25000000000000 : ℝ), (859356727997/12500000000000 : ℝ), (1578888696691/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296254041/2500000000 : ℝ)|^4447 ≤ (10650176967527/25000000000000 : ℝ)^3423
        have hw : |(1296254041/2500000000 : ℝ)|=(1296254041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1273514853/10000000000 : ℝ)|^4447 ≤ (859356727997/12500000000000 : ℝ)^3423
        have hw : |(-1273514853/10000000000 : ℝ)|=(1273514853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739069883/1250000000 : ℝ)|^4447 ≤ (1578888696691/3125000000000 : ℝ)^3423
        have hw : |(739069883/1250000000 : ℝ)|=(739069883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185016111/10000000000 : ℝ)*x 0 + (1182511783/2000000000 : ℝ)*x 1 + (-127351517/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185016111/10000000000 : ℝ)^4447 ≤ (21300353652193/50000000000000 : ℝ)^3423 := by
    have hnat : (5185016111 : ℕ)^4447*50000000000000^3423 ≤ 21300353652193^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185016111 10000000000 21300353652193 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182511783/2000000000 : ℝ)^4447 ≤ (50524436639971/100000000000000 : ℝ)^3423 := by
    have hnat : (1182511783 : ℕ)^4447*100000000000000^3423 ≤ 50524436639971^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182511783 2000000000 50524436639971 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127351517/1000000000 : ℝ)^4447 ≤ (3437428023589/50000000000000 : ℝ)^3423 := by
    have hnat : (127351517 : ℕ)^4447*50000000000000^3423 ≤ 3437428023589^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127351517 1000000000 3437428023589 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185016111/10000000000 : ℝ), (1182511783/2000000000 : ℝ), (-127351517/1000000000 : ℝ)] ![(21300353652193/50000000000000 : ℝ), (50524436639971/100000000000000 : ℝ), (3437428023589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185016111/10000000000 : ℝ)|^4447 ≤ (21300353652193/50000000000000 : ℝ)^3423
        have hw : |(5185016111/10000000000 : ℝ)|=(5185016111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1182511783/2000000000 : ℝ)|^4447 ≤ (50524436639971/100000000000000 : ℝ)^3423
        have hw : |(1182511783/2000000000 : ℝ)|=(1182511783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127351517/1000000000 : ℝ)|^4447 ≤ (3437428023589/50000000000000 : ℝ)^3423
        have hw : |(-127351517/1000000000 : ℝ)|=(127351517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s0_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163777327/10000000000 : ℝ)*x 0 + (85383107/156250000 : ℝ)*x 1 + (126255329/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163777327/10000000000 : ℝ)^4447 ≤ (8009328887473/25000000000000 : ℝ)^3423 := by
    have hnat : (4163777327 : ℕ)^4447*25000000000000^3423 ≤ 8009328887473^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163777327 10000000000 8009328887473 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85383107/156250000 : ℝ)^4447 ≤ (45607876855383/100000000000000 : ℝ)^3423 := by
    have hnat : (85383107 : ℕ)^4447*100000000000000^3423 ≤ 45607876855383^3423*156250000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85383107 156250000 45607876855383 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126255329/400000000 : ℝ)^4447 ≤ (2235480758357/10000000000000 : ℝ)^3423 := by
    have hnat : (126255329 : ℕ)^4447*10000000000000^3423 ≤ 2235480758357^3423*400000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126255329 400000000 2235480758357 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163777327/10000000000 : ℝ), (85383107/156250000 : ℝ), (126255329/400000000 : ℝ)] ![(8009328887473/25000000000000 : ℝ), (45607876855383/100000000000000 : ℝ), (2235480758357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163777327/10000000000 : ℝ)|^4447 ≤ (8009328887473/25000000000000 : ℝ)^3423
        have hw : |(4163777327/10000000000 : ℝ)|=(4163777327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85383107/156250000 : ℝ)|^4447 ≤ (45607876855383/100000000000000 : ℝ)^3423
        have hw : |(85383107/156250000 : ℝ)|=(85383107/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126255329/400000000 : ℝ)|^4447 ≤ (2235480758357/10000000000000 : ℝ)^3423
        have hw : |(126255329/400000000 : ℝ)|=(126255329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1169/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6493/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4445/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4445 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4445*1^1024 ≤ 0^1024*1^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4445/1024 : ℝ) ≤ (58541513854135607/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4445 ≤ (58541513854135607/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4445*3125000000000000000^1024 ≤ 58541513854135607^1024*5^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 58541513854135607 3125000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (58541513854135607/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4445 := by
      have hnat : (1 : ℕ)^1024*1^4445 ≤ 1^4445*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3183541513854135607/3125000000000000000 : ℝ) ≤ (1255356047675047/1250000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (3183541513854135607/3125000000000000000 : ℝ)^1024 ≤ (1255356047675047/1250000000000000 : ℝ)^4445 := by
      have hnat : (3183541513854135607 : ℕ)^1024*1250000000000000^4445 ≤ 1255356047675047^4445*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3183541513854135607 3125000000000000000 1255356047675047 1250000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255356047675047/1250000000000000 : ℝ)) (X := (3183541513854135607/3125000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1621041513854135607/1562500000000000000 : ℝ) ≤ (630356047675047/625000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (1621041513854135607/1562500000000000000 : ℝ)^1024 ≤ (630356047675047/625000000000000 : ℝ)^4445 := by
      have hnat : (1621041513854135607 : ℕ)^1024*625000000000000^4445 ≤ 630356047675047^4445*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1621041513854135607 1562500000000000000 630356047675047 625000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630356047675047/625000000000000 : ℝ)) (X := (1621041513854135607/1562500000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5356047675047/500000000000000 : ℝ)*(0 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5356047675047/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58541513854135607/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5356047675047/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5356047675047/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1255356047675047/1250000000000000 : ℝ) by norm_num, show 1+(58541513854135607/3125000000000000000 : ℝ)+(0 : ℝ)=(3183541513854135607/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58541513854135607/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5356047675047/500000000000000 : ℝ)*(2/5 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5356047675047/500000000000000 : ℝ)*(2/5 : ℝ)=(630356047675047/625000000000000 : ℝ) by norm_num, show 1+2*(58541513854135607/3125000000000000000 : ℝ)=(1621041513854135607/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5356047675047/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5356047675047/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5356047675047/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5356047675047/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5356047675047/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5356047675047/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-69031613/400000000 : ℝ)*X 0 0+(5941891039/10000000000 : ℝ)*X 0 1+(967834929/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((171439821/312500000 : ℝ)*X 1 0+(-234689941/1000000000 : ℝ)*X 1 1+(4839174557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((171439827/312500000 : ℝ)*X 2 0+(1209793597/2500000000 : ℝ)*X 2 1+(-2346899373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2077637767/5000000000 : ℝ)*X 0 0+(3091600503/10000000000 : ℝ)*X 0 1+(1381762813/2500000000 : ℝ)*X 0 2+(2077637767/5000000000 : ℝ)*X 1 0+(3091600503/10000000000 : ℝ)*X 1 1+(1381762813/2500000000 : ℝ)*X 1 2+(2077637767/5000000000 : ℝ)*X 2 0+(3091600503/10000000000 : ℝ)*X 2 1+(1381762813/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1729639971/10000000000 : ℝ)*X 0 0+(4867487871/10000000000 : ℝ)*X 0 1+(5912558937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1296254041/2500000000 : ℝ)*X 1 0+(-1273514853/10000000000 : ℝ)*X 1 1+(739069883/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185016111/10000000000 : ℝ)*X 2 0+(1182511783/2000000000 : ℝ)*X 2 1+(-127351517/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4163777327/10000000000 : ℝ)*X 0 0+(85383107/156250000 : ℝ)*X 0 1+(126255329/400000000 : ℝ)*X 0 2+(4163777327/10000000000 : ℝ)*X 1 0+(85383107/156250000 : ℝ)*X 1 1+(126255329/400000000 : ℝ)*X 1 2+(4163777327/10000000000 : ℝ)*X 2 0+(85383107/156250000 : ℝ)*X 2 1+(126255329/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (717724357435129195209/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125175907/100000000000000 : ℝ)*(base1) + (1314195471/100000000000000 : ℝ)*(base19) + (1345933429/100000000000000 : ℝ)*(base23) + (35824941/25000000000000 : ℝ)*(upper3) + (163062191/100000000000000 : ℝ)*(upper5) + (13174652234651/2000000000000 : ℝ)*(major0) + (13174652234651/2000000000000 : ℝ)*(major1) + (13174652234651/2000000000000 : ℝ)*(major2) + (226713858412921/25000000000000 : ℝ)*(sp0) + (906858339214447/100000000000000 : ℝ)*(sp1) + (906858307476489/100000000000000 : ℝ)*(sp2) + (410603402025911/100000000000000 : ℝ)*(sp3) + (4344934141/100000000000000 : ℝ)*(sp4) + (925730099/50000000000000 : ℝ)*(sp7) + (410605378662017/100000000000000 : ℝ)*(f.failure) + (453429826704959/50000000000000 : ℝ)*(f.sum) + (240551050903/500000000000000000000000000 : ℝ)*base66 + (3474032829597/1000000000000000000000000000 : ℝ)*base67 + (2779952034597/1000000000000000000000000000 : ℝ)*base69 + (586541649597/1000000000000000000000000000 : ℝ)*base71 + (35807020097/500000000000000000000000000 : ℝ)*base73 + (511047352597/1000000000000000000000000000 : ℝ)*base75 + (380672337597/1000000000000000000000000000 : ℝ)*base77 + (811232584597/1000000000000000000000000000 : ℝ)*base79 + (1149127591097/500000000000000000000000000 : ℝ)*base81 + (87785387/10000000000000000000000 : ℝ)*base89 + (87785387/10000000000000000000000 : ℝ)*base91 + (87785387/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30553554645407147819643/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1408347807/100000000000000 : ℝ)*(base19) + (13985913/1000000000000 : ℝ)*(base23) + (135145843/100000000000000 : ℝ)*(base32) + (52925163/25000000000000 : ℝ)*(upper3) + (128517203/100000000000000 : ℝ)*(upper5) + (695061093265423/100000000000000 : ℝ)*(major0) + (695061093265423/100000000000000 : ℝ)*(major1) + (695061093265423/100000000000000 : ℝ)*(major2) + (3503921189/100000000000000 : ℝ)*(sp1) + (3504338521/100000000000000 : ℝ)*(sp2) + (239218026314207/25000000000000 : ℝ)*(sp4) + (119608399123479/12500000000000 : ℝ)*(sp5) + (956867202327007/100000000000000 : ℝ)*(sp6) + (216624871218903/50000000000000 : ℝ)*(sp7) + (13539058674489/3125000000000 : ℝ)*(f.failure) + (239218026314207/25000000000000 : ℝ)*(f.sum) + (40135389350119/25000000000000000000000000000 : ℝ)*base66 + (304346608800119/50000000000000000000000000000 : ℝ)*base68 + (231905384300119/50000000000000000000000000000 : ℝ)*base70 + (44826095900119/50000000000000000000000000000 : ℝ)*base72 + (197709082550119/25000000000000000000000000000 : ℝ)*base74 + (122086668550119/50000000000000000000000000000 : ℝ)*base76 + (15615320849881/50000000000000000000000000000 : ℝ)*base77 + (107255827050119/50000000000000000000000000000 : ℝ)*base80 + (130970595675119/25000000000000000000000000000 : ℝ)*base82 + (981221/312500000000000000000 : ℝ)*base90 + (981221/312500000000000000000 : ℝ)*base92 + (981221/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1475_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1169/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6493/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1475_s1_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-236196779/1250000000 : ℝ)*x 0 + (559639191/1000000000 : ℝ)*x 1 + (1015913063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236196779/1250000000 : ℝ)^4447 ≤ (11478528502157/100000000000000 : ℝ)^3423 := by
    have hnat : (236196779 : ℕ)^4447*100000000000000^3423 ≤ 11478528502157^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236196779 1250000000 11478528502157 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559639191/1000000000 : ℝ)^4447 ≤ (47042904828099/100000000000000 : ℝ)^3423 := by
    have hnat : (559639191 : ℕ)^4447*100000000000000^3423 ≤ 47042904828099^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559639191 1000000000 47042904828099 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015913063/2000000000 : ℝ)^4447 ≤ (10369641665123/25000000000000 : ℝ)^3423 := by
    have hnat : (1015913063 : ℕ)^4447*25000000000000^3423 ≤ 10369641665123^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015913063 2000000000 10369641665123 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236196779/1250000000 : ℝ), (559639191/1000000000 : ℝ), (1015913063/2000000000 : ℝ)] ![(11478528502157/100000000000000 : ℝ), (47042904828099/100000000000000 : ℝ), (10369641665123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236196779/1250000000 : ℝ)|^4447 ≤ (11478528502157/100000000000000 : ℝ)^3423
        have hw : |(-236196779/1250000000 : ℝ)|=(236196779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559639191/1000000000 : ℝ)|^4447 ≤ (47042904828099/100000000000000 : ℝ)^3423
        have hw : |(559639191/1000000000 : ℝ)|=(559639191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015913063/2000000000 : ℝ)|^4447 ≤ (10369641665123/25000000000000 : ℝ)^3423
        have hw : |(1015913063/2000000000 : ℝ)|=(1015913063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674189023/1250000000 : ℝ)*x 0 + (-432608401/2000000000 : ℝ)*x 1 + (634946081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674189023/1250000000 : ℝ)^4447 ≤ (22419727452301/50000000000000 : ℝ)^3423 := by
    have hnat : (674189023 : ℕ)^4447*50000000000000^3423 ≤ 22419727452301^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674189023 1250000000 22419727452301 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432608401/2000000000 : ℝ)^4447 ≤ (2736388613281/20000000000000 : ℝ)^3423 := by
    have hnat : (432608401 : ℕ)^4447*20000000000000^3423 ≤ 2736388613281^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432608401 2000000000 2736388613281 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634946081/1250000000 : ℝ)^4447 ≤ (20739301009453/50000000000000 : ℝ)^3423 := by
    have hnat : (634946081 : ℕ)^4447*50000000000000^3423 ≤ 20739301009453^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634946081 1250000000 20739301009453 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674189023/1250000000 : ℝ), (-432608401/2000000000 : ℝ), (634946081/1250000000 : ℝ)] ![(22419727452301/50000000000000 : ℝ), (2736388613281/20000000000000 : ℝ), (20739301009453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674189023/1250000000 : ℝ)|^4447 ≤ (22419727452301/50000000000000 : ℝ)^3423
        have hw : |(674189023/1250000000 : ℝ)|=(674189023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432608401/2000000000 : ℝ)|^4447 ≤ (2736388613281/20000000000000 : ℝ)^3423
        have hw : |(-432608401/2000000000 : ℝ)|=(432608401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634946081/1250000000 : ℝ)|^4447 ≤ (20739301009453/50000000000000 : ℝ)^3423
        have hw : |(634946081/1250000000 : ℝ)|=(634946081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696757351/5000000000 : ℝ)*x 0 + (2539782939/5000000000 : ℝ)*x 1 + (-2163042271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696757351/5000000000 : ℝ)^4447 ≤ (22419741050289/50000000000000 : ℝ)^3423 := by
    have hnat : (2696757351 : ℕ)^4447*50000000000000^3423 ≤ 22419741050289^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696757351 5000000000 22419741050289 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539782939/5000000000 : ℝ)^4447 ≤ (66365716213/160000000000 : ℝ)^3423 := by
    have hnat : (2539782939 : ℕ)^4447*160000000000^3423 ≤ 66365716213^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539782939 5000000000 66365716213 160000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163042271/10000000000 : ℝ)^4447 ≤ (13681945252277/100000000000000 : ℝ)^3423 := by
    have hnat : (2163042271 : ℕ)^4447*100000000000000^3423 ≤ 13681945252277^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163042271 10000000000 13681945252277 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696757351/5000000000 : ℝ), (2539782939/5000000000 : ℝ), (-2163042271/10000000000 : ℝ)] ![(22419741050289/50000000000000 : ℝ), (66365716213/160000000000 : ℝ), (13681945252277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696757351/5000000000 : ℝ)|^4447 ≤ (22419741050289/50000000000000 : ℝ)^3423
        have hw : |(2696757351/5000000000 : ℝ)|=(2696757351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539782939/5000000000 : ℝ)|^4447 ≤ (66365716213/160000000000 : ℝ)^3423
        have hw : |(2539782939/5000000000 : ℝ)|=(2539782939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2163042271/10000000000 : ℝ)|^4447 ≤ (13681945252277/100000000000000 : ℝ)^3423
        have hw : |(-2163042271/10000000000 : ℝ)|=(2163042271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4263078309/10000000000 : ℝ)*x 0 + (149024409/400000000 : ℝ)*x 1 + (4867062171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263078309/10000000000 : ℝ)^4447 ≤ (33033455473533/100000000000000 : ℝ)^3423 := by
    have hnat : (4263078309 : ℕ)^4447*100000000000000^3423 ≤ 33033455473533^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263078309 10000000000 33033455473533 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149024409/400000000 : ℝ)^4447 ≤ (2772808826091/10000000000000 : ℝ)^3423 := by
    have hnat : (149024409 : ℕ)^4447*10000000000000^3423 ≤ 2772808826091^3423*400000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149024409 400000000 2772808826091 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4867062171/10000000000 : ℝ)^4447 ≤ (39238456248549/100000000000000 : ℝ)^3423 := by
    have hnat : (4867062171 : ℕ)^4447*100000000000000^3423 ≤ 39238456248549^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867062171 10000000000 39238456248549 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263078309/10000000000 : ℝ), (149024409/400000000 : ℝ), (4867062171/10000000000 : ℝ)] ![(33033455473533/100000000000000 : ℝ), (2772808826091/10000000000000 : ℝ), (39238456248549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263078309/10000000000 : ℝ)|^4447 ≤ (33033455473533/100000000000000 : ℝ)^3423
        have hw : |(4263078309/10000000000 : ℝ)|=(4263078309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149024409/400000000 : ℝ)|^4447 ≤ (2772808826091/10000000000000 : ℝ)^3423
        have hw : |(149024409/400000000 : ℝ)|=(149024409/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4867062171/10000000000 : ℝ)|^4447 ≤ (39238456248549/100000000000000 : ℝ)^3423
        have hw : |(4867062171/10000000000 : ℝ)|=(4867062171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-59061113/312500000 : ℝ)*x 0 + (5085657319/10000000000 : ℝ)*x 1 + (5590196251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59061113/312500000 : ℝ)^4447 ≤ (11481538443757/100000000000000 : ℝ)^3423 := by
    have hnat : (59061113 : ℕ)^4447*100000000000000^3423 ≤ 11481538443757^3423*312500000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59061113 312500000 11481538443757 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085657319/10000000000 : ℝ)^4447 ≤ (41543205787227/100000000000000 : ℝ)^3423 := by
    have hnat : (5085657319 : ℕ)^4447*100000000000000^3423 ≤ 41543205787227^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085657319 10000000000 41543205787227 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590196251/10000000000 : ℝ)^4447 ≤ (23487627880871/50000000000000 : ℝ)^3423 := by
    have hnat : (5590196251 : ℕ)^4447*50000000000000^3423 ≤ 23487627880871^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590196251 10000000000 23487627880871 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59061113/312500000 : ℝ), (5085657319/10000000000 : ℝ), (5590196251/10000000000 : ℝ)] ![(11481538443757/100000000000000 : ℝ), (41543205787227/100000000000000 : ℝ), (23487627880871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59061113/312500000 : ℝ)|^4447 ≤ (11481538443757/100000000000000 : ℝ)^3423
        have hw : |(-59061113/312500000 : ℝ)|=(59061113/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085657319/10000000000 : ℝ)|^4447 ≤ (41543205787227/100000000000000 : ℝ)^3423
        have hw : |(5085657319/10000000000 : ℝ)|=(5085657319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5590196251/10000000000 : ℝ)|^4447 ≤ (23487627880871/50000000000000 : ℝ)^3423
        have hw : |(5590196251/10000000000 : ℝ)|=(5590196251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258025083/10000000000 : ℝ)*x 0 + (-103275853/625000000 : ℝ)*x 1 + (2795098139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258025083/10000000000 : ℝ)^4447 ≤ (8676328107841/20000000000000 : ℝ)^3423 := by
    have hnat : (5258025083 : ℕ)^4447*20000000000000^3423 ≤ 8676328107841^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258025083 10000000000 8676328107841 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103275853/625000000 : ℝ)^4447 ≤ (4821551693239/50000000000000 : ℝ)^3423 := by
    have hnat : (103275853 : ℕ)^4447*50000000000000^3423 ≤ 4821551693239^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103275853 625000000 4821551693239 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2795098139/5000000000 : ℝ)^4447 ≤ (46975256056501/100000000000000 : ℝ)^3423 := by
    have hnat : (2795098139 : ℕ)^4447*100000000000000^3423 ≤ 46975256056501^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795098139 5000000000 46975256056501 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258025083/10000000000 : ℝ), (-103275853/625000000 : ℝ), (2795098139/5000000000 : ℝ)] ![(8676328107841/20000000000000 : ℝ), (4821551693239/50000000000000 : ℝ), (46975256056501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258025083/10000000000 : ℝ)|^4447 ≤ (8676328107841/20000000000000 : ℝ)^3423
        have hw : |(5258025083/10000000000 : ℝ)|=(5258025083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103275853/625000000 : ℝ)|^4447 ≤ (4821551693239/50000000000000 : ℝ)^3423
        have hw : |(-103275853/625000000 : ℝ)|=(103275853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2795098139/5000000000 : ℝ)|^4447 ≤ (46975256056501/100000000000000 : ℝ)^3423
        have hw : |(2795098139/5000000000 : ℝ)|=(2795098139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258025127/10000000000 : ℝ)*x 0 + (2795098121/5000000000 : ℝ)*x 1 + (-826206819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258025127/10000000000 : ℝ)^4447 ≤ (4338164101083/10000000000000 : ℝ)^3423 := by
    have hnat : (5258025127 : ℕ)^4447*10000000000000^3423 ≤ 4338164101083^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258025127 10000000000 4338164101083 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795098121/5000000000 : ℝ)^4447 ≤ (4697525566349/10000000000000 : ℝ)^3423 := by
    have hnat : (2795098121 : ℕ)^4447*10000000000000^3423 ≤ 4697525566349^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795098121 5000000000 4697525566349 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826206819/5000000000 : ℝ)^4447 ≤ (9643103310663/100000000000000 : ℝ)^3423 := by
    have hnat : (826206819 : ℕ)^4447*100000000000000^3423 ≤ 9643103310663^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826206819 5000000000 9643103310663 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258025127/10000000000 : ℝ), (2795098121/5000000000 : ℝ), (-826206819/5000000000 : ℝ)] ![(4338164101083/10000000000000 : ℝ), (4697525566349/10000000000000 : ℝ), (9643103310663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258025127/10000000000 : ℝ)|^4447 ≤ (4338164101083/10000000000000 : ℝ)^3423
        have hw : |(5258025127/10000000000 : ℝ)|=(5258025127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2795098121/5000000000 : ℝ)|^4447 ≤ (4697525566349/10000000000000 : ℝ)^3423
        have hw : |(2795098121/5000000000 : ℝ)|=(2795098121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-826206819/5000000000 : ℝ)|^4447 ≤ (9643103310663/100000000000000 : ℝ)^3423
        have hw : |(-826206819/5000000000 : ℝ)|=(826206819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s1_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852784511/2000000000 : ℝ)*x 0 + (1213402581/2500000000 : ℝ)*x 1 + (747857839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852784511/2000000000 : ℝ)^4447 ≤ (8260488642707/25000000000000 : ℝ)^3423 := by
    have hnat : (852784511 : ℕ)^4447*25000000000000^3423 ≤ 8260488642707^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852784511 2000000000 8260488642707 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213402581/2500000000 : ℝ)^4447 ≤ (39097622261507/100000000000000 : ℝ)^3423 := by
    have hnat : (1213402581 : ℕ)^4447*100000000000000^3423 ≤ 39097622261507^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213402581 2500000000 39097622261507 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (747857839/2000000000 : ℝ)^4447 ≤ (6965105788961/25000000000000 : ℝ)^3423 := by
    have hnat : (747857839 : ℕ)^4447*25000000000000^3423 ≤ 6965105788961^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747857839 2000000000 6965105788961 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852784511/2000000000 : ℝ), (1213402581/2500000000 : ℝ), (747857839/2000000000 : ℝ)] ![(8260488642707/25000000000000 : ℝ), (39097622261507/100000000000000 : ℝ), (6965105788961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852784511/2000000000 : ℝ)|^4447 ≤ (8260488642707/25000000000000 : ℝ)^3423
        have hw : |(852784511/2000000000 : ℝ)|=(852784511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1213402581/2500000000 : ℝ)|^4447 ≤ (39097622261507/100000000000000 : ℝ)^3423
        have hw : |(1213402581/2500000000 : ℝ)|=(1213402581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(747857839/2000000000 : ℝ)|^4447 ≤ (6965105788961/25000000000000 : ℝ)^3423
        have hw : |(747857839/2000000000 : ℝ)|=(747857839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1169/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7831/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1169/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1169/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1169/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1169/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1169/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1169/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1169/50000 : ℝ) ^ (4445/1024 : ℝ) ≤ (519190957223/6250000000000000000 : ℝ) := by
    have hpowers : (1169/50000 : ℝ)^4445 ≤ (519190957223/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1169 : ℕ)^4445*6250000000000000000^1024 ≤ 519190957223^1024*50000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1169 50000 519190957223 6250000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1169/50000 : ℝ)) (X := (519190957223/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6493/25000 : ℝ) ^ (4445/1024 : ℝ) ≤ (287390972695198241/100000000000000000000 : ℝ) := by
    have hpowers : (6493/25000 : ℝ)^4445 ≤ (287390972695198241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6493 : ℕ)^4445*100000000000000000000^1024 ≤ 287390972695198241^1024*25000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6493 25000 287390972695198241 100000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6493/25000 : ℝ)) (X := (287390972695198241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000519190957223/3125000000000000000 : ℝ) ≤ (5000000191370621/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (3125000519190957223/3125000000000000000 : ℝ)^1024 ≤ (5000000191370621/5000000000000000 : ℝ)^4445 := by
      have hnat : (3125000519190957223 : ℕ)^1024*5000000000000000^4445 ≤ 5000000191370621^4445*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000519190957223 3125000000000000000 5000000191370621 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000191370621/5000000000000000 : ℝ)) (X := (3125000519190957223/3125000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100287399279750513809/100000000000000000000 : ℝ) ≤ (2001322708366331/2000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (100287399279750513809/100000000000000000000 : ℝ)^1024 ≤ (2001322708366331/2000000000000000 : ℝ)^4445 := by
      have hnat : (100287399279750513809 : ℕ)^1024*2000000000000000^4445 ≤ 2001322708366331^4445*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100287399279750513809 100000000000000000000 2001322708366331 2000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001322708366331/2000000000000000 : ℝ)) (X := (100287399279750513809/100000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50287390972695198241/50000000000000000000 : ℝ) ≤ (2503306675230517/2500000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (50287390972695198241/50000000000000000000 : ℝ)^1024 ≤ (2503306675230517/2500000000000000 : ℝ)^4445 := by
      have hnat : (50287390972695198241 : ℕ)^1024*2500000000000000^4445 ≤ 2503306675230517^4445*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50287390972695198241 50000000000000000000 2503306675230517 2500000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503306675230517/2500000000000000 : ℝ)) (X := (50287390972695198241/50000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(519190957223/6250000000000000000 : ℝ) ≤ ((492310595653749463/492375000000000000 : ℝ)+2*(2204386363471/787800000000000 : ℝ)*(1169/50000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (492310595653749463/492375000000000000 : ℝ)+2*(2204386363471/787800000000000 : ℝ)*(1169/50000 : ℝ)=(5000000191370621/5000000000000000 : ℝ) by norm_num, show 1+2*(519190957223/6250000000000000000 : ℝ)=(3125000519190957223/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(287390972695198241/100000000000000000000 : ℝ)+(519190957223/6250000000000000000 : ℝ) ≤ ((492310595653749463/492375000000000000 : ℝ)+(2204386363471/787800000000000 : ℝ)*((6493/25000 : ℝ)+(1169/50000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (492310595653749463/492375000000000000 : ℝ)+(2204386363471/787800000000000 : ℝ)*((6493/25000 : ℝ)+(1169/50000 : ℝ))=(2001322708366331/2000000000000000 : ℝ) by norm_num, show 1+(287390972695198241/100000000000000000000 : ℝ)+(519190957223/6250000000000000000 : ℝ)=(100287399279750513809/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(287390972695198241/100000000000000000000 : ℝ) ≤ ((492310595653749463/492375000000000000 : ℝ)+2*(2204386363471/787800000000000 : ℝ)*(6493/25000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (492310595653749463/492375000000000000 : ℝ)+2*(2204386363471/787800000000000 : ℝ)*(6493/25000 : ℝ)=(2503306675230517/2500000000000000 : ℝ) by norm_num, show 1+2*(287390972695198241/100000000000000000000 : ℝ)=(50287390972695198241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (492310595653749463/492375000000000000 : ℝ)*(X 1 0+X 2 0)+(2204386363471/787800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (1169/50000 : ℝ)) (hi := (6493/25000 : ℝ)) (c := (492310595653749463/492375000000000000 : ℝ)) (alpha := (2204386363471/787800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (492310595653749463/492375000000000000 : ℝ)*(X 0 1+X 2 1)+(2204386363471/787800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (1169/50000 : ℝ)) (hi := (6493/25000 : ℝ)) (c := (492310595653749463/492375000000000000 : ℝ)) (alpha := (2204386363471/787800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (492310595653749463/492375000000000000 : ℝ)*(X 0 2+X 1 2)+(2204386363471/787800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (1169/50000 : ℝ)) (hi := (6493/25000 : ℝ)) (c := (492310595653749463/492375000000000000 : ℝ)) (alpha := (2204386363471/787800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-236196779/1250000000 : ℝ)*X 0 0+(559639191/1000000000 : ℝ)*X 0 1+(1015913063/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((674189023/1250000000 : ℝ)*X 1 0+(-432608401/2000000000 : ℝ)*X 1 1+(634946081/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2696757351/5000000000 : ℝ)*X 2 0+(2539782939/5000000000 : ℝ)*X 2 1+(-2163042271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4263078309/10000000000 : ℝ)*X 0 0+(149024409/400000000 : ℝ)*X 0 1+(4867062171/10000000000 : ℝ)*X 0 2+(4263078309/10000000000 : ℝ)*X 1 0+(149024409/400000000 : ℝ)*X 1 1+(4867062171/10000000000 : ℝ)*X 1 2+(4263078309/10000000000 : ℝ)*X 2 0+(149024409/400000000 : ℝ)*X 2 1+(4867062171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-59061113/312500000 : ℝ)*X 0 0+(5085657319/10000000000 : ℝ)*X 0 1+(5590196251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258025083/10000000000 : ℝ)*X 1 0+(-103275853/625000000 : ℝ)*X 1 1+(2795098139/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258025127/10000000000 : ℝ)*X 2 0+(2795098121/5000000000 : ℝ)*X 2 1+(-826206819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((852784511/2000000000 : ℝ)*X 0 0+(1213402581/2500000000 : ℝ)*X 0 1+(747857839/2000000000 : ℝ)*X 0 2+(852784511/2000000000 : ℝ)*X 1 0+(1213402581/2500000000 : ℝ)*X 1 1+(747857839/2000000000 : ℝ)*X 1 2+(852784511/2000000000 : ℝ)*X 2 0+(1213402581/2500000000 : ℝ)*X 2 1+(747857839/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33558814937926151433342883/4103125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1311040643/100000000000000 : ℝ)*(base19) + (24774553/1250000000000 : ℝ)*(base23) + (163781173/100000000000000 : ℝ)*(upper3) + (15668821/12500000000000 : ℝ)*(upper4) + (28100039/50000000000000 : ℝ)*(upper5) + (702754379405053/50000000000000 : ℝ)*(major0) + (702754379405053/50000000000000 : ℝ)*(major1) + (702754379405053/50000000000000 : ℝ)*(major2) + (483726144707021/25000000000000 : ℝ)*(sp0) + (1934925323216199/100000000000000 : ℝ)*(sp1) + (967462326146301/50000000000000 : ℝ)*(sp2) + (876082921640471/100000000000000 : ℝ)*(sp3) + (11027714379/50000000000000 : ℝ)*(sp4) + (7689094791/100000000000000 : ℝ)*(sp7) + (438045305367631/50000000000000 : ℝ)*(f.failure) + (967463317128421/50000000000000 : ℝ)*(f.sum) + (27279404011997/19695000000000000000000000000 : ℝ)*base66 + (41204647181074333/3077343750000000000000000000000 : ℝ)*base67 + (41923265812369207/12309375000000000000000000000000 : ℝ)*base69 + (45971515749919207/12309375000000000000000000000000 : ℝ)*base71 + (140719317514483/19695000000000000000000000000 : ℝ)*base73 + (103930065419475457/12309375000000000000000000000000 : ℝ)*base75 + (51877972541381707/12309375000000000000000000000000 : ℝ)*base77 + (68826795701451791/6154687500000000000000000000000 : ℝ)*base79 + (8707186734617/19695000000000000000000000000 : ℝ)*base82 + (46678459/5000000000000000000000 : ℝ)*base90 + (46678459/5000000000000000000000 : ℝ)*base92 + (46678459/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31476114475288929598209747/8206250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367252617/50000000000000 : ℝ)*(base19) + (79495217/10000000000000 : ℝ)*(base23) + (6616471/6250000000000 : ℝ)*(upper3) + (15876391/100000000000000 : ℝ)*(lower4) + (74743399/100000000000000 : ℝ)*(upper5) + (1439707392360897/100000000000000 : ℝ)*(major0) + (1439707392360897/100000000000000 : ℝ)*(major1) + (1439707392360897/100000000000000 : ℝ)*(major2) + (4374817603/100000000000000 : ℝ)*(sp1) + (613138199/12500000000000 : ℝ)*(sp2) + (1982007137528187/100000000000000 : ℝ)*(sp4) + (39640040564107/2000000000000 : ℝ)*(sp5) + (79280057498817/4000000000000 : ℝ)*(sp6) + (112175939917421/12500000000000 : ℝ)*(sp7) + (112175939917421/12500000000000 : ℝ)*(f.failure) + (1982007137528187/100000000000000 : ℝ)*(f.sum) + (27006019042411/13130000000000000000000000000 : ℝ)*base66 + (4683869199865031/8206250000000000000000000000000 : ℝ)*base67 + (34190530569859969/8206250000000000000000000000000 : ℝ)*base70 + (27952619754766219/8206250000000000000000000000000 : ℝ)*base72 + (14226023202619/13130000000000000000000000000 : ℝ)*base73 + (59898833466678719/8206250000000000000000000000000 : ℝ)*base76 + (35755233506897469/8206250000000000000000000000000 : ℝ)*base78 + (53957845366066219/8206250000000000000000000000000 : ℝ)*base80 + (27776699229311/13130000000000000000000000000 : ℝ)*base82 + (10653231/1250000000000000000000 : ℝ)*base89 + (10653231/1250000000000000000000 : ℝ)*base91 + (10653231/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1475_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1169/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1475_s2_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-119917467/625000000 : ℝ)*x 0 + (5470782151/10000000000 : ℝ)*x 1 + (5186396931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119917467/625000000 : ℝ)^4447 ≤ (2341750388639/20000000000000 : ℝ)^3423 := by
    have hnat : (119917467 : ℕ)^4447*20000000000000^3423 ≤ 2341750388639^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119917467 625000000 2341750388639 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470782151/10000000000 : ℝ)^4447 ≤ (45675801286387/100000000000000 : ℝ)^3423 := by
    have hnat : (5470782151 : ℕ)^4447*100000000000000^3423 ≤ 45675801286387^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470782151 10000000000 45675801286387 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186396931/10000000000 : ℝ)^4447 ≤ (42615446755019/100000000000000 : ℝ)^3423 := by
    have hnat : (5186396931 : ℕ)^4447*100000000000000^3423 ≤ 42615446755019^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186396931 10000000000 42615446755019 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119917467/625000000 : ℝ), (5470782151/10000000000 : ℝ), (5186396931/10000000000 : ℝ)] ![(2341750388639/20000000000000 : ℝ), (45675801286387/100000000000000 : ℝ), (42615446755019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119917467/625000000 : ℝ)|^4447 ≤ (2341750388639/20000000000000 : ℝ)^3423
        have hw : |(-119917467/625000000 : ℝ)|=(119917467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470782151/10000000000 : ℝ)|^4447 ≤ (45675801286387/100000000000000 : ℝ)^3423
        have hw : |(5470782151/10000000000 : ℝ)|=(5470782151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186396931/10000000000 : ℝ)|^4447 ≤ (42615446755019/100000000000000 : ℝ)^3423
        have hw : |(5186396931/10000000000 : ℝ)|=(5186396931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680993763/5000000000 : ℝ)*x 0 + (-129089439/625000000 : ℝ)*x 1 + (1296599119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680993763/5000000000 : ℝ)^4447 ≤ (8899853394899/20000000000000 : ℝ)^3423 := by
    have hnat : (2680993763 : ℕ)^4447*20000000000000^3423 ≤ 8899853394899^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680993763 5000000000 8899853394899 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129089439/625000000 : ℝ)^4447 ≤ (3221322777361/25000000000000 : ℝ)^3423 := by
    have hnat : (129089439 : ℕ)^4447*25000000000000^3423 ≤ 3221322777361^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129089439 625000000 3221322777361 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296599119/2500000000 : ℝ)^4447 ≤ (8523088379593/20000000000000 : ℝ)^3423 := by
    have hnat : (1296599119 : ℕ)^4447*20000000000000^3423 ≤ 8523088379593^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296599119 2500000000 8523088379593 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680993763/5000000000 : ℝ), (-129089439/625000000 : ℝ), (1296599119/2500000000 : ℝ)] ![(8899853394899/20000000000000 : ℝ), (3221322777361/25000000000000 : ℝ), (8523088379593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680993763/5000000000 : ℝ)|^4447 ≤ (8899853394899/20000000000000 : ℝ)^3423
        have hw : |(2680993763/5000000000 : ℝ)|=(2680993763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129089439/625000000 : ℝ)|^4447 ≤ (3221322777361/25000000000000 : ℝ)^3423
        have hw : |(-129089439/625000000 : ℝ)|=(129089439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296599119/2500000000 : ℝ)|^4447 ≤ (8523088379593/20000000000000 : ℝ)^3423
        have hw : |(1296599119/2500000000 : ℝ)|=(1296599119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361987401/10000000000 : ℝ)*x 0 + (5186396421/10000000000 : ℝ)*x 1 + (-2065431263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361987401/10000000000 : ℝ)^4447 ≤ (22249632813391/50000000000000 : ℝ)^3423 := by
    have hnat : (5361987401 : ℕ)^4447*50000000000000^3423 ≤ 22249632813391^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361987401 10000000000 22249632813391 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186396421/10000000000 : ℝ)^4447 ≤ (42615441310849/100000000000000 : ℝ)^3423 := by
    have hnat : (5186396421 : ℕ)^4447*100000000000000^3423 ≤ 42615441310849^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186396421 10000000000 42615441310849 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065431263/10000000000 : ℝ)^4447 ≤ (6442646523249/50000000000000 : ℝ)^3423 := by
    have hnat : (2065431263 : ℕ)^4447*50000000000000^3423 ≤ 6442646523249^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065431263 10000000000 6442646523249 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361987401/10000000000 : ℝ), (5186396421/10000000000 : ℝ), (-2065431263/10000000000 : ℝ)] ![(22249632813391/50000000000000 : ℝ), (42615441310849/100000000000000 : ℝ), (6442646523249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361987401/10000000000 : ℝ)|^4447 ≤ (22249632813391/50000000000000 : ℝ)^3423
        have hw : |(5361987401/10000000000 : ℝ)|=(5361987401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186396421/10000000000 : ℝ)|^4447 ≤ (42615441310849/100000000000000 : ℝ)^3423
        have hw : |(5186396421/10000000000 : ℝ)|=(5186396421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065431263/10000000000 : ℝ)|^4447 ≤ (6442646523249/50000000000000 : ℝ)^3423
        have hw : |(-2065431263/10000000000 : ℝ)|=(2065431263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141915501/5000000000 : ℝ)*x 0 + (3979853459/10000000000 : ℝ)*x 1 + (2303972851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141915501/5000000000 : ℝ)^4447 ≤ (33242520380747/100000000000000 : ℝ)^3423 := by
    have hnat : (2141915501 : ℕ)^4447*100000000000000^3423 ≤ 33242520380747^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141915501 5000000000 33242520380747 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979853459/10000000000 : ℝ)^4447 ≤ (15105538311569/50000000000000 : ℝ)^3423 := by
    have hnat : (3979853459 : ℕ)^4447*50000000000000^3423 ≤ 15105538311569^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979853459 10000000000 15105538311569 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303972851/5000000000 : ℝ)^4447 ≤ (18273201492677/50000000000000 : ℝ)^3423 := by
    have hnat : (2303972851 : ℕ)^4447*50000000000000^3423 ≤ 18273201492677^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303972851 5000000000 18273201492677 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141915501/5000000000 : ℝ), (3979853459/10000000000 : ℝ), (2303972851/5000000000 : ℝ)] ![(33242520380747/100000000000000 : ℝ), (15105538311569/50000000000000 : ℝ), (18273201492677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141915501/5000000000 : ℝ)|^4447 ≤ (33242520380747/100000000000000 : ℝ)^3423
        have hw : |(2141915501/5000000000 : ℝ)|=(2141915501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979853459/10000000000 : ℝ)|^4447 ≤ (15105538311569/50000000000000 : ℝ)^3423
        have hw : |(3979853459/10000000000 : ℝ)|=(3979853459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2303972851/5000000000 : ℝ)|^4447 ≤ (18273201492677/50000000000000 : ℝ)^3423
        have hw : |(2303972851/5000000000 : ℝ)|=(2303972851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1918743051/10000000000 : ℝ)*x 0 + (259412509/500000000 : ℝ)*x 1 + (5468911597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1918743051/10000000000 : ℝ)^4447 ≤ (365914250173/3125000000000 : ℝ)^3423 := by
    have hnat : (1918743051 : ℕ)^4447*3125000000000^3423 ≤ 365914250173^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918743051 10000000000 365914250173 3125000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259412509/500000000 : ℝ)^4447 ≤ (42635230955691/100000000000000 : ℝ)^3423 := by
    have hnat : (259412509 : ℕ)^4447*100000000000000^3423 ≤ 42635230955691^3423*500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259412509 500000000 42635230955691 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468911597/10000000000 : ℝ)^4447 ≤ (22827756508083/50000000000000 : ℝ)^3423 := by
    have hnat : (5468911597 : ℕ)^4447*50000000000000^3423 ≤ 22827756508083^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468911597 10000000000 22827756508083 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1918743051/10000000000 : ℝ), (259412509/500000000 : ℝ), (5468911597/10000000000 : ℝ)] ![(365914250173/3125000000000 : ℝ), (42635230955691/100000000000000 : ℝ), (22827756508083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1918743051/10000000000 : ℝ)|^4447 ≤ (365914250173/3125000000000 : ℝ)^3423
        have hw : |(-1918743051/10000000000 : ℝ)|=(1918743051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259412509/500000000 : ℝ)|^4447 ≤ (42635230955691/100000000000000 : ℝ)^3423
        have hw : |(259412509/500000000 : ℝ)|=(259412509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468911597/10000000000 : ℝ)|^4447 ≤ (22827756508083/50000000000000 : ℝ)^3423
        have hw : |(5468911597/10000000000 : ℝ)|=(5468911597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287746747/10000000000 : ℝ)*x 0 + (-445729163/2500000000 : ℝ)*x 1 + (2734455813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287746747/10000000000 : ℝ)^4447 ≤ (8740097638639/20000000000000 : ℝ)^3423 := by
    have hnat : (5287746747 : ℕ)^4447*20000000000000^3423 ≤ 8740097638639^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287746747 10000000000 8740097638639 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445729163/2500000000 : ℝ)^4447 ≤ (10643998455659/100000000000000 : ℝ)^3423 := by
    have hnat : (445729163 : ℕ)^4447*100000000000000^3423 ≤ 10643998455659^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445729163 2500000000 10643998455659 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734455813/5000000000 : ℝ)^4447 ≤ (44585462237/97656250000 : ℝ)^3423 := by
    have hnat : (2734455813 : ℕ)^4447*97656250000^3423 ≤ 44585462237^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734455813 5000000000 44585462237 97656250000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287746747/10000000000 : ℝ), (-445729163/2500000000 : ℝ), (2734455813/5000000000 : ℝ)] ![(8740097638639/20000000000000 : ℝ), (10643998455659/100000000000000 : ℝ), (44585462237/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287746747/10000000000 : ℝ)|^4447 ≤ (8740097638639/20000000000000 : ℝ)^3423
        have hw : |(5287746747/10000000000 : ℝ)|=(5287746747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445729163/2500000000 : ℝ)|^4447 ≤ (10643998455659/100000000000000 : ℝ)^3423
        have hw : |(-445729163/2500000000 : ℝ)|=(445729163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734455813/5000000000 : ℝ)|^4447 ≤ (44585462237/97656250000 : ℝ)^3423
        have hw : |(2734455813/5000000000 : ℝ)|=(2734455813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528774699/1000000000 : ℝ)*x 0 + (5468911657/10000000000 : ℝ)*x 1 + (-1782916273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528774699/1000000000 : ℝ)^4447 ≤ (43700490802243/100000000000000 : ℝ)^3423 := by
    have hnat : (528774699 : ℕ)^4447*100000000000000^3423 ≤ 43700490802243^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528774699 1000000000 43700490802243 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468911657/10000000000 : ℝ)^4447 ≤ (456555136669/1000000000000 : ℝ)^3423 := by
    have hnat : (5468911657 : ℕ)^4447*1000000000000^3423 ≤ 456555136669^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468911657 10000000000 456555136669 1000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1782916273/10000000000 : ℝ)^4447 ≤ (10643995516161/100000000000000 : ℝ)^3423 := by
    have hnat : (1782916273 : ℕ)^4447*100000000000000^3423 ≤ 10643995516161^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782916273 10000000000 10643995516161 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528774699/1000000000 : ℝ), (5468911657/10000000000 : ℝ), (-1782916273/10000000000 : ℝ)] ![(43700490802243/100000000000000 : ℝ), (456555136669/1000000000000 : ℝ), (10643995516161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528774699/1000000000 : ℝ)|^4447 ≤ (43700490802243/100000000000000 : ℝ)^3423
        have hw : |(528774699/1000000000 : ℝ)|=(528774699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468911657/10000000000 : ℝ)|^4447 ≤ (456555136669/1000000000000 : ℝ)^3423
        have hw : |(5468911657/10000000000 : ℝ)|=(5468911657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1782916273/10000000000 : ℝ)|^4447 ≤ (10643995516161/100000000000000 : ℝ)^3423
        have hw : |(-1782916273/10000000000 : ℝ)|=(1782916273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s2_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141985751/5000000000 : ℝ)*x 0 + (4603851989/10000000000 : ℝ)*x 1 + (3983985781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141985751/5000000000 : ℝ)^4447 ≤ (664878736553/2000000000000 : ℝ)^3423 := by
    have hnat : (2141985751 : ℕ)^4447*2000000000000^3423 ≤ 664878736553^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141985751 5000000000 664878736553 2000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4603851989/10000000000 : ℝ)^4447 ≤ (36504227782361/100000000000000 : ℝ)^3423 := by
    have hnat : (4603851989 : ℕ)^4447*100000000000000^3423 ≤ 36504227782361^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603851989 10000000000 36504227782361 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983985781/10000000000 : ℝ)^4447 ≤ (30251835380411/100000000000000 : ℝ)^3423 := by
    have hnat : (3983985781 : ℕ)^4447*100000000000000^3423 ≤ 30251835380411^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983985781 10000000000 30251835380411 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141985751/5000000000 : ℝ), (4603851989/10000000000 : ℝ), (3983985781/10000000000 : ℝ)] ![(664878736553/2000000000000 : ℝ), (36504227782361/100000000000000 : ℝ), (30251835380411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141985751/5000000000 : ℝ)|^4447 ≤ (664878736553/2000000000000 : ℝ)^3423
        have hw : |(2141985751/5000000000 : ℝ)|=(2141985751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4603851989/10000000000 : ℝ)|^4447 ≤ (36504227782361/100000000000000 : ℝ)^3423
        have hw : |(4603851989/10000000000 : ℝ)|=(4603851989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983985781/10000000000 : ℝ)|^4447 ≤ (30251835380411/100000000000000 : ℝ)^3423
        have hw : |(3983985781/10000000000 : ℝ)|=(3983985781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (507/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3231/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7831/100000 : ℝ) ^ (4445/1024 : ℝ) ≤ (157855361255489/10000000000000000000 : ℝ) := by
    have hpowers : (7831/100000 : ℝ)^4445 ≤ (157855361255489/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7831 : ℕ)^4445*10000000000000000000^1024 ≤ 157855361255489^1024*100000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7831 100000 157855361255489 10000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7831/100000 : ℝ)) (X := (157855361255489/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4689/25000 : ℝ) ^ (4445/1024 : ℝ) ≤ (69957184140295887/100000000000000000000 : ℝ) := by
    have hpowers : (4689/25000 : ℝ)^4445 ≤ (69957184140295887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4689 : ℕ)^4445*100000000000000000000^1024 ≤ 69957184140295887^1024*25000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4689 25000 69957184140295887 100000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4689/25000 : ℝ)) (X := (69957184140295887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000157855361255489/5000000000000000000 : ℝ) ≤ (5000036364887773/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (5000157855361255489/5000000000000000000 : ℝ)^1024 ≤ (5000036364887773/5000000000000000 : ℝ)^4445 := by
      have hnat : (5000157855361255489 : ℕ)^1024*5000000000000000^4445 ≤ 5000036364887773^4445*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000157855361255489 5000000000000000000 5000036364887773 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000036364887773/5000000000000000 : ℝ)) (X := (5000157855361255489/5000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100071535737752850777/100000000000000000000 : ℝ) ≤ (5000823761968533/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (100071535737752850777/100000000000000000000 : ℝ)^1024 ≤ (5000823761968533/5000000000000000 : ℝ)^4445 := by
      have hnat : (100071535737752850777 : ℕ)^1024*5000000000000000^4445 ≤ 5000823761968533^4445*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100071535737752850777 100000000000000000000 5000823761968533 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000823761968533/5000000000000000 : ℝ)) (X := (100071535737752850777/100000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50069957184140295887/50000000000000000000 : ℝ) ≤ (5001611159049293/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (50069957184140295887/50000000000000000000 : ℝ)^1024 ≤ (5001611159049293/5000000000000000 : ℝ)^4445 := by
      have hnat : (50069957184140295887 : ℕ)^1024*5000000000000000^4445 ≤ 5001611159049293^4445*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069957184140295887 50000000000000000000 5001611159049293 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001611159049293/5000000000000000 : ℝ)) (X := (50069957184140295887/50000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(157855361255489/10000000000000000000 : ℝ) ≤ ((10922613014664011381/10925000000000000000 : ℝ)+2*(19684927019/13656250000000 : ℝ)*(7831/100000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (10922613014664011381/10925000000000000000 : ℝ)+2*(19684927019/13656250000000 : ℝ)*(7831/100000 : ℝ)=(5000036364887773/5000000000000000 : ℝ) by norm_num, show 1+2*(157855361255489/10000000000000000000 : ℝ)=(5000157855361255489/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(69957184140295887/100000000000000000000 : ℝ)+(157855361255489/10000000000000000000 : ℝ) ≤ ((10922613014664011381/10925000000000000000 : ℝ)+(19684927019/13656250000000 : ℝ)*((4689/25000 : ℝ)+(7831/100000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (10922613014664011381/10925000000000000000 : ℝ)+(19684927019/13656250000000 : ℝ)*((4689/25000 : ℝ)+(7831/100000 : ℝ))=(5000823761968533/5000000000000000 : ℝ) by norm_num, show 1+(69957184140295887/100000000000000000000 : ℝ)+(157855361255489/10000000000000000000 : ℝ)=(100071535737752850777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(69957184140295887/100000000000000000000 : ℝ) ≤ ((10922613014664011381/10925000000000000000 : ℝ)+2*(19684927019/13656250000000 : ℝ)*(4689/25000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (10922613014664011381/10925000000000000000 : ℝ)+2*(19684927019/13656250000000 : ℝ)*(4689/25000 : ℝ)=(5001611159049293/5000000000000000 : ℝ) by norm_num, show 1+2*(69957184140295887/100000000000000000000 : ℝ)=(50069957184140295887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10922613014664011381/10925000000000000000 : ℝ)*(X 1 0+X 2 0)+(19684927019/13656250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (7831/100000 : ℝ)) (hi := (4689/25000 : ℝ)) (c := (10922613014664011381/10925000000000000000 : ℝ)) (alpha := (19684927019/13656250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10922613014664011381/10925000000000000000 : ℝ)*(X 0 1+X 2 1)+(19684927019/13656250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (7831/100000 : ℝ)) (hi := (4689/25000 : ℝ)) (c := (10922613014664011381/10925000000000000000 : ℝ)) (alpha := (19684927019/13656250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10922613014664011381/10925000000000000000 : ℝ)*(X 0 2+X 1 2)+(19684927019/13656250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (7831/100000 : ℝ)) (hi := (4689/25000 : ℝ)) (c := (10922613014664011381/10925000000000000000 : ℝ)) (alpha := (19684927019/13656250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-119917467/625000000 : ℝ)*X 0 0+(5470782151/10000000000 : ℝ)*X 0 1+(5186396931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680993763/5000000000 : ℝ)*X 1 0+(-129089439/625000000 : ℝ)*X 1 1+(1296599119/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361987401/10000000000 : ℝ)*X 2 0+(5186396421/10000000000 : ℝ)*X 2 1+(-2065431263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2141915501/5000000000 : ℝ)*X 0 0+(3979853459/10000000000 : ℝ)*X 0 1+(2303972851/5000000000 : ℝ)*X 0 2+(2141915501/5000000000 : ℝ)*X 1 0+(3979853459/10000000000 : ℝ)*X 1 1+(2303972851/5000000000 : ℝ)*X 1 2+(2141915501/5000000000 : ℝ)*X 2 0+(3979853459/10000000000 : ℝ)*X 2 1+(2303972851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1918743051/10000000000 : ℝ)*X 0 0+(259412509/500000000 : ℝ)*X 0 1+(5468911597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287746747/10000000000 : ℝ)*X 1 0+(-445729163/2500000000 : ℝ)*X 1 1+(2734455813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528774699/1000000000 : ℝ)*X 2 0+(5468911657/10000000000 : ℝ)*X 2 1+(-1782916273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2141985751/5000000000 : ℝ)*X 0 0+(4603851989/10000000000 : ℝ)*X 0 1+(3983985781/10000000000 : ℝ)*X 0 2+(2141985751/5000000000 : ℝ)*X 1 0+(4603851989/10000000000 : ℝ)*X 1 1+(3983985781/10000000000 : ℝ)*X 1 2+(2141985751/5000000000 : ℝ)*X 2 0+(4603851989/10000000000 : ℝ)*X 2 1+(3983985781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7353653995201874291082051/1365625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31133751/2000000000000 : ℝ)*(base19) + (720017507/50000000000000 : ℝ)*(base23) + (18594149/100000000000000 : ℝ)*(lower2) + (265986171/100000000000000 : ℝ)*(upper3) + (41758837/100000000000000 : ℝ)*(upper5) + (2554262030707199/100000000000000 : ℝ)*(major0) + (2554262030707199/100000000000000 : ℝ)*(major1) + (199551721149/7812500000 : ℝ)*(major2) + (1758186834748241/50000000000000 : ℝ)*(sp0) + (1758191779044967/50000000000000 : ℝ)*(sp1) + (3516383674742471/100000000000000 : ℝ)*(sp2) + (796064908125157/50000000000000 : ℝ)*(sp3) + (11445281003/100000000000000 : ℝ)*(sp4) + (8950892367/100000000000000 : ℝ)*(sp7) + (796069383571341/50000000000000 : ℝ)*(f.failure) + (703277022955497/20000000000000 : ℝ)*(f.sum) + (56012785383023/10925000000000000000000000000 : ℝ)*base65 + (9623516889462868181/1092500000000000000000000000000000 : ℝ)*base68 + (1311868618035451/341406250000000000000000000000 : ℝ)*base69 + (3078111270049631819/1092500000000000000000000000000000 : ℝ)*base71 + (3968845554877/10925000000000000000000000000 : ℝ)*base74 + (13170715939994929/1365625000000000000000000000000 : ℝ)*base75 + (184092613788562253/47500000000000000000000000000000 : ℝ)*base77 + (364134936943937747/47500000000000000000000000000000 : ℝ)*base80 + (234511575149/237500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (77378351/5000000000000000000000 : ℝ)*base89 + (77378351/5000000000000000000000 : ℝ)*base91 + (27378351/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (314434020102510405453624411/27312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6334457/400000000000 : ℝ)*(base19) + (196478993/10000000000000 : ℝ)*(base23) + (55319491/25000000000000 : ℝ)*(upper3) + (17603747/25000000000000 : ℝ)*(lower4) + (273097629/100000000000000 : ℝ)*(upper5) + (258813239730377/10000000000000 : ℝ)*(major0) + (258813239730377/10000000000000 : ℝ)*(major1) + (258813239730377/10000000000000 : ℝ)*(major2) + (17931936993/100000000000000 : ℝ)*(sp1) + (11967065933/50000000000000 : ℝ)*(sp2) + (890753338136661/25000000000000 : ℝ)*(sp4) + (3562993836995401/100000000000000 : ℝ)*(sp5) + (222686715851553/6250000000000 : ℝ)*(sp6) + (806625529156139/50000000000000 : ℝ)*(sp7) + (806625529156139/50000000000000 : ℝ)*(f.failure) + (890753338136661/25000000000000 : ℝ)*(f.sum) + (1017085901063/273125000000000000000000000 : ℝ)*base66 + (94215572456320637/109250000000000000000000000000000 : ℝ)*base67 + (610308477640679363/109250000000000000000000000000000 : ℝ)*base70 + (624424870614429363/109250000000000000000000000000000 : ℝ)*base72 + (3177879019743/1092500000000000000000000000 : ℝ)*base73 + (56589953831179363/109250000000000000000000000000000 : ℝ)*base76 + (688900715983679363/109250000000000000000000000000000 : ℝ)*base78 + (834967564162179363/109250000000000000000000000000000 : ℝ)*base80 + (1408230984143/273125000000000000000000000 : ℝ)*base82 + (38031929/5000000000000000000000 : ℝ)*base89 + (38031929/5000000000000000000000 : ℝ)*base91 + (38031929/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1475_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1475_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1475_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1475_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1475_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1475_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
