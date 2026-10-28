-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1282_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:39.40034+00:00
-- url     : https://prove2.me/submissions/32bbbc48-0822-4c32-b30f-c02ed499c672

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
theorem support_rectangle_w1282_s6_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096955263/10000000000 : ℝ)*x 0 + (338490077/625000000 : ℝ)*x 1 + (2621267613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096955263/10000000000 : ℝ)^2121 ≤ (6377963234299/50000000000000 : ℝ)^1609 := by
    have hnat : (2096955263 : ℕ)^2121*50000000000000^1609 ≤ 6377963234299^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096955263 10000000000 6377963234299 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338490077/625000000 : ℝ)^2121 ≤ (11139244807437/25000000000000 : ℝ)^1609 := by
    have hnat : (338490077 : ℕ)^2121*25000000000000^1609 ≤ 11139244807437^1609*625000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338490077 625000000 11139244807437 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621267613/5000000000 : ℝ)^2121 ≤ (21343547146349/50000000000000 : ℝ)^1609 := by
    have hnat : (2621267613 : ℕ)^2121*50000000000000^1609 ≤ 21343547146349^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621267613 5000000000 21343547146349 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096955263/10000000000 : ℝ), (338490077/625000000 : ℝ), (2621267613/5000000000 : ℝ)] ![(6377963234299/50000000000000 : ℝ), (11139244807437/25000000000000 : ℝ), (21343547146349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096955263/10000000000 : ℝ)|^2121 ≤ (6377963234299/50000000000000 : ℝ)^1609
        have hw : |(-2096955263/10000000000 : ℝ)|=(2096955263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338490077/625000000 : ℝ)|^2121 ≤ (11139244807437/25000000000000 : ℝ)^1609
        have hw : |(338490077/625000000 : ℝ)|=(338490077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621267613/5000000000 : ℝ)|^2121 ≤ (21343547146349/50000000000000 : ℝ)^1609
        have hw : |(2621267613/5000000000 : ℝ)|=(2621267613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674976229/5000000000 : ℝ)*x 0 + (-437061673/2000000000 : ℝ)*x 1 + (524253497/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674976229/5000000000 : ℝ)^2121 ≤ (43843794453527/100000000000000 : ℝ)^1609 := by
    have hnat : (2674976229 : ℕ)^2121*100000000000000^1609 ≤ 43843794453527^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674976229 5000000000 43843794453527 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437061673/2000000000 : ℝ)^2121 ≤ (1683639248109/12500000000000 : ℝ)^1609 := by
    have hnat : (437061673 : ℕ)^2121*12500000000000^1609 ≤ 1683639248109^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437061673 2000000000 1683639248109 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524253497/1000000000 : ℝ)^2121 ≤ (42687091544931/100000000000000 : ℝ)^1609 := by
    have hnat : (524253497 : ℕ)^2121*100000000000000^1609 ≤ 42687091544931^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524253497 1000000000 42687091544931 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674976229/5000000000 : ℝ), (-437061673/2000000000 : ℝ), (524253497/1000000000 : ℝ)] ![(43843794453527/100000000000000 : ℝ), (1683639248109/12500000000000 : ℝ), (42687091544931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674976229/5000000000 : ℝ)|^2121 ≤ (43843794453527/100000000000000 : ℝ)^1609
        have hw : |(2674976229/5000000000 : ℝ)|=(2674976229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437061673/2000000000 : ℝ)|^2121 ≤ (1683639248109/12500000000000 : ℝ)^1609
        have hw : |(-437061673/2000000000 : ℝ)|=(437061673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524253497/1000000000 : ℝ)|^2121 ≤ (42687091544931/100000000000000 : ℝ)^1609
        have hw : |(524253497/1000000000 : ℝ)|=(524253497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674976371/5000000000 : ℝ)*x 0 + (5242535171/10000000000 : ℝ)*x 1 + (-2185307721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674976371/5000000000 : ℝ)^2121 ≤ (1370118672549/3125000000000 : ℝ)^1609 := by
    have hnat : (2674976371 : ℕ)^2121*3125000000000^1609 ≤ 1370118672549^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674976371 5000000000 1370118672549 3125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242535171/10000000000 : ℝ)^2121 ≤ (42687093702357/100000000000000 : ℝ)^1609 := by
    have hnat : (5242535171 : ℕ)^2121*100000000000000^1609 ≤ 42687093702357^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242535171 10000000000 42687093702357 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185307721/10000000000 : ℝ)^2121 ≤ (6734554376261/50000000000000 : ℝ)^1609 := by
    have hnat : (2185307721 : ℕ)^2121*50000000000000^1609 ≤ 6734554376261^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185307721 10000000000 6734554376261 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674976371/5000000000 : ℝ), (5242535171/10000000000 : ℝ), (-2185307721/10000000000 : ℝ)] ![(1370118672549/3125000000000 : ℝ), (42687093702357/100000000000000 : ℝ), (6734554376261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674976371/5000000000 : ℝ)|^2121 ≤ (1370118672549/3125000000000 : ℝ)^1609
        have hw : |(2674976371/5000000000 : ℝ)|=(2674976371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242535171/10000000000 : ℝ)|^2121 ≤ (42687093702357/100000000000000 : ℝ)^1609
        have hw : |(5242535171/10000000000 : ℝ)|=(5242535171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185307721/10000000000 : ℝ)|^2121 ≤ (6734554376261/50000000000000 : ℝ)^1609
        have hw : |(-2185307721/10000000000 : ℝ)|=(2185307721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2171275259/5000000000 : ℝ)*x 0 + (416861953/1000000000 : ℝ)*x 1 + (4523443279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171275259/5000000000 : ℝ)^2121 ≤ (33302102464111/100000000000000 : ℝ)^1609 := by
    have hnat : (2171275259 : ℕ)^2121*100000000000000^1609 ≤ 33302102464111^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171275259 5000000000 33302102464111 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416861953/1000000000 : ℝ)^2121 ≤ (31555129700149/100000000000000 : ℝ)^1609 := by
    have hnat : (416861953 : ℕ)^2121*100000000000000^1609 ≤ 31555129700149^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416861953 1000000000 31555129700149 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523443279/10000000000 : ℝ)^2121 ≤ (4392845977557/12500000000000 : ℝ)^1609 := by
    have hnat : (4523443279 : ℕ)^2121*12500000000000^1609 ≤ 4392845977557^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523443279 10000000000 4392845977557 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171275259/5000000000 : ℝ), (416861953/1000000000 : ℝ), (4523443279/10000000000 : ℝ)] ![(33302102464111/100000000000000 : ℝ), (31555129700149/100000000000000 : ℝ), (4392845977557/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171275259/5000000000 : ℝ)|^2121 ≤ (33302102464111/100000000000000 : ℝ)^1609
        have hw : |(2171275259/5000000000 : ℝ)|=(2171275259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416861953/1000000000 : ℝ)|^2121 ≤ (31555129700149/100000000000000 : ℝ)^1609
        have hw : |(416861953/1000000000 : ℝ)|=(416861953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523443279/10000000000 : ℝ)|^2121 ≤ (4392845977557/12500000000000 : ℝ)^1609
        have hw : |(4523443279/10000000000 : ℝ)|=(4523443279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096968039/10000000000 : ℝ)*x 0 + (20481067/39062500 : ℝ)*x 1 + (2707610099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096968039/10000000000 : ℝ)^2121 ≤ (2551205783287/20000000000000 : ℝ)^1609 := by
    have hnat : (2096968039 : ℕ)^2121*20000000000000^1609 ≤ 2551205783287^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096968039 10000000000 2551205783287 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20481067/39062500 : ℝ)^2121 ≤ (5336715862861/12500000000000 : ℝ)^1609 := by
    have hnat : (20481067 : ℕ)^2121*12500000000000^1609 ≤ 5336715862861^1609*39062500^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20481067 39062500 5336715862861 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707610099/5000000000 : ℝ)^2121 ≤ (8910048832633/20000000000000 : ℝ)^1609 := by
    have hnat : (2707610099 : ℕ)^2121*20000000000000^1609 ≤ 8910048832633^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707610099 5000000000 8910048832633 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096968039/10000000000 : ℝ), (20481067/39062500 : ℝ), (2707610099/5000000000 : ℝ)] ![(2551205783287/20000000000000 : ℝ), (5336715862861/12500000000000 : ℝ), (8910048832633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096968039/10000000000 : ℝ)|^2121 ≤ (2551205783287/20000000000000 : ℝ)^1609
        have hw : |(-2096968039/10000000000 : ℝ)|=(2096968039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20481067/39062500 : ℝ)|^2121 ≤ (5336715862861/12500000000000 : ℝ)^1609
        have hw : |(20481067/39062500 : ℝ)|=(20481067/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707610099/5000000000 : ℝ)|^2121 ≤ (8910048832633/20000000000000 : ℝ)^1609
        have hw : |(2707610099/5000000000 : ℝ)|=(2707610099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305638347/10000000000 : ℝ)*x 0 + (-503155741/2500000000 : ℝ)*x 1 + (2707610101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305638347/10000000000 : ℝ)^2121 ≤ (43365702903771/100000000000000 : ℝ)^1609 := by
    have hnat : (5305638347 : ℕ)^2121*100000000000000^1609 ≤ 43365702903771^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305638347 10000000000 43365702903771 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503155741/2500000000 : ℝ)^2121 ≤ (12084052875291/100000000000000 : ℝ)^1609 := by
    have hnat : (503155741 : ℕ)^2121*100000000000000^1609 ≤ 12084052875291^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503155741 2500000000 12084052875291 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707610101/5000000000 : ℝ)^2121 ≤ (2784390262909/6250000000000 : ℝ)^1609 := by
    have hnat : (2707610101 : ℕ)^2121*6250000000000^1609 ≤ 2784390262909^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707610101 5000000000 2784390262909 6250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305638347/10000000000 : ℝ), (-503155741/2500000000 : ℝ), (2707610101/5000000000 : ℝ)] ![(43365702903771/100000000000000 : ℝ), (12084052875291/100000000000000 : ℝ), (2784390262909/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305638347/10000000000 : ℝ)|^2121 ≤ (43365702903771/100000000000000 : ℝ)^1609
        have hw : |(5305638347/10000000000 : ℝ)|=(5305638347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-503155741/2500000000 : ℝ)|^2121 ≤ (12084052875291/100000000000000 : ℝ)^1609
        have hw : |(-503155741/2500000000 : ℝ)|=(503155741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707610101/5000000000 : ℝ)|^2121 ≤ (2784390262909/6250000000000 : ℝ)^1609
        have hw : |(2707610101/5000000000 : ℝ)|=(2707610101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652819177/5000000000 : ℝ)*x 0 + (1353805049/2500000000 : ℝ)*x 1 + (-1006311481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652819177/5000000000 : ℝ)^2121 ≤ (43365702979191/100000000000000 : ℝ)^1609 := by
    have hnat : (2652819177 : ℕ)^2121*100000000000000^1609 ≤ 43365702979191^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652819177 5000000000 43365702979191 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353805049/2500000000 : ℝ)^2121 ≤ (1782009765659/4000000000000 : ℝ)^1609 := by
    have hnat : (1353805049 : ℕ)^2121*4000000000000^1609 ≤ 1782009765659^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353805049 2500000000 1782009765659 4000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006311481/5000000000 : ℝ)^2121 ≤ (6042026429731/50000000000000 : ℝ)^1609 := by
    have hnat : (1006311481 : ℕ)^2121*50000000000000^1609 ≤ 6042026429731^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006311481 5000000000 6042026429731 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652819177/5000000000 : ℝ), (1353805049/2500000000 : ℝ), (-1006311481/5000000000 : ℝ)] ![(43365702979191/100000000000000 : ℝ), (1782009765659/4000000000000 : ℝ), (6042026429731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652819177/5000000000 : ℝ)|^2121 ≤ (43365702979191/100000000000000 : ℝ)^1609
        have hw : |(2652819177/5000000000 : ℝ)|=(2652819177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353805049/2500000000 : ℝ)|^2121 ≤ (1782009765659/4000000000000 : ℝ)^1609
        have hw : |(1353805049/2500000000 : ℝ)|=(1353805049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1006311481/5000000000 : ℝ)|^2121 ≤ (6042026429731/50000000000000 : ℝ)^1609
        have hw : |(-1006311481/5000000000 : ℝ)|=(1006311481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s6_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4342577459/10000000000 : ℝ)*x 0 + (1130544563/2500000000 : ℝ)*x 1 + (2084945229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342577459/10000000000 : ℝ)^2121 ≤ (8325593703239/25000000000000 : ℝ)^1609 := by
    have hnat : (4342577459 : ℕ)^2121*25000000000000^1609 ≤ 8325593703239^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342577459 10000000000 8325593703239 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130544563/2500000000 : ℝ)^2121 ≤ (43912266231/125000000000 : ℝ)^1609 := by
    have hnat : (1130544563 : ℕ)^2121*125000000000^1609 ≤ 43912266231^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130544563 2500000000 43912266231 125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084945229/5000000000 : ℝ)^2121 ≤ (31567812184867/100000000000000 : ℝ)^1609 := by
    have hnat : (2084945229 : ℕ)^2121*100000000000000^1609 ≤ 31567812184867^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084945229 5000000000 31567812184867 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342577459/10000000000 : ℝ), (1130544563/2500000000 : ℝ), (2084945229/5000000000 : ℝ)] ![(8325593703239/25000000000000 : ℝ), (43912266231/125000000000 : ℝ), (31567812184867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342577459/10000000000 : ℝ)|^2121 ≤ (8325593703239/25000000000000 : ℝ)^1609
        have hw : |(4342577459/10000000000 : ℝ)|=(4342577459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130544563/2500000000 : ℝ)|^2121 ≤ (43912266231/125000000000 : ℝ)^1609
        have hw : |(1130544563/2500000000 : ℝ)|=(1130544563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084945229/5000000000 : ℝ)|^2121 ≤ (31567812184867/100000000000000 : ℝ)^1609
        have hw : |(2084945229/5000000000 : ℝ)|=(2084945229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11/100 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3667/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2747/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2747/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2747/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2747/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2747/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2747/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2747/25000 : ℝ) ^ (4241/1024 : ℝ) ≤ (10662699879024909/100000000000000000000 : ℝ) := by
    have hpowers : (2747/25000 : ℝ)^4241 ≤ (10662699879024909/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2747 : ℕ)^4241*100000000000000000000^1024 ≤ 10662699879024909^1024*25000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2747 25000 10662699879024909 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2747/25000 : ℝ)) (X := (10662699879024909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (367/2500 : ℝ) ^ (4241/1024 : ℝ) ≤ (353925072582981/1000000000000000000 : ℝ) := by
    have hpowers : (367/2500 : ℝ)^4241 ≤ (353925072582981/1000000000000000000 : ℝ)^1024 := by
      have hnat : (367 : ℕ)^4241*1000000000000000000^1024 ≤ 353925072582981^1024*2500^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        367 2500 353925072582981 1000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (367/2500 : ℝ)) (X := (353925072582981/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010662699879024909/50000000000000000000 : ℝ) ≤ (10000514865440783/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50010662699879024909/50000000000000000000 : ℝ)^1024 ≤ (10000514865440783/10000000000000000 : ℝ)^4241 := by
      have hnat : (50010662699879024909 : ℕ)^1024*10000000000000000^4241 ≤ 10000514865440783^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010662699879024909 50000000000000000000 10000514865440783 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000514865440783/10000000000000000 : ℝ)) (X := (50010662699879024909/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046055207137323009/100000000000000000000 : ℝ) ≤ (1250138977530509/1250000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (100046055207137323009/100000000000000000000 : ℝ)^1024 ≤ (1250138977530509/1250000000000000 : ℝ)^4241 := by
      have hnat : (100046055207137323009 : ℕ)^1024*1250000000000000^4241 ≤ 1250138977530509^4241*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046055207137323009 100000000000000000000 1250138977530509 1250000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250138977530509/1250000000000000 : ℝ)) (X := (100046055207137323009/100000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500353925072582981/500000000000000000 : ℝ) ≤ (10001708775047361/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (500353925072582981/500000000000000000 : ℝ)^1024 ≤ (10001708775047361/10000000000000000 : ℝ)^4241 := by
      have hnat : (500353925072582981 : ℕ)^1024*10000000000000000^4241 ≤ 10001708775047361^4241*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500353925072582981 500000000000000000 10001708775047361 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001708775047361/10000000000000000 : ℝ)) (X := (500353925072582981/500000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10662699879024909/100000000000000000000 : ℝ) ≤ ((709784273162505611/710000000000000000 : ℝ)+2*(45919600253/28400000000000 : ℝ)*(2747/25000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (709784273162505611/710000000000000000 : ℝ)+2*(45919600253/28400000000000 : ℝ)*(2747/25000 : ℝ)=(10000514865440783/10000000000000000 : ℝ) by norm_num, show 1+2*(10662699879024909/100000000000000000000 : ℝ)=(50010662699879024909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(353925072582981/1000000000000000000 : ℝ)+(10662699879024909/100000000000000000000 : ℝ) ≤ ((709784273162505611/710000000000000000 : ℝ)+(45919600253/28400000000000 : ℝ)*((367/2500 : ℝ)+(2747/25000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (709784273162505611/710000000000000000 : ℝ)+(45919600253/28400000000000 : ℝ)*((367/2500 : ℝ)+(2747/25000 : ℝ))=(1250138977530509/1250000000000000 : ℝ) by norm_num, show 1+(353925072582981/1000000000000000000 : ℝ)+(10662699879024909/100000000000000000000 : ℝ)=(100046055207137323009/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(353925072582981/1000000000000000000 : ℝ) ≤ ((709784273162505611/710000000000000000 : ℝ)+2*(45919600253/28400000000000 : ℝ)*(367/2500 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (709784273162505611/710000000000000000 : ℝ)+2*(45919600253/28400000000000 : ℝ)*(367/2500 : ℝ)=(10001708775047361/10000000000000000 : ℝ) by norm_num, show 1+2*(353925072582981/1000000000000000000 : ℝ)=(500353925072582981/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (709784273162505611/710000000000000000 : ℝ)*(X 1 0+X 2 0)+(45919600253/28400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (2747/25000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (709784273162505611/710000000000000000 : ℝ)) (alpha := (45919600253/28400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (709784273162505611/710000000000000000 : ℝ)*(X 0 1+X 2 1)+(45919600253/28400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (2747/25000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (709784273162505611/710000000000000000 : ℝ)) (alpha := (45919600253/28400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (709784273162505611/710000000000000000 : ℝ)*(X 0 2+X 1 2)+(45919600253/28400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (2747/25000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (709784273162505611/710000000000000000 : ℝ)) (alpha := (45919600253/28400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2096955263/10000000000 : ℝ)*X 0 0+(338490077/625000000 : ℝ)*X 0 1+(2621267613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674976229/5000000000 : ℝ)*X 1 0+(-437061673/2000000000 : ℝ)*X 1 1+(524253497/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674976371/5000000000 : ℝ)*X 2 0+(5242535171/10000000000 : ℝ)*X 2 1+(-2185307721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171275259/5000000000 : ℝ)*X 0 0+(416861953/1000000000 : ℝ)*X 0 1+(4523443279/10000000000 : ℝ)*X 0 2+(2171275259/5000000000 : ℝ)*X 1 0+(416861953/1000000000 : ℝ)*X 1 1+(4523443279/10000000000 : ℝ)*X 1 2+(2171275259/5000000000 : ℝ)*X 2 0+(416861953/1000000000 : ℝ)*X 2 1+(4523443279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2096968039/10000000000 : ℝ)*X 0 0+(20481067/39062500 : ℝ)*X 0 1+(2707610099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305638347/10000000000 : ℝ)*X 1 0+(-503155741/2500000000 : ℝ)*X 1 1+(2707610101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652819177/5000000000 : ℝ)*X 2 0+(1353805049/2500000000 : ℝ)*X 2 1+(-1006311481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342577459/10000000000 : ℝ)*X 0 0+(1130544563/2500000000 : ℝ)*X 0 1+(2084945229/5000000000 : ℝ)*X 0 2+(4342577459/10000000000 : ℝ)*X 1 0+(1130544563/2500000000 : ℝ)*X 1 1+(2084945229/5000000000 : ℝ)*X 1 2+(4342577459/10000000000 : ℝ)*X 2 0+(1130544563/2500000000 : ℝ)*X 2 1+(2084945229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43220605799038895576503017/8875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195219961/25000000000000 : ℝ)*(base19) + (43058251/5000000000000 : ℝ)*(base23) + (23103273/12500000000000 : ℝ)*(upper4) + (84852291/100000000000000 : ℝ)*(upper5) + (2147125442097051/50000000000000 : ℝ)*(major0) + (2147125442097051/50000000000000 : ℝ)*(major1) + (2147125442097051/50000000000000 : ℝ)*(major2) + (2885078645688693/50000000000000 : ℝ)*(sp0) + (5770169469616161/100000000000000 : ℝ)*(sp1) + (180318244071243/3125000000000 : ℝ)*(sp2) + (2818307978111257/100000000000000 : ℝ)*(sp3) + (2738006741/10000000000000 : ℝ)*(sp4) + (14420948791/100000000000000 : ℝ)*(sp5) + (358260049/4000000000000 : ℝ)*(sp7) + (1409158467306241/50000000000000 : ℝ)*(f.failure) + (1442546167861199/25000000000000 : ℝ)*(f.sum) + (2948511559873/710000000000000000000000000 : ℝ)*base65 + (187112288980628161/35500000000000000000000000000000 : ℝ)*base67 + (121526557742128161/35500000000000000000000000000000 : ℝ)*base69 + (349891616373628161/35500000000000000000000000000000 : ℝ)*base71 + (2967071927007/710000000000000000000000000 : ℝ)*base74 + (542131284214128161/35500000000000000000000000000000 : ℝ)*base75 + (107596300609871839/35500000000000000000000000000000 : ℝ)*base78 + (927470262228628161/35500000000000000000000000000000 : ℝ)*base79 + (1734216051433/710000000000000000000000000 : ℝ)*base81 + (48255301/5000000000000000000000 : ℝ)*base90 + (48255301/5000000000000000000000 : ℝ)*base92 + (48255301/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201883908706724946477052491/17750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2024003991/100000000000000 : ℝ)*(base19) + (276507329/12500000000000 : ℝ)*(base23) + (14489597/6250000000000 : ℝ)*(upper3) + (4074981/5000000000000 : ℝ)*(lower4) + (234264373/100000000000000 : ℝ)*(upper5) + (2162568686543973/50000000000000 : ℝ)*(major0) + (2162568686543973/50000000000000 : ℝ)*(major1) + (2162568686543973/50000000000000 : ℝ)*(major2) + (8089312279/20000000000000 : ℝ)*(sp1) + (43652308759/100000000000000 : ℝ)*(sp2) + (5811686629207181/100000000000000 : ℝ)*(sp4) + (1162328831728359/20000000000000 : ℝ)*(sp5) + (581164076483979/10000000000000 : ℝ)*(sp6) + (1419293868921997/50000000000000 : ℝ)*(sp7) + (1419293868921997/50000000000000 : ℝ)*(f.failure) + (5811686629207181/100000000000000 : ℝ)*(f.sum) + (2766750237601/710000000000000000000000000 : ℝ)*base66 + (23658921060042497/35500000000000000000000000000000 : ℝ)*base68 + (216951271744957503/35500000000000000000000000000000 : ℝ)*base69 + (246169478194457503/35500000000000000000000000000000 : ℝ)*base71 + (4365830517261/710000000000000000000000000 : ℝ)*base74 + (308286243223957503/35500000000000000000000000000000 : ℝ)*base75 + (198109509542042497/35500000000000000000000000000000 : ℝ)*base78 + (487538341286457503/35500000000000000000000000000000 : ℝ)*base79 + (916247071739/710000000000000000000000000 : ℝ)*base81 + (25449983/5000000000000000000000 : ℝ)*base89 + (25449983/5000000000000000000000 : ℝ)*base91 + (25449983/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1282_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1282_s7_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-524241433/2500000000 : ℝ)*x 0 + (676966507/1250000000 : ℝ)*x 1 + (1048527543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524241433/2500000000 : ℝ)^2121 ≤ (1594501302139/12500000000000 : ℝ)^1609 := by
    have hnat : (524241433 : ℕ)^2121*12500000000000^1609 ≤ 1594501302139^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524241433 2500000000 1594501302139 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676966507/1250000000 : ℝ)^2121 ≤ (44555795206511/100000000000000 : ℝ)^1609 := by
    have hnat : (676966507 : ℕ)^2121*100000000000000^1609 ≤ 44555795206511^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676966507 1250000000 44555795206511 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048527543/2000000000 : ℝ)^2121 ≤ (42688194358001/100000000000000 : ℝ)^1609 := by
    have hnat : (1048527543 : ℕ)^2121*100000000000000^1609 ≤ 42688194358001^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048527543 2000000000 42688194358001 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524241433/2500000000 : ℝ), (676966507/1250000000 : ℝ), (1048527543/2000000000 : ℝ)] ![(1594501302139/12500000000000 : ℝ), (44555795206511/100000000000000 : ℝ), (42688194358001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524241433/2500000000 : ℝ)|^2121 ≤ (1594501302139/12500000000000 : ℝ)^1609
        have hw : |(-524241433/2500000000 : ℝ)|=(524241433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676966507/1250000000 : ℝ)|^2121 ≤ (44555795206511/100000000000000 : ℝ)^1609
        have hw : |(676966507/1250000000 : ℝ)|=(676966507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048527543/2000000000 : ℝ)|^2121 ≤ (42688194358001/100000000000000 : ℝ)^1609
        have hw : |(1048527543/2000000000 : ℝ)|=(1048527543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213997/400000 : ℝ)*x 0 + (-1092604231/5000000000 : ℝ)*x 1 + (1310659557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213997/400000 : ℝ)^2121 ≤ (171263663383/390625000000 : ℝ)^1609 := by
    have hnat : (213997 : ℕ)^2121*390625000000^1609 ≤ 171263663383^1609*400000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213997 400000 171263663383 390625000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092604231/5000000000 : ℝ)^2121 ≤ (13468302302161/100000000000000 : ℝ)^1609 := by
    have hnat : (1092604231 : ℕ)^2121*100000000000000^1609 ≤ 13468302302161^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092604231 5000000000 13468302302161 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310659557/2500000000 : ℝ)^2121 ≤ (21344099932151/50000000000000 : ℝ)^1609 := by
    have hnat : (1310659557 : ℕ)^2121*50000000000000^1609 ≤ 21344099932151^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310659557 2500000000 21344099932151 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213997/400000 : ℝ), (-1092604231/5000000000 : ℝ), (1310659557/2500000000 : ℝ)] ![(171263663383/390625000000 : ℝ), (13468302302161/100000000000000 : ℝ), (21344099932151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213997/400000 : ℝ)|^2121 ≤ (171263663383/390625000000 : ℝ)^1609
        have hw : |(213997/400000 : ℝ)|=(213997/400000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092604231/5000000000 : ℝ)|^2121 ≤ (13468302302161/100000000000000 : ℝ)^1609
        have hw : |(-1092604231/5000000000 : ℝ)|=(1092604231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310659557/2500000000 : ℝ)|^2121 ≤ (21344099932151/50000000000000 : ℝ)^1609
        have hw : |(1310659557/2500000000 : ℝ)|=(1310659557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349925259/10000000000 : ℝ)*x 0 + (5242636571/10000000000 : ℝ)*x 1 + (-2185210307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349925259/10000000000 : ℝ)^2121 ≤ (43843500624011/100000000000000 : ℝ)^1609 := by
    have hnat : (5349925259 : ℕ)^2121*100000000000000^1609 ≤ 43843500624011^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349925259 10000000000 43843500624011 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242636571/10000000000 : ℝ)^2121 ≤ (10672045519711/25000000000000 : ℝ)^1609 := by
    have hnat : (5242636571 : ℕ)^2121*25000000000000^1609 ≤ 10672045519711^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242636571 10000000000 10672045519711 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185210307/10000000000 : ℝ)^2121 ≤ (673415864607/5000000000000 : ℝ)^1609 := by
    have hnat : (2185210307 : ℕ)^2121*5000000000000^1609 ≤ 673415864607^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185210307 10000000000 673415864607 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349925259/10000000000 : ℝ), (5242636571/10000000000 : ℝ), (-2185210307/10000000000 : ℝ)] ![(43843500624011/100000000000000 : ℝ), (10672045519711/25000000000000 : ℝ), (673415864607/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349925259/10000000000 : ℝ)|^2121 ≤ (43843500624011/100000000000000 : ℝ)^1609
        have hw : |(5349925259/10000000000 : ℝ)|=(5349925259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242636571/10000000000 : ℝ)|^2121 ≤ (10672045519711/25000000000000 : ℝ)^1609
        have hw : |(5242636571/10000000000 : ℝ)|=(5242636571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185210307/10000000000 : ℝ)|^2121 ≤ (673415864607/5000000000000 : ℝ)^1609
        have hw : |(-2185210307/10000000000 : ℝ)|=(2185210307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4342556949/10000000000 : ℝ)*x 0 + (1042208827/2500000000 : ℝ)*x 1 + (2261613343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342556949/10000000000 : ℝ)^2121 ≤ (260173183403/781250000000 : ℝ)^1609 := by
    have hnat : (4342556949 : ℕ)^2121*781250000000^1609 ≤ 260173183403^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342556949 10000000000 260173183403 781250000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042208827/2500000000 : ℝ)^2121 ≤ (6311456568829/20000000000000 : ℝ)^1609 := by
    have hnat : (1042208827 : ℕ)^2121*20000000000000^1609 ≤ 6311456568829^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042208827 2500000000 6311456568829 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261613343/5000000000 : ℝ)^2121 ≤ (4392568707763/12500000000000 : ℝ)^1609 := by
    have hnat : (2261613343 : ℕ)^2121*12500000000000^1609 ≤ 4392568707763^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261613343 5000000000 4392568707763 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342556949/10000000000 : ℝ), (1042208827/2500000000 : ℝ), (2261613343/5000000000 : ℝ)] ![(260173183403/781250000000 : ℝ), (6311456568829/20000000000000 : ℝ), (4392568707763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342556949/10000000000 : ℝ)|^2121 ≤ (260173183403/781250000000 : ℝ)^1609
        have hw : |(4342556949/10000000000 : ℝ)|=(4342556949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042208827/2500000000 : ℝ)|^2121 ≤ (6311456568829/20000000000000 : ℝ)^1609
        have hw : |(1042208827/2500000000 : ℝ)|=(1042208827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261613343/5000000000 : ℝ)|^2121 ≤ (4392568707763/12500000000000 : ℝ)^1609
        have hw : |(2261613343/5000000000 : ℝ)|=(2261613343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-104848937/500000000 : ℝ)*x 0 + (5243253793/10000000000 : ℝ)*x 1 + (169222271/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104848937/500000000 : ℝ)^2121 ≤ (12756114725471/100000000000000 : ℝ)^1609 := by
    have hnat : (104848937 : ℕ)^2121*100000000000000^1609 ≤ 12756114725471^1609*500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104848937 500000000 12756114725471 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243253793/10000000000 : ℝ)^2121 ≤ (42694807173143/100000000000000 : ℝ)^1609 := by
    have hnat : (5243253793 : ℕ)^2121*100000000000000^1609 ≤ 42694807173143^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243253793 10000000000 42694807173143 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169222271/312500000 : ℝ)^2121 ≤ (22274539038409/50000000000000 : ℝ)^1609 := by
    have hnat : (169222271 : ℕ)^2121*50000000000000^1609 ≤ 22274539038409^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169222271 312500000 22274539038409 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104848937/500000000 : ℝ), (5243253793/10000000000 : ℝ), (169222271/312500000 : ℝ)] ![(12756114725471/100000000000000 : ℝ), (42694807173143/100000000000000 : ℝ), (22274539038409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104848937/500000000 : ℝ)|^2121 ≤ (12756114725471/100000000000000 : ℝ)^1609
        have hw : |(-104848937/500000000 : ℝ)|=(104848937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243253793/10000000000 : ℝ)|^2121 ≤ (42694807173143/100000000000000 : ℝ)^1609
        have hw : |(5243253793/10000000000 : ℝ)|=(5243253793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169222271/312500000 : ℝ)|^2121 ≤ (22274539038409/50000000000000 : ℝ)^1609
        have hw : |(169222271/312500000 : ℝ)|=(169222271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305665267/10000000000 : ℝ)*x 0 + (-2012733653/10000000000 : ℝ)*x 1 + (169222271/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305665267/10000000000 : ℝ)^2121 ≤ (43365992951037/100000000000000 : ℝ)^1609 := by
    have hnat : (5305665267 : ℕ)^2121*100000000000000^1609 ≤ 43365992951037^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305665267 10000000000 43365992951037 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012733653/10000000000 : ℝ)^2121 ≤ (12084928953911/100000000000000 : ℝ)^1609 := by
    have hnat : (2012733653 : ℕ)^2121*100000000000000^1609 ≤ 12084928953911^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012733653 10000000000 12084928953911 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169222271/312500000 : ℝ)^2121 ≤ (22274539038409/50000000000000 : ℝ)^1609 := by
    have hnat : (169222271 : ℕ)^2121*50000000000000^1609 ≤ 22274539038409^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169222271 312500000 22274539038409 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305665267/10000000000 : ℝ), (-2012733653/10000000000 : ℝ), (169222271/312500000 : ℝ)] ![(43365992951037/100000000000000 : ℝ), (12084928953911/100000000000000 : ℝ), (22274539038409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305665267/10000000000 : ℝ)|^2121 ≤ (43365992951037/100000000000000 : ℝ)^1609
        have hw : |(5305665267/10000000000 : ℝ)|=(5305665267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2012733653/10000000000 : ℝ)|^2121 ≤ (12084928953911/100000000000000 : ℝ)^1609
        have hw : |(-2012733653/10000000000 : ℝ)|=(2012733653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169222271/312500000 : ℝ)|^2121 ≤ (22274539038409/50000000000000 : ℝ)^1609
        have hw : |(169222271/312500000 : ℝ)|=(169222271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305665267/10000000000 : ℝ)*x 0 + (169222271/312500000 : ℝ)*x 1 + (-2012733653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305665267/10000000000 : ℝ)^2121 ≤ (43365992951037/100000000000000 : ℝ)^1609 := by
    have hnat : (5305665267 : ℕ)^2121*100000000000000^1609 ≤ 43365992951037^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305665267 10000000000 43365992951037 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169222271/312500000 : ℝ)^2121 ≤ (22274539038409/50000000000000 : ℝ)^1609 := by
    have hnat : (169222271 : ℕ)^2121*50000000000000^1609 ≤ 22274539038409^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169222271 312500000 22274539038409 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012733653/10000000000 : ℝ)^2121 ≤ (12084928953911/100000000000000 : ℝ)^1609 := by
    have hnat : (2012733653 : ℕ)^2121*100000000000000^1609 ≤ 12084928953911^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012733653 10000000000 12084928953911 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305665267/10000000000 : ℝ), (169222271/312500000 : ℝ), (-2012733653/10000000000 : ℝ)] ![(43365992951037/100000000000000 : ℝ), (22274539038409/50000000000000 : ℝ), (12084928953911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305665267/10000000000 : ℝ)|^2121 ≤ (43365992951037/100000000000000 : ℝ)^1609
        have hw : |(5305665267/10000000000 : ℝ)|=(5305665267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169222271/312500000 : ℝ)|^2121 ≤ (22274539038409/50000000000000 : ℝ)^1609
        have hw : |(169222271/312500000 : ℝ)|=(169222271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2012733653/10000000000 : ℝ)|^2121 ≤ (12084928953911/100000000000000 : ℝ)^1609
        have hw : |(-2012733653/10000000000 : ℝ)|=(2012733653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s7_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4342584873/10000000000 : ℝ)*x 0 + (904392839/2000000000 : ℝ)*x 1 + (2085051299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342584873/10000000000 : ℝ)^2121 ≤ (33302449761803/100000000000000 : ℝ)^1609 := by
    have hnat : (4342584873 : ℕ)^2121*100000000000000^1609 ≤ 33302449761803^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342584873 10000000000 33302449761803 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904392839/2000000000 : ℝ)^2121 ≤ (439095262411/1250000000000 : ℝ)^1609 := by
    have hnat : (904392839 : ℕ)^2121*1250000000000^1609 ≤ 439095262411^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904392839 2000000000 439095262411 1250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085051299/5000000000 : ℝ)^2121 ≤ (31569929232073/100000000000000 : ℝ)^1609 := by
    have hnat : (2085051299 : ℕ)^2121*100000000000000^1609 ≤ 31569929232073^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085051299 5000000000 31569929232073 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342584873/10000000000 : ℝ), (904392839/2000000000 : ℝ), (2085051299/5000000000 : ℝ)] ![(33302449761803/100000000000000 : ℝ), (439095262411/1250000000000 : ℝ), (31569929232073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342584873/10000000000 : ℝ)|^2121 ≤ (33302449761803/100000000000000 : ℝ)^1609
        have hw : |(4342584873/10000000000 : ℝ)|=(4342584873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904392839/2000000000 : ℝ)|^2121 ≤ (439095262411/1250000000000 : ℝ)^1609
        have hw : |(904392839/2000000000 : ℝ)|=(904392839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085051299/5000000000 : ℝ)|^2121 ≤ (31569929232073/100000000000000 : ℝ)^1609
        have hw : |(2085051299/5000000000 : ℝ)|=(2085051299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    (5501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2933/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3667/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3667/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3667/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3667/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3667/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3667/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11/100 : ℝ) ^ (4241/1024 : ℝ) ≤ (1338876318597231/12500000000000000000 : ℝ) := by
    have hpowers : (11/100 : ℝ)^4241 ≤ (1338876318597231/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11 : ℕ)^4241*12500000000000000000^1024 ≤ 1338876318597231^1024*100^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 100 1338876318597231 12500000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/100 : ℝ)) (X := (1338876318597231/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3667/25000 : ℝ) ^ (4241/1024 : ℝ) ≤ (35272839500184347/100000000000000000000 : ℝ) := by
    have hpowers : (3667/25000 : ℝ)^4241 ≤ (35272839500184347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3667 : ℕ)^4241*100000000000000000000^1024 ≤ 35272839500184347^1024*25000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3667 25000 35272839500184347 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3667/25000 : ℝ)) (X := (35272839500184347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251338876318597231/6250000000000000000 : ℝ) ≤ (2500129299502223/2500000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (6251338876318597231/6250000000000000000 : ℝ)^1024 ≤ (2500129299502223/2500000000000000 : ℝ)^4241 := by
      have hnat : (6251338876318597231 : ℕ)^1024*2500000000000000^4241 ≤ 2500129299502223^4241*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251338876318597231 6250000000000000000 2500129299502223 2500000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500129299502223/2500000000000000 : ℝ)) (X := (6251338876318597231/6250000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009196770009792439/20000000000000000000 : ℝ) ≤ (5000555048955311/5000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (20009196770009792439/20000000000000000000 : ℝ)^1024 ≤ (5000555048955311/5000000000000000 : ℝ)^4241 := by
      have hnat : (20009196770009792439 : ℕ)^1024*5000000000000000^4241 ≤ 5000555048955311^4241*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009196770009792439 20000000000000000000 5000555048955311 5000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000555048955311/5000000000000000 : ℝ)) (X := (20009196770009792439/20000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035272839500184347/50000000000000000000 : ℝ) ≤ (78138304670409/78125000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50035272839500184347/50000000000000000000 : ℝ)^1024 ≤ (78138304670409/78125000000000 : ℝ)^4241 := by
      have hnat : (50035272839500184347 : ℕ)^1024*78125000000000^4241 ≤ 78138304670409^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035272839500184347 50000000000000000000 78138304670409 78125000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78138304670409/78125000000000 : ℝ)) (X := (50035272839500184347/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1338876318597231/12500000000000000000 : ℝ) ≤ ((2291803330278659741/2292500000000000000 : ℝ)+2*(59289990173/36680000000000 : ℝ)*(11/100 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (2291803330278659741/2292500000000000000 : ℝ)+2*(59289990173/36680000000000 : ℝ)*(11/100 : ℝ)=(2500129299502223/2500000000000000 : ℝ) by norm_num, show 1+2*(1338876318597231/12500000000000000000 : ℝ)=(6251338876318597231/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35272839500184347/100000000000000000000 : ℝ)+(1338876318597231/12500000000000000000 : ℝ) ≤ ((2291803330278659741/2292500000000000000 : ℝ)+(59289990173/36680000000000 : ℝ)*((3667/25000 : ℝ)+(11/100 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (2291803330278659741/2292500000000000000 : ℝ)+(59289990173/36680000000000 : ℝ)*((3667/25000 : ℝ)+(11/100 : ℝ))=(5000555048955311/5000000000000000 : ℝ) by norm_num, show 1+(35272839500184347/100000000000000000000 : ℝ)+(1338876318597231/12500000000000000000 : ℝ)=(20009196770009792439/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35272839500184347/100000000000000000000 : ℝ) ≤ ((2291803330278659741/2292500000000000000 : ℝ)+2*(59289990173/36680000000000 : ℝ)*(3667/25000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (2291803330278659741/2292500000000000000 : ℝ)+2*(59289990173/36680000000000 : ℝ)*(3667/25000 : ℝ)=(78138304670409/78125000000000 : ℝ) by norm_num, show 1+2*(35272839500184347/100000000000000000000 : ℝ)=(50035272839500184347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2291803330278659741/2292500000000000000 : ℝ)*(X 1 0+X 2 0)+(59289990173/36680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (11/100 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (2291803330278659741/2292500000000000000 : ℝ)) (alpha := (59289990173/36680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2291803330278659741/2292500000000000000 : ℝ)*(X 0 1+X 2 1)+(59289990173/36680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (11/100 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (2291803330278659741/2292500000000000000 : ℝ)) (alpha := (59289990173/36680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2291803330278659741/2292500000000000000 : ℝ)*(X 0 2+X 1 2)+(59289990173/36680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (11/100 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (2291803330278659741/2292500000000000000 : ℝ)) (alpha := (59289990173/36680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-524241433/2500000000 : ℝ)*X 0 0+(676966507/1250000000 : ℝ)*X 0 1+(1048527543/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213997/400000 : ℝ)*X 1 0+(-1092604231/5000000000 : ℝ)*X 1 1+(1310659557/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349925259/10000000000 : ℝ)*X 2 0+(5242636571/10000000000 : ℝ)*X 2 1+(-2185210307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342556949/10000000000 : ℝ)*X 0 0+(1042208827/2500000000 : ℝ)*X 0 1+(2261613343/5000000000 : ℝ)*X 0 2+(4342556949/10000000000 : ℝ)*X 1 0+(1042208827/2500000000 : ℝ)*X 1 1+(2261613343/5000000000 : ℝ)*X 1 2+(4342556949/10000000000 : ℝ)*X 2 0+(1042208827/2500000000 : ℝ)*X 2 1+(2261613343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104848937/500000000 : ℝ)*X 0 0+(5243253793/10000000000 : ℝ)*X 0 1+(169222271/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305665267/10000000000 : ℝ)*X 1 0+(-2012733653/10000000000 : ℝ)*X 1 1+(169222271/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305665267/10000000000 : ℝ)*X 2 0+(169222271/312500000 : ℝ)*X 2 1+(-2012733653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342584873/10000000000 : ℝ)*X 0 0+(904392839/2000000000 : ℝ)*X 0 1+(2085051299/5000000000 : ℝ)*X 0 2+(4342584873/10000000000 : ℝ)*X 1 0+(904392839/2000000000 : ℝ)*X 1 1+(2085051299/5000000000 : ℝ)*X 1 2+(4342584873/10000000000 : ℝ)*X 2 0+(904392839/2000000000 : ℝ)*X 2 1+(2085051299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294030767228579368938449133/28656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215604339/100000000000000 : ℝ)*(base15) + (239742243/100000000000000 : ℝ)*(upper2) + (53309461/100000000000000 : ℝ)*(upper4) + (164939931/100000000000000 : ℝ)*(lower5) + (2149747646699171/50000000000000 : ℝ)*(major0) + (2149747646699171/50000000000000 : ℝ)*(major1) + (2149747646699171/50000000000000 : ℝ)*(major2) + (2888610387224483/50000000000000 : ℝ)*(sp0) + (2888615594350861/50000000000000 : ℝ)*(sp1) + (1155435625394227/20000000000000 : ℝ)*(sp2) + (1410874668240001/50000000000000 : ℝ)*(sp3) + (1328732137/12500000000000 : ℝ)*(sp4) + (26638667463/50000000000000 : ℝ)*(sp6) + (950399009/10000000000000 : ℝ)*(sp7) + (705439710117523/25000000000000 : ℝ)*(f.failure) + (5777231404306061/100000000000000 : ℝ)*(f.sum) + (11644770733189/917000000000000000000000000 : ℝ)*base66 + (158541267578462211/114625000000000000000000000000000 : ℝ)*base67 + (1264769164255037789/114625000000000000000000000000000 : ℝ)*base70 + (1219622053237287789/114625000000000000000000000000000 : ℝ)*base72 + (4627947872549/917000000000000000000000000 : ℝ)*base73 + (2394232953584787789/114625000000000000000000000000000 : ℝ)*base76 + (8467275464662789/114625000000000000000000000000000 : ℝ)*base78 + (234730359791662789/114625000000000000000000000000000 : ℝ)*base80 + (247061099469/91700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (41827297/2500000000000000000000 : ℝ)*base89 + (41827297/2500000000000000000000 : ℝ)*base91 + (41827297/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5035174128404205968836623/1146250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31599357/4000000000000 : ℝ)*(base19) + (856968759/100000000000000 : ℝ)*(base23) + (68047001/25000000000000 : ℝ)*(lower1) + (90010727/100000000000000 : ℝ)*(upper3) + (30373941/100000000000000 : ℝ)*(lower4) + (45351361/50000000000000 : ℝ)*(upper5) + (86607299223699/2000000000000 : ℝ)*(major0) + (86607299223699/2000000000000 : ℝ)*(major1) + (86607299223699/2000000000000 : ℝ)*(major2) + (583593363/50000000000000 : ℝ)*(sp2) + (5818711171936729/100000000000000 : ℝ)*(sp4) + (1163742076390561/20000000000000 : ℝ)*(sp5) + (1454677286945311/25000000000000 : ℝ)*(sp6) + (710504651002153/25000000000000 : ℝ)*(sp7) + (710504651002153/25000000000000 : ℝ)*(f.failure) + (5818711171936729/100000000000000 : ℝ)*(f.sum) + (4384349928097/917000000000000000000000000 : ℝ)*base66 + (41870206481194459/4585000000000000000000000000000 : ℝ)*base67 + (2811538618399459/4585000000000000000000000000000 : ℝ)*base69 + (91541096382595541/4585000000000000000000000000000 : ℝ)*base72 + (7013205823/2292500000000000000000000 : ℝ)*base73 + (83180559013279459/4585000000000000000000000000000 : ℝ)*base75 + (33720919084909459/4585000000000000000000000000000 : ℝ)*base77 + (85444132624249459/4585000000000000000000000000000 : ℝ)*base79 + (3051603121421/917000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9813133/2500000000000000000000 : ℝ)*base90 + (9813133/2500000000000000000000 : ℝ)*base92 + (9813133/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1282_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1282_box_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1924771727/10000000000 : ℝ)*x 0 + (1078485001/2000000000 : ℝ)*x 1 + (5392423307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924771727/10000000000 : ℝ)^2121 ≤ (11393613860641/100000000000000 : ℝ)^1609 := by
    have hnat : (1924771727 : ℕ)^2121*100000000000000^1609 ≤ 11393613860641^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924771727 10000000000 11393613860641 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078485001/2000000000 : ℝ)^2121 ≤ (4430320226157/10000000000000 : ℝ)^1609 := by
    have hnat : (1078485001 : ℕ)^2121*10000000000000^1609 ≤ 4430320226157^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078485001 2000000000 4430320226157 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392423307/10000000000 : ℝ)^2121 ≤ (44303183871927/100000000000000 : ℝ)^1609 := by
    have hnat : (5392423307 : ℕ)^2121*100000000000000^1609 ≤ 44303183871927^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392423307 10000000000 44303183871927 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1924771727/10000000000 : ℝ), (1078485001/2000000000 : ℝ), (5392423307/10000000000 : ℝ)] ![(11393613860641/100000000000000 : ℝ), (4430320226157/10000000000000 : ℝ), (44303183871927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1924771727/10000000000 : ℝ)|^2121 ≤ (11393613860641/100000000000000 : ℝ)^1609
        have hw : |(-1924771727/10000000000 : ℝ)|=(1924771727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078485001/2000000000 : ℝ)|^2121 ≤ (4430320226157/10000000000000 : ℝ)^1609
        have hw : |(1078485001/2000000000 : ℝ)|=(1078485001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392423307/10000000000 : ℝ)|^2121 ≤ (44303183871927/100000000000000 : ℝ)^1609
        have hw : |(5392423307/10000000000 : ℝ)|=(5392423307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284181377/10000000000 : ℝ)*x 0 + (-1036371747/5000000000 : ℝ)*x 1 + (5392424677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284181377/10000000000 : ℝ)^2121 ≤ (43134665672681/100000000000000 : ℝ)^1609 := by
    have hnat : (5284181377 : ℕ)^2121*100000000000000^1609 ≤ 43134665672681^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284181377 10000000000 43134665672681 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036371747/5000000000 : ℝ)^2121 ≤ (6281067796387/50000000000000 : ℝ)^1609 := by
    have hnat : (1036371747 : ℕ)^2121*50000000000000^1609 ≤ 6281067796387^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036371747 5000000000 6281067796387 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392424677/10000000000 : ℝ)^2121 ≤ (44303198709271/100000000000000 : ℝ)^1609 := by
    have hnat : (5392424677 : ℕ)^2121*100000000000000^1609 ≤ 44303198709271^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392424677 10000000000 44303198709271 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284181377/10000000000 : ℝ), (-1036371747/5000000000 : ℝ), (5392424677/10000000000 : ℝ)] ![(43134665672681/100000000000000 : ℝ), (6281067796387/50000000000000 : ℝ), (44303198709271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284181377/10000000000 : ℝ)|^2121 ≤ (43134665672681/100000000000000 : ℝ)^1609
        have hw : |(5284181377/10000000000 : ℝ)|=(5284181377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036371747/5000000000 : ℝ)|^2121 ≤ (6281067796387/50000000000000 : ℝ)^1609
        have hw : |(-1036371747/5000000000 : ℝ)|=(1036371747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392424677/10000000000 : ℝ)|^2121 ≤ (44303198709271/100000000000000 : ℝ)^1609
        have hw : |(5392424677/10000000000 : ℝ)|=(5392424677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41282669/78125000 : ℝ)*x 0 + (5392425069/10000000000 : ℝ)*x 1 + (-103637131/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41282669/78125000 : ℝ)^2121 ≤ (21567334208307/50000000000000 : ℝ)^1609 := by
    have hnat : (41282669 : ℕ)^2121*50000000000000^1609 ≤ 21567334208307^1609*78125000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41282669 78125000 21567334208307 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392425069/10000000000 : ℝ)^2121 ≤ (44303202954701/100000000000000 : ℝ)^1609 := by
    have hnat : (5392425069 : ℕ)^2121*100000000000000^1609 ≤ 44303202954701^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392425069 10000000000 44303202954701 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103637131/500000000 : ℝ)^2121 ≤ (6281064305113/50000000000000 : ℝ)^1609 := by
    have hnat : (103637131 : ℕ)^2121*50000000000000^1609 ≤ 6281064305113^1609*500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103637131 500000000 6281064305113 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41282669/78125000 : ℝ), (5392425069/10000000000 : ℝ), (-103637131/500000000 : ℝ)] ![(21567334208307/50000000000000 : ℝ), (44303202954701/100000000000000 : ℝ), (6281064305113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41282669/78125000 : ℝ)|^2121 ≤ (21567334208307/50000000000000 : ℝ)^1609
        have hw : |(41282669/78125000 : ℝ)|=(41282669/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392425069/10000000000 : ℝ)|^2121 ≤ (44303202954701/100000000000000 : ℝ)^1609
        have hw : |(5392425069/10000000000 : ℝ)|=(5392425069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103637131/500000000 : ℝ)|^2121 ≤ (6281064305113/50000000000000 : ℝ)^1609
        have hw : |(-103637131/500000000 : ℝ)|=(103637131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (898449947/2000000000 : ℝ)*x 0 + (266983897/625000000 : ℝ)*x 1 + (4271744151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898449947/2000000000 : ℝ)^2121 ≤ (6964731823967/20000000000000 : ℝ)^1609 := by
    have hnat : (898449947 : ℕ)^2121*20000000000000^1609 ≤ 6964731823967^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898449947 2000000000 6964731823967 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266983897/625000000 : ℝ)^2121 ≤ (6517632277863/20000000000000 : ℝ)^1609 := by
    have hnat : (266983897 : ℕ)^2121*20000000000000^1609 ≤ 6517632277863^1609*625000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266983897 625000000 6517632277863 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4271744151/10000000000 : ℝ)^2121 ≤ (651763589613/2000000000000 : ℝ)^1609 := by
    have hnat : (4271744151 : ℕ)^2121*2000000000000^1609 ≤ 651763589613^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271744151 10000000000 651763589613 2000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898449947/2000000000 : ℝ), (266983897/625000000 : ℝ), (4271744151/10000000000 : ℝ)] ![(6964731823967/20000000000000 : ℝ), (6517632277863/20000000000000 : ℝ), (651763589613/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898449947/2000000000 : ℝ)|^2121 ≤ (6964731823967/20000000000000 : ℝ)^1609
        have hw : |(898449947/2000000000 : ℝ)|=(898449947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(266983897/625000000 : ℝ)|^2121 ≤ (6517632277863/20000000000000 : ℝ)^1609
        have hw : |(266983897/625000000 : ℝ)|=(266983897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4271744151/10000000000 : ℝ)|^2121 ≤ (651763589613/2000000000000 : ℝ)^1609
        have hw : |(4271744151/10000000000 : ℝ)|=(4271744151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2271929979/10000000000 : ℝ)*x 0 + (1315853877/2500000000 : ℝ)*x 1 + (42107323/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2271929979/10000000000 : ℝ)^2121 ≤ (14177293584113/100000000000000 : ℝ)^1609 := by
    have hnat : (2271929979 : ℕ)^2121*100000000000000^1609 ≤ 14177293584113^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271929979 10000000000 14177293584113 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315853877/2500000000 : ℝ)^2121 ≤ (10727838479733/25000000000000 : ℝ)^1609 := by
    have hnat : (1315853877 : ℕ)^2121*25000000000000^1609 ≤ 10727838479733^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315853877 2500000000 10727838479733 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42107323/80000000 : ℝ)^2121 ≤ (1716454099583/4000000000000 : ℝ)^1609 := by
    have hnat : (42107323 : ℕ)^2121*4000000000000^1609 ≤ 1716454099583^1609*80000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42107323 80000000 1716454099583 4000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2271929979/10000000000 : ℝ), (1315853877/2500000000 : ℝ), (42107323/80000000 : ℝ)] ![(14177293584113/100000000000000 : ℝ), (10727838479733/25000000000000 : ℝ), (1716454099583/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2271929979/10000000000 : ℝ)|^2121 ≤ (14177293584113/100000000000000 : ℝ)^1609
        have hw : |(-2271929979/10000000000 : ℝ)|=(2271929979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315853877/2500000000 : ℝ)|^2121 ≤ (10727838479733/25000000000000 : ℝ)^1609
        have hw : |(1315853877/2500000000 : ℝ)|=(1315853877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42107323/80000000 : ℝ)|^2121 ≤ (1716454099583/4000000000000 : ℝ)^1609
        have hw : |(42107323/80000000 : ℝ)|=(42107323/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5375028059/10000000000 : ℝ)*x 0 + (-1062032503/5000000000 : ℝ)*x 1 + (5263415517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375028059/10000000000 : ℝ)^2121 ≤ (44114887008059/100000000000000 : ℝ)^1609 := by
    have hnat : (5375028059 : ℕ)^2121*100000000000000^1609 ≤ 44114887008059^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375028059 10000000000 44114887008059 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062032503/5000000000 : ℝ)^2121 ≤ (810859935007/6250000000000 : ℝ)^1609 := by
    have hnat : (1062032503 : ℕ)^2121*6250000000000^1609 ≤ 810859935007^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062032503 5000000000 810859935007 6250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263415517/10000000000 : ℝ)^2121 ≤ (5363919251957/12500000000000 : ℝ)^1609 := by
    have hnat : (5263415517 : ℕ)^2121*12500000000000^1609 ≤ 5363919251957^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263415517 10000000000 5363919251957 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375028059/10000000000 : ℝ), (-1062032503/5000000000 : ℝ), (5263415517/10000000000 : ℝ)] ![(44114887008059/100000000000000 : ℝ), (810859935007/6250000000000 : ℝ), (5363919251957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375028059/10000000000 : ℝ)|^2121 ≤ (44114887008059/100000000000000 : ℝ)^1609
        have hw : |(5375028059/10000000000 : ℝ)|=(5375028059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062032503/5000000000 : ℝ)|^2121 ≤ (810859935007/6250000000000 : ℝ)^1609
        have hw : |(-1062032503/5000000000 : ℝ)|=(1062032503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263415517/10000000000 : ℝ)|^2121 ≤ (5363919251957/12500000000000 : ℝ)^1609
        have hw : |(5263415517/10000000000 : ℝ)|=(5263415517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5375027731/10000000000 : ℝ)*x 0 + (657926959/1250000000 : ℝ)*x 1 + (-53101631/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375027731/10000000000 : ℝ)^2121 ≤ (44114883459411/100000000000000 : ℝ)^1609 := by
    have hnat : (5375027731 : ℕ)^2121*100000000000000^1609 ≤ 44114883459411^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375027731 10000000000 44114883459411 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657926959/1250000000 : ℝ)^2121 ≤ (5363919460181/12500000000000 : ℝ)^1609 := by
    have hnat : (657926959 : ℕ)^2121*12500000000000^1609 ≤ 5363919460181^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657926959 1250000000 5363919460181 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53101631/250000000 : ℝ)^2121 ≤ (12973760844189/100000000000000 : ℝ)^1609 := by
    have hnat : (53101631 : ℕ)^2121*100000000000000^1609 ≤ 12973760844189^1609*250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53101631 250000000 12973760844189 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375027731/10000000000 : ℝ), (657926959/1250000000 : ℝ), (-53101631/250000000 : ℝ)] ![(44114883459411/100000000000000 : ℝ), (5363919460181/12500000000000 : ℝ), (12973760844189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375027731/10000000000 : ℝ)|^2121 ≤ (44114883459411/100000000000000 : ℝ)^1609
        have hw : |(5375027731/10000000000 : ℝ)|=(5375027731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657926959/1250000000 : ℝ)|^2121 ≤ (5363919460181/12500000000000 : ℝ)^1609
        have hw : |(657926959/1250000000 : ℝ)|=(657926959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53101631/250000000 : ℝ)|^2121 ≤ (12973760844189/100000000000000 : ℝ)^1609
        have hw : |(-53101631/250000000 : ℝ)|=(53101631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4192033131/10000000000 : ℝ)*x 0 + (2210897943/5000000000 : ℝ)*x 1 + (442179573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192033131/10000000000 : ℝ)^2121 ≤ (6357793851649/20000000000000 : ℝ)^1609 := by
    have hnat : (4192033131 : ℕ)^2121*20000000000000^1609 ≤ 6357793851649^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192033131 10000000000 6357793851649 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210897943/5000000000 : ℝ)^2121 ≤ (34105516159597/100000000000000 : ℝ)^1609 := by
    have hnat : (2210897943 : ℕ)^2121*100000000000000^1609 ≤ 34105516159597^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210897943 5000000000 34105516159597 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442179573/1000000000 : ℝ)^2121 ≤ (852637864337/2500000000000 : ℝ)^1609 := by
    have hnat : (442179573 : ℕ)^2121*2500000000000^1609 ≤ 852637864337^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442179573 1000000000 852637864337 2500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192033131/10000000000 : ℝ), (2210897943/5000000000 : ℝ), (442179573/1000000000 : ℝ)] ![(6357793851649/20000000000000 : ℝ), (34105516159597/100000000000000 : ℝ), (852637864337/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192033131/10000000000 : ℝ)|^2121 ≤ (6357793851649/20000000000000 : ℝ)^1609
        have hw : |(4192033131/10000000000 : ℝ)|=(4192033131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210897943/5000000000 : ℝ)|^2121 ≤ (34105516159597/100000000000000 : ℝ)^1609
        have hw : |(2210897943/5000000000 : ℝ)|=(2210897943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442179573/1000000000 : ℝ)|^2121 ≤ (852637864337/2500000000000 : ℝ)^1609
        have hw : |(442179573/1000000000 : ℝ)|=(442179573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_8 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-43983979/200000000 : ℝ)*x 0 + (1293723989/2500000000 : ℝ)*x 1 + (675808217/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43983979/200000000 : ℝ)^2121 ≤ (6791042862799/50000000000000 : ℝ)^1609 := by
    have hnat : (43983979 : ℕ)^2121*50000000000000^1609 ≤ 6791042862799^1609*200000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43983979 200000000 6791042862799 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293723989/2500000000 : ℝ)^2121 ≤ (4196258541201/10000000000000 : ℝ)^1609 := by
    have hnat : (1293723989 : ℕ)^2121*10000000000000^1609 ≤ 4196258541201^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293723989 2500000000 4196258541201 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675808217/1250000000 : ℝ)^2121 ≤ (22227664424317/50000000000000 : ℝ)^1609 := by
    have hnat : (675808217 : ℕ)^2121*50000000000000^1609 ≤ 22227664424317^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675808217 1250000000 22227664424317 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43983979/200000000 : ℝ), (1293723989/2500000000 : ℝ), (675808217/1250000000 : ℝ)] ![(6791042862799/50000000000000 : ℝ), (4196258541201/10000000000000 : ℝ), (22227664424317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43983979/200000000 : ℝ)|^2121 ≤ (6791042862799/50000000000000 : ℝ)^1609
        have hw : |(-43983979/200000000 : ℝ)|=(43983979/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293723989/2500000000 : ℝ)|^2121 ≤ (4196258541201/10000000000000 : ℝ)^1609
        have hw : |(1293723989/2500000000 : ℝ)|=(1293723989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675808217/1250000000 : ℝ)|^2121 ≤ (22227664424317/50000000000000 : ℝ)^1609
        have hw : |(675808217/1250000000 : ℝ)|=(675808217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_9 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1318571869/2500000000 : ℝ)*x 0 + (-516755293/2500000000 : ℝ)*x 1 + (2703232789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318571869/2500000000 : ℝ)^2121 ≤ (21514116930683/50000000000000 : ℝ)^1609 := by
    have hnat : (1318571869 : ℕ)^2121*50000000000000^1609 ≤ 21514116930683^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318571869 2500000000 21514116930683 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516755293/2500000000 : ℝ)^2121 ≤ (3129109747679/25000000000000 : ℝ)^1609 := by
    have hnat : (516755293 : ℕ)^2121*25000000000000^1609 ≤ 3129109747679^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516755293 2500000000 3129109747679 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703232789/5000000000 : ℝ)^2121 ≤ (44455327136049/100000000000000 : ℝ)^1609 := by
    have hnat : (2703232789 : ℕ)^2121*100000000000000^1609 ≤ 44455327136049^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703232789 5000000000 44455327136049 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318571869/2500000000 : ℝ), (-516755293/2500000000 : ℝ), (2703232789/5000000000 : ℝ)] ![(21514116930683/50000000000000 : ℝ), (3129109747679/25000000000000 : ℝ), (44455327136049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318571869/2500000000 : ℝ)|^2121 ≤ (21514116930683/50000000000000 : ℝ)^1609
        have hw : |(1318571869/2500000000 : ℝ)|=(1318571869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516755293/2500000000 : ℝ)|^2121 ≤ (3129109747679/25000000000000 : ℝ)^1609
        have hw : |(-516755293/2500000000 : ℝ)|=(516755293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703232789/5000000000 : ℝ)|^2121 ≤ (44455327136049/100000000000000 : ℝ)^1609
        have hw : |(2703232789/5000000000 : ℝ)|=(2703232789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_10 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5274287743/10000000000 : ℝ)*x 0 + (168952049/312500000 : ℝ)*x 1 + (-82680833/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274287743/10000000000 : ℝ)^2121 ≤ (43028236732713/100000000000000 : ℝ)^1609 := by
    have hnat : (5274287743 : ℕ)^2121*100000000000000^1609 ≤ 43028236732713^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274287743 10000000000 43028236732713 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168952049/312500000 : ℝ)^2121 ≤ (22227663513829/50000000000000 : ℝ)^1609 := by
    have hnat : (168952049 : ℕ)^2121*50000000000000^1609 ≤ 22227663513829^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168952049 312500000 22227663513829 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82680833/400000000 : ℝ)^2121 ≤ (6258218110453/50000000000000 : ℝ)^1609 := by
    have hnat : (82680833 : ℕ)^2121*50000000000000^1609 ≤ 6258218110453^1609*400000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82680833 400000000 6258218110453 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274287743/10000000000 : ℝ), (168952049/312500000 : ℝ), (-82680833/400000000 : ℝ)] ![(43028236732713/100000000000000 : ℝ), (22227663513829/50000000000000 : ℝ), (6258218110453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274287743/10000000000 : ℝ)|^2121 ≤ (43028236732713/100000000000000 : ℝ)^1609
        have hw : |(5274287743/10000000000 : ℝ)|=(5274287743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168952049/312500000 : ℝ)|^2121 ≤ (22227663513829/50000000000000 : ℝ)^1609
        have hw : |(168952049/312500000 : ℝ)|=(168952049/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82680833/400000000 : ℝ)|^2121 ≤ (6258218110453/50000000000000 : ℝ)^1609
        have hw : |(-82680833/400000000 : ℝ)|=(82680833/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_11 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2262182591/5000000000 : ℝ)*x 0 + (2127698967/5000000000 : ℝ)*x 1 + (106384941/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2262182591/5000000000 : ℝ)^2121 ≤ (35152209532449/100000000000000 : ℝ)^1609 := by
    have hnat : (2262182591 : ℕ)^2121*100000000000000^1609 ≤ 35152209532449^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262182591 5000000000 35152209532449 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127698967/5000000000 : ℝ)^2121 ≤ (32423896706451/100000000000000 : ℝ)^1609 := by
    have hnat : (2127698967 : ℕ)^2121*100000000000000^1609 ≤ 32423896706451^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127698967 5000000000 32423896706451 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106384941/250000000 : ℝ)^2121 ≤ (6484778750699/20000000000000 : ℝ)^1609 := by
    have hnat : (106384941 : ℕ)^2121*20000000000000^1609 ≤ 6484778750699^1609*250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106384941 250000000 6484778750699 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2262182591/5000000000 : ℝ), (2127698967/5000000000 : ℝ), (106384941/250000000 : ℝ)] ![(35152209532449/100000000000000 : ℝ), (32423896706451/100000000000000 : ℝ), (6484778750699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2262182591/5000000000 : ℝ)|^2121 ≤ (35152209532449/100000000000000 : ℝ)^1609
        have hw : |(2262182591/5000000000 : ℝ)|=(2262182591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2127698967/5000000000 : ℝ)|^2121 ≤ (32423896706451/100000000000000 : ℝ)^1609
        have hw : |(2127698967/5000000000 : ℝ)|=(2127698967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106384941/250000000 : ℝ)|^2121 ≤ (6484778750699/20000000000000 : ℝ)^1609
        have hw : |(106384941/250000000 : ℝ)|=(106384941/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_12 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-124872669/625000000 : ℝ)*x 0 + (5478595123/10000000000 : ℝ)*x 1 + (5252402857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124872669/625000000 : ℝ)^2121 ≤ (478726236683/4000000000000 : ℝ)^1609 := by
    have hnat : (124872669 : ℕ)^2121*4000000000000^1609 ≤ 478726236683^1609*625000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124872669 625000000 478726236683 4000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478595123/10000000000 : ℝ)^2121 ≤ (9047760844981/20000000000000 : ℝ)^1609 := by
    have hnat : (5478595123 : ℕ)^2121*20000000000000^1609 ≤ 9047760844981^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478595123 10000000000 9047760844981 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252402857/10000000000 : ℝ)^2121 ≤ (42793039848823/100000000000000 : ℝ)^1609 := by
    have hnat : (5252402857 : ℕ)^2121*100000000000000^1609 ≤ 42793039848823^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252402857 10000000000 42793039848823 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124872669/625000000 : ℝ), (5478595123/10000000000 : ℝ), (5252402857/10000000000 : ℝ)] ![(478726236683/4000000000000 : ℝ), (9047760844981/20000000000000 : ℝ), (42793039848823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124872669/625000000 : ℝ)|^2121 ≤ (478726236683/4000000000000 : ℝ)^1609
        have hw : |(-124872669/625000000 : ℝ)|=(124872669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478595123/10000000000 : ℝ)|^2121 ≤ (9047760844981/20000000000000 : ℝ)^1609
        have hw : |(5478595123/10000000000 : ℝ)|=(5478595123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252402857/10000000000 : ℝ)|^2121 ≤ (42793039848823/100000000000000 : ℝ)^1609
        have hw : |(5252402857/10000000000 : ℝ)|=(5252402857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_13 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (168211877/312500000 : ℝ)*x 0 + (-532084889/2500000000 : ℝ)*x 1 + (5252402633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168211877/312500000 : ℝ)^2121 ≤ (44198775563429/100000000000000 : ℝ)^1609 := by
    have hnat : (168211877 : ℕ)^2121*100000000000000^1609 ≤ 44198775563429^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168211877 312500000 44198775563429 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532084889/2500000000 : ℝ)^2121 ≤ (2601637395559/20000000000000 : ℝ)^1609 := by
    have hnat : (532084889 : ℕ)^2121*20000000000000^1609 ≤ 2601637395559^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532084889 2500000000 2601637395559 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252402633/10000000000 : ℝ)^2121 ≤ (2674564840193/6250000000000 : ℝ)^1609 := by
    have hnat : (5252402633 : ℕ)^2121*6250000000000^1609 ≤ 2674564840193^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252402633 10000000000 2674564840193 6250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168211877/312500000 : ℝ), (-532084889/2500000000 : ℝ), (5252402633/10000000000 : ℝ)] ![(44198775563429/100000000000000 : ℝ), (2601637395559/20000000000000 : ℝ), (2674564840193/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168211877/312500000 : ℝ)|^2121 ≤ (44198775563429/100000000000000 : ℝ)^1609
        have hw : |(168211877/312500000 : ℝ)|=(168211877/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532084889/2500000000 : ℝ)|^2121 ≤ (2601637395559/20000000000000 : ℝ)^1609
        have hw : |(-532084889/2500000000 : ℝ)|=(532084889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252402633/10000000000 : ℝ)|^2121 ≤ (2674564840193/6250000000000 : ℝ)^1609
        have hw : |(5252402633/10000000000 : ℝ)|=(5252402633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_14 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2691389999/5000000000 : ℝ)*x 0 + (2626201431/5000000000 : ℝ)*x 1 + (-1064169669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691389999/5000000000 : ℝ)^2121 ≤ (11049693712261/25000000000000 : ℝ)^1609 := by
    have hnat : (2691389999 : ℕ)^2121*25000000000000^1609 ≤ 11049693712261^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691389999 5000000000 11049693712261 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626201431/5000000000 : ℝ)^2121 ≤ (21396519951261/50000000000000 : ℝ)^1609 := by
    have hnat : (2626201431 : ℕ)^2121*50000000000000^1609 ≤ 21396519951261^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626201431 5000000000 21396519951261 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064169669/5000000000 : ℝ)^2121 ≤ (13008185221421/100000000000000 : ℝ)^1609 := by
    have hnat : (1064169669 : ℕ)^2121*100000000000000^1609 ≤ 13008185221421^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064169669 5000000000 13008185221421 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691389999/5000000000 : ℝ), (2626201431/5000000000 : ℝ), (-1064169669/5000000000 : ℝ)] ![(11049693712261/25000000000000 : ℝ), (21396519951261/50000000000000 : ℝ), (13008185221421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691389999/5000000000 : ℝ)|^2121 ≤ (11049693712261/25000000000000 : ℝ)^1609
        have hw : |(2691389999/5000000000 : ℝ)|=(2691389999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626201431/5000000000 : ℝ)|^2121 ≤ (21396519951261/50000000000000 : ℝ)^1609
        have hw : |(2626201431/5000000000 : ℝ)|=(2626201431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064169669/5000000000 : ℝ)|^2121 ≤ (13008185221421/100000000000000 : ℝ)^1609
        have hw : |(-1064169669/5000000000 : ℝ)|=(1064169669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_box_15 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (130186217/312500000 : ℝ)*x 0 + (2217297577/5000000000 : ℝ)*x 1 + (1108648617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130186217/312500000 : ℝ)^2121 ≤ (31528583917969/100000000000000 : ℝ)^1609 := by
    have hnat : (130186217 : ℕ)^2121*100000000000000^1609 ≤ 31528583917969^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130186217 312500000 31528583917969 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217297577/5000000000 : ℝ)^2121 ≤ (8558927881371/25000000000000 : ℝ)^1609 := by
    have hnat : (2217297577 : ℕ)^2121*25000000000000^1609 ≤ 8558927881371^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217297577 5000000000 8558927881371 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108648617/2500000000 : ℝ)^2121 ≤ (34235704544219/100000000000000 : ℝ)^1609 := by
    have hnat : (1108648617 : ℕ)^2121*100000000000000^1609 ≤ 34235704544219^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108648617 2500000000 34235704544219 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130186217/312500000 : ℝ), (2217297577/5000000000 : ℝ), (1108648617/2500000000 : ℝ)] ![(31528583917969/100000000000000 : ℝ), (8558927881371/25000000000000 : ℝ), (34235704544219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130186217/312500000 : ℝ)|^2121 ≤ (31528583917969/100000000000000 : ℝ)^1609
        have hw : |(130186217/312500000 : ℝ)|=(130186217/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217297577/5000000000 : ℝ)|^2121 ≤ (8558927881371/25000000000000 : ℝ)^1609
        have hw : |(2217297577/5000000000 : ℝ)|=(2217297577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108648617/2500000000 : ℝ)|^2121 ≤ (34235704544219/100000000000000 : ℝ)^1609
        have hw : |(1108648617/2500000000 : ℝ)|=(1108648617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62837/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29413/50000 : ℝ) ∧ (19899/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16823/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2933/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2933/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2933/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2933/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2933/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2933/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5501/50000 : ℝ) ^ (4241/1024 : ℝ) ≤ (1339884805167739/12500000000000000000 : ℝ) := by
    have hpowers : (5501/50000 : ℝ)^4241 ≤ (1339884805167739/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5501 : ℕ)^4241*12500000000000000000^1024 ≤ 1339884805167739^1024*50000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5501 50000 1339884805167739 12500000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5501/50000 : ℝ)) (X := (1339884805167739/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2933/20000 : ℝ) ^ (4241/1024 : ℝ) ≤ (35242970577188123/100000000000000000000 : ℝ) := by
    have hpowers : (2933/20000 : ℝ)^4241 ≤ (35242970577188123/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2933 : ℕ)^4241*100000000000000000000^1024 ≤ 35242970577188123^1024*20000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2933 20000 35242970577188123 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2933/20000 : ℝ)) (X := (35242970577188123/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251339884805167739/6250000000000000000 : ℝ) ≤ (10000517587548117/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (6251339884805167739/6250000000000000000 : ℝ)^1024 ≤ (10000517587548117/10000000000000000 : ℝ)^4241 := by
      have hnat : (6251339884805167739 : ℕ)^1024*10000000000000000^4241 ≤ 10000517587548117^4241*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251339884805167739 6250000000000000000 10000517587548117 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000517587548117/10000000000000000 : ℝ)) (X := (6251339884805167739/6250000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009192409803706007/20000000000000000000 : ℝ) ≤ (10001109571702811/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (20009192409803706007/20000000000000000000 : ℝ)^1024 ≤ (10001109571702811/10000000000000000 : ℝ)^4241 := by
      have hnat : (20009192409803706007 : ℕ)^1024*10000000000000000^4241 ≤ 10001109571702811^4241*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009192409803706007 20000000000000000000 10001109571702811 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001109571702811/10000000000000000 : ℝ)) (X := (20009192409803706007/20000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035242970577188123/50000000000000000000 : ℝ) ≤ (2000340311171501/2000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50035242970577188123/50000000000000000000 : ℝ)^1024 ≤ (2000340311171501/2000000000000000 : ℝ)^4241 := by
      have hnat : (50035242970577188123 : ℕ)^1024*2000000000000000^4241 ≤ 2000340311171501^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035242970577188123 50000000000000000000 2000340311171501 2000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000340311171501/2000000000000000 : ℝ)) (X := (50035242970577188123/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1339884805167739/12500000000000000000 : ℝ) ≤ ((7323773980769773159/7326000000000000000 : ℝ)+2*(295992077347/183150000000000 : ℝ)*(5501/50000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (7323773980769773159/7326000000000000000 : ℝ)+2*(295992077347/183150000000000 : ℝ)*(5501/50000 : ℝ)=(10000517587548117/10000000000000000 : ℝ) by norm_num, show 1+2*(1339884805167739/12500000000000000000 : ℝ)=(6251339884805167739/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35242970577188123/100000000000000000000 : ℝ)+(1339884805167739/12500000000000000000 : ℝ) ≤ ((7323773980769773159/7326000000000000000 : ℝ)+(295992077347/183150000000000 : ℝ)*((2933/20000 : ℝ)+(5501/50000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (7323773980769773159/7326000000000000000 : ℝ)+(295992077347/183150000000000 : ℝ)*((2933/20000 : ℝ)+(5501/50000 : ℝ))=(10001109571702811/10000000000000000 : ℝ) by norm_num, show 1+(35242970577188123/100000000000000000000 : ℝ)+(1339884805167739/12500000000000000000 : ℝ)=(20009192409803706007/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35242970577188123/100000000000000000000 : ℝ) ≤ ((7323773980769773159/7326000000000000000 : ℝ)+2*(295992077347/183150000000000 : ℝ)*(2933/20000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (7323773980769773159/7326000000000000000 : ℝ)+2*(295992077347/183150000000000 : ℝ)*(2933/20000 : ℝ)=(2000340311171501/2000000000000000 : ℝ) by norm_num, show 1+2*(35242970577188123/100000000000000000000 : ℝ)=(50035242970577188123/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7323773980769773159/7326000000000000000 : ℝ)*(X 1 0+X 2 0)+(295992077347/183150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (2933/20000 : ℝ)) (c := (7323773980769773159/7326000000000000000 : ℝ)) (alpha := (295992077347/183150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7323773980769773159/7326000000000000000 : ℝ)*(X 0 1+X 2 1)+(295992077347/183150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (2933/20000 : ℝ)) (c := (7323773980769773159/7326000000000000000 : ℝ)) (alpha := (295992077347/183150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7323773980769773159/7326000000000000000 : ℝ)*(X 0 2+X 1 2)+(295992077347/183150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (2933/20000 : ℝ)) (c := (7323773980769773159/7326000000000000000 : ℝ)) (alpha := (295992077347/183150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1924771727/10000000000 : ℝ)*X 0 0+(1078485001/2000000000 : ℝ)*X 0 1+(5392423307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284181377/10000000000 : ℝ)*X 1 0+(-1036371747/5000000000 : ℝ)*X 1 1+(5392424677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41282669/78125000 : ℝ)*X 2 0+(5392425069/10000000000 : ℝ)*X 2 1+(-103637131/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((898449947/2000000000 : ℝ)*X 0 0+(266983897/625000000 : ℝ)*X 0 1+(4271744151/10000000000 : ℝ)*X 0 2+(898449947/2000000000 : ℝ)*X 1 0+(266983897/625000000 : ℝ)*X 1 1+(4271744151/10000000000 : ℝ)*X 1 2+(898449947/2000000000 : ℝ)*X 2 0+(266983897/625000000 : ℝ)*X 2 1+(4271744151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2271929979/10000000000 : ℝ)*X 0 0+(1315853877/2500000000 : ℝ)*X 0 1+(42107323/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5375028059/10000000000 : ℝ)*X 1 0+(-1062032503/5000000000 : ℝ)*X 1 1+(5263415517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375027731/10000000000 : ℝ)*X 2 0+(657926959/1250000000 : ℝ)*X 2 1+(-53101631/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4192033131/10000000000 : ℝ)*X 0 0+(2210897943/5000000000 : ℝ)*X 0 1+(442179573/1000000000 : ℝ)*X 0 2+(4192033131/10000000000 : ℝ)*X 1 0+(2210897943/5000000000 : ℝ)*X 1 1+(442179573/1000000000 : ℝ)*X 1 2+(4192033131/10000000000 : ℝ)*X 2 0+(2210897943/5000000000 : ℝ)*X 2 1+(442179573/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-43983979/200000000 : ℝ)*X 0 0+(1293723989/2500000000 : ℝ)*X 0 1+(675808217/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1318571869/2500000000 : ℝ)*X 1 0+(-516755293/2500000000 : ℝ)*X 1 1+(2703232789/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274287743/10000000000 : ℝ)*X 2 0+(168952049/312500000 : ℝ)*X 2 1+(-82680833/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2262182591/5000000000 : ℝ)*X 0 0+(2127698967/5000000000 : ℝ)*X 0 1+(106384941/250000000 : ℝ)*X 0 2+(2262182591/5000000000 : ℝ)*X 1 0+(2127698967/5000000000 : ℝ)*X 1 1+(106384941/250000000 : ℝ)*X 1 2+(2262182591/5000000000 : ℝ)*X 2 0+(2127698967/5000000000 : ℝ)*X 2 1+(106384941/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-124872669/625000000 : ℝ)*X 0 0+(5478595123/10000000000 : ℝ)*X 0 1+(5252402857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((168211877/312500000 : ℝ)*X 1 0+(-532084889/2500000000 : ℝ)*X 1 1+(5252402633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2691389999/5000000000 : ℝ)*X 2 0+(2626201431/5000000000 : ℝ)*X 2 1+(-1064169669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((130186217/312500000 : ℝ)*X 0 0+(2217297577/5000000000 : ℝ)*X 0 1+(1108648617/2500000000 : ℝ)*X 0 2+(130186217/312500000 : ℝ)*X 1 0+(2217297577/5000000000 : ℝ)*X 1 1+(1108648617/2500000000 : ℝ)*X 1 2+(130186217/312500000 : ℝ)*X 2 0+(2217297577/5000000000 : ℝ)*X 2 1+(1108648617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62837/100000 : ℝ) ≤ (-2557363089011921895693528933353/4070000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3116777/5000000000000 : ℝ)*(upper1) + (9475019/25000000000000 : ℝ)*(upper3) + (153419/125000000000 : ℝ)*(lower4) + (4234201/20000000000000 : ℝ)*(lower5) + (285253609186367/10000000000000 : ℝ)*(major0) + (285253609186367/10000000000000 : ℝ)*(major1) + (285253609186367/10000000000000 : ℝ)*(major2) + (546981191/50000000000000 : ℝ)*(sp3) + (192694875929699/5000000000000 : ℝ)*(sp4) + (963456409603337/25000000000000 : ℝ)*(sp5) + (1926910451669753/50000000000000 : ℝ)*(sp6) + (1872118395814803/100000000000000 : ℝ)*(sp7) + (8985022579/12500000000000 : ℝ)*(sp13) + (38307627237/50000000000000 : ℝ)*(sp14) + (374423897955437/20000000000000 : ℝ)*(f.failure) + (192694875929699/5000000000000 : ℝ)*(f.sum) + (9898283415613/3663000000000000000000000000 : ℝ)*base66 + (13189693649058469/1980000000000000000000000000000 : ℝ)*base67 + (293524761258469/1980000000000000000000000000000 : ℝ)*base69 + (16964733570678469/1980000000000000000000000000000 : ℝ)*base71 + (6166805093/73260000000000000000000000 : ℝ)*base74 + (7340181466698469/1980000000000000000000000000000 : ℝ)*base75 + (10635861653838469/1980000000000000000000000000000 : ℝ)*base77 + (8387004104658469/1980000000000000000000000000000 : ℝ)*base79 + (4225317547433/457875000000000000000000000 : ℝ)*base82 + (12853857/2000000000000000000000 : ℝ)*base90 + (12853857/2000000000000000000000 : ℝ)*base92 + (12853857/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29413/50000 : ℝ) ≤ (71829571797854110613929282462067/122100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70644407/12500000000000 : ℝ)*(lower1) + (77867471/20000000000000 : ℝ)*(lower2) + (8710583/20000000000000 : ℝ)*(lower5) + (2919265413270329/100000000000000 : ℝ)*(major0) + (2919265413270329/100000000000000 : ℝ)*(major1) + (2919265413270329/100000000000000 : ℝ)*(major2) + (1951496946170441/50000000000000 : ℝ)*(sp0) + (3902972209041757/100000000000000 : ℝ)*(sp1) + (1951489659657601/50000000000000 : ℝ)*(sp2) + (1915912374653567/100000000000000 : ℝ)*(sp3) + (14034933131/50000000000000 : ℝ)*(sp6) + (392498829/25000000000000 : ℝ)*(sp7) + (13496840581/100000000000000 : ℝ)*(sp8) + (35180139707/100000000000000 : ℝ)*(sp9) + (1915913944648883/100000000000000 : ℝ)*(f.failure) + (487875923647683/12500000000000 : ℝ)*(f.sum) + (11036943855571/18315000000000000000000000000 : ℝ)*base65 + (120352267873681603/19800000000000000000000000000000 : ℝ)*base67 + (99821206709881603/19800000000000000000000000000000 : ℝ)*base69 + (89251345484881603/19800000000000000000000000000000 : ℝ)*base71 + (11159926037261/4578750000000000000000000000 : ℝ)*base74 + (64573766558881603/19800000000000000000000000000000 : ℝ)*base75 + (29397682637881603/19800000000000000000000000000000 : ℝ)*base77 + (39997687184881603/19800000000000000000000000000000 : ℝ)*base79 + (11731516892429/18315000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (10201663/10000000000000000000000 : ℝ)*base90 + (10201663/10000000000000000000000 : ℝ)*base92 + (10201663/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (19899/25000 : ℝ) ≤ (1619820167081657418457734633/2035000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69039933/100000000000000 : ℝ)*(lower2) + (62917321/50000000000000 : ℝ)*(lower3) + (107682369/100000000000000 : ℝ)*(upper4) + (73885417/100000000000000 : ℝ)*(lower5) + (3233528094440151/100000000000000 : ℝ)*(major0) + (3233528094440151/100000000000000 : ℝ)*(major1) + (3233528094440151/100000000000000 : ℝ)*(major2) + (41026264013/100000000000000 : ℝ)*(sp1) + (103107179419/100000000000000 : ℝ)*(sp2) + (62452181967/100000000000000 : ℝ)*(sp3) + (431835895990567/10000000000000 : ℝ)*(sp8) + (4318317933641657/100000000000000 : ℝ)*(sp9) + (1079563963181563/25000000000000 : ℝ)*(sp10) + (2122102095923181/100000000000000 : ℝ)*(sp11) + (530541137026287/25000000000000 : ℝ)*(f.failure) + (431835895990567/10000000000000 : ℝ)*(f.sum) + (7028385110679/2035000000000000000000000000 : ℝ)*base66 + (2570051061611973/2200000000000000000000000000000 : ℝ)*base67 + (6948240180188027/2200000000000000000000000000000 : ℝ)*base70 + (26938700065211973/2200000000000000000000000000000 : ℝ)*base71 + (4750317514777/1017500000000000000000000000 : ℝ)*base74 + (8609041280411973/2200000000000000000000000000000 : ℝ)*base75 + (19919732238988027/2200000000000000000000000000000 : ℝ)*base78 + (9397235097788027/2200000000000000000000000000000 : ℝ)*base80 + (7247717849671/2035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (814293/2500000000000000000000 : ℝ)*base89 + (814293/2500000000000000000000 : ℝ)*base91 + (814293/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16823/20000 : ℝ) ≤ (-855844647637478852151343111/1017500000000000000000000000 : ℝ) := by norm_num
    linear_combination (97857813/100000000000000 : ℝ)*(lower0) + (20419749/25000000000000 : ℝ)*(lower2) + (14086793/100000000000000 : ℝ)*(upper3) + (408664851667609/12500000000000 : ℝ)*(major0) + (408664851667609/12500000000000 : ℝ)*(major1) + (408664851667609/12500000000000 : ℝ)*(major2) + (4834779861/50000000000000 : ℝ)*(sp0) + (225655039437/100000000000000 : ℝ)*(sp5) + (8264700361/10000000000000 : ℝ)*(sp6) + (8415382949/20000000000000 : ℝ)*(sp7) + (2210505729117681/50000000000000 : ℝ)*(sp12) + (4420795472755647/100000000000000 : ℝ)*(sp13) + (2210469240395737/50000000000000 : ℝ)*(sp14) + (214561192066601/10000000000000 : ℝ)*(sp15) + (429130799516151/20000000000000 : ℝ)*(f.failure) + (1105255281948771/25000000000000 : ℝ)*(f.sum) + (30465877678127/18315000000000000000000000000 : ℝ)*base66 + (1761871809888563/2475000000000000000000000000000 : ℝ)*base67 + (3852755096688563/2475000000000000000000000000000 : ℝ)*base69 + (299683103111437/2475000000000000000000000000000 : ℝ)*base72 + (41021464870967/1144687500000000000000000000 : ℝ)*base74 + (13800659068511437/2475000000000000000000000000000 : ℝ)*base76 + (2333295986336437/2475000000000000000000000000000 : ℝ)*base78 + (51053015539188563/2475000000000000000000000000000 : ℝ)*base79 + (37822290105001/9157500000000000000000000000 : ℝ)*base82 + (7694189/2000000000000000000000 : ℝ)*base89 + (7694189/2000000000000000000000 : ℝ)*base91 + (7694189/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1282_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29413/50000 : ℝ) else (19899/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16823/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1282_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1282_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29413/50000 : ℝ) else (19899/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16823/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1282_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1282_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1282_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29413/50000 : ℝ) else (19899/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16823/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1282_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
