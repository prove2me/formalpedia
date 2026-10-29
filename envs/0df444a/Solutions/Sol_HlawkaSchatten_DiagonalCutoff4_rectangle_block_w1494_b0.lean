-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1494_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:48.907757+00:00
-- url     : https://prove2.me/submissions/96a8e4a0-f273-4bfa-864a-79295c9fa3b1

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
theorem support_rectangle_w1494_s0_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53284191/312500000 : ℝ)*x 0 + (5926822717/10000000000 : ℝ)*x 1 + (2423770971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53284191/312500000 : ℝ)^4485 ≤ (5051462020963/50000000000000 : ℝ)^3461 := by
    have hnat : (53284191 : ℕ)^4485*50000000000000^3461 ≤ 5051462020963^3461*312500000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53284191 312500000 5051462020963 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5926822717/10000000000 : ℝ)^4485 ≤ (50769999801379/100000000000000 : ℝ)^3461 := by
    have hnat : (5926822717 : ℕ)^4485*100000000000000^3461 ≤ 50769999801379^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926822717 10000000000 50769999801379 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2423770971/5000000000 : ℝ)^4485 ≤ (19563538068167/50000000000000 : ℝ)^3461 := by
    have hnat : (2423770971 : ℕ)^4485*50000000000000^3461 ≤ 19563538068167^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423770971 5000000000 19563538068167 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53284191/312500000 : ℝ), (5926822717/10000000000 : ℝ), (2423770971/5000000000 : ℝ)] ![(5051462020963/50000000000000 : ℝ), (50769999801379/100000000000000 : ℝ), (19563538068167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53284191/312500000 : ℝ)|^4485 ≤ (5051462020963/50000000000000 : ℝ)^3461
        have hw : |(-53284191/312500000 : ℝ)|=(53284191/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5926822717/10000000000 : ℝ)|^4485 ≤ (50769999801379/100000000000000 : ℝ)^3461
        have hw : |(5926822717/10000000000 : ℝ)|=(5926822717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2423770971/5000000000 : ℝ)|^4485 ≤ (19563538068167/50000000000000 : ℝ)^3461
        have hw : |(2423770971/5000000000 : ℝ)|=(2423770971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (219276291/400000000 : ℝ)*x 0 + (-2257294/9765625 : ℝ)*x 1 + (605942807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219276291/400000000 : ℝ)^4485 ≤ (22943510331589/50000000000000 : ℝ)^3461 := by
    have hnat : (219276291 : ℕ)^4485*50000000000000^3461 ≤ 22943510331589^3461*400000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219276291 400000000 22943510331589 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257294/9765625 : ℝ)^4485 ≤ (14985897812009/100000000000000 : ℝ)^3461 := by
    have hnat : (2257294 : ℕ)^4485*100000000000000^3461 ≤ 14985897812009^3461*9765625^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257294 9765625 14985897812009 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605942807/1250000000 : ℝ)^4485 ≤ (9781770378147/25000000000000 : ℝ)^3461 := by
    have hnat : (605942807 : ℕ)^4485*25000000000000^3461 ≤ 9781770378147^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605942807 1250000000 9781770378147 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219276291/400000000 : ℝ), (-2257294/9765625 : ℝ), (605942807/1250000000 : ℝ)] ![(22943510331589/50000000000000 : ℝ), (14985897812009/100000000000000 : ℝ), (9781770378147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219276291/400000000 : ℝ)|^4485 ≤ (22943510331589/50000000000000 : ℝ)^3461
        have hw : |(219276291/400000000 : ℝ)|=(219276291/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257294/9765625 : ℝ)|^4485 ≤ (14985897812009/100000000000000 : ℝ)^3461
        have hw : |(-2257294/9765625 : ℝ)|=(2257294/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(605942807/1250000000 : ℝ)|^4485 ≤ (9781770378147/25000000000000 : ℝ)^3461
        have hw : |(605942807/1250000000 : ℝ)|=(605942807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1096381391/2000000000 : ℝ)*x 0 + (605942969/1250000000 : ℝ)*x 1 + (-462293571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096381391/2000000000 : ℝ)^4485 ≤ (45887017192063/100000000000000 : ℝ)^3461 := by
    have hnat : (1096381391 : ℕ)^4485*100000000000000^3461 ≤ 45887017192063^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096381391 2000000000 45887017192063 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605942969/1250000000 : ℝ)^4485 ≤ (978177376707/2500000000000 : ℝ)^3461 := by
    have hnat : (605942969 : ℕ)^4485*2500000000000^3461 ≤ 978177376707^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605942969 1250000000 978177376707 2500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462293571/2000000000 : ℝ)^4485 ≤ (14985887721839/100000000000000 : ℝ)^3461 := by
    have hnat : (462293571 : ℕ)^4485*100000000000000^3461 ≤ 14985887721839^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462293571 2000000000 14985887721839 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1096381391/2000000000 : ℝ), (605942969/1250000000 : ℝ), (-462293571/2000000000 : ℝ)] ![(45887017192063/100000000000000 : ℝ), (978177376707/2500000000000 : ℝ), (14985887721839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1096381391/2000000000 : ℝ)|^4485 ≤ (45887017192063/100000000000000 : ℝ)^3461
        have hw : |(1096381391/2000000000 : ℝ)|=(1096381391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605942969/1250000000 : ℝ)|^4485 ≤ (978177376707/2500000000000 : ℝ)^3461
        have hw : |(605942969/1250000000 : ℝ)|=(605942969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-462293571/2000000000 : ℝ)|^4485 ≤ (14985887721839/100000000000000 : ℝ)^3461
        have hw : |(-462293571/2000000000 : ℝ)|=(462293571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2075016337/5000000000 : ℝ)*x 0 + (3091271349/10000000000 : ℝ)*x 1 + (2753809047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075016337/5000000000 : ℝ)^4485 ≤ (3999034040393/12500000000000 : ℝ)^3461 := by
    have hnat : (2075016337 : ℕ)^4485*12500000000000^3461 ≤ 3999034040393^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075016337 5000000000 3999034040393 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091271349/10000000000 : ℝ)^4485 ≤ (21841622424491/100000000000000 : ℝ)^3461 := by
    have hnat : (3091271349 : ℕ)^4485*100000000000000^3461 ≤ 21841622424491^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091271349 10000000000 21841622424491 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753809047/5000000000 : ℝ)^4485 ≤ (9233221046593/20000000000000 : ℝ)^3461 := by
    have hnat : (2753809047 : ℕ)^4485*20000000000000^3461 ≤ 9233221046593^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753809047 5000000000 9233221046593 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2075016337/5000000000 : ℝ), (3091271349/10000000000 : ℝ), (2753809047/5000000000 : ℝ)] ![(3999034040393/12500000000000 : ℝ), (21841622424491/100000000000000 : ℝ), (9233221046593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2075016337/5000000000 : ℝ)|^4485 ≤ (3999034040393/12500000000000 : ℝ)^3461
        have hw : |(2075016337/5000000000 : ℝ)|=(2075016337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091271349/10000000000 : ℝ)|^4485 ≤ (21841622424491/100000000000000 : ℝ)^3461
        have hw : |(3091271349/10000000000 : ℝ)|=(3091271349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2753809047/5000000000 : ℝ)|^4485 ≤ (9233221046593/20000000000000 : ℝ)^3461
        have hw : |(2753809047/5000000000 : ℝ)|=(2753809047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-170876969/1000000000 : ℝ)*x 0 + (487516429/1000000000 : ℝ)*x 1 + (2949104871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170876969/1000000000 : ℝ)^4485 ≤ (2532788717647/25000000000000 : ℝ)^3461 := by
    have hnat : (170876969 : ℕ)^4485*25000000000000^3461 ≤ 2532788717647^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170876969 1000000000 2532788717647 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487516429/1000000000 : ℝ)^4485 ≤ (39416239129497/100000000000000 : ℝ)^3461 := by
    have hnat : (487516429 : ℕ)^4485*100000000000000^3461 ≤ 39416239129497^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487516429 1000000000 39416239129497 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949104871/5000000000 : ℝ)^4485 ≤ (12613151496601/25000000000000 : ℝ)^3461 := by
    have hnat : (2949104871 : ℕ)^4485*25000000000000^3461 ≤ 12613151496601^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949104871 5000000000 12613151496601 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170876969/1000000000 : ℝ), (487516429/1000000000 : ℝ), (2949104871/5000000000 : ℝ)] ![(2532788717647/25000000000000 : ℝ), (39416239129497/100000000000000 : ℝ), (12613151496601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170876969/1000000000 : ℝ)|^4485 ≤ (2532788717647/25000000000000 : ℝ)^3461
        have hw : |(-170876969/1000000000 : ℝ)|=(170876969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487516429/1000000000 : ℝ)|^4485 ≤ (39416239129497/100000000000000 : ℝ)^3461
        have hw : |(487516429/1000000000 : ℝ)|=(487516429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949104871/5000000000 : ℝ)|^4485 ≤ (12613151496601/25000000000000 : ℝ)^3461
        have hw : |(2949104871/5000000000 : ℝ)|=(2949104871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187129149/10000000000 : ℝ)*x 0 + (-1260801157/10000000000 : ℝ)*x 1 + (1179641959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187129149/10000000000 : ℝ)^4485 ≤ (42715257694787/100000000000000 : ℝ)^3461 := by
    have hnat : (5187129149 : ℕ)^4485*100000000000000^3461 ≤ 42715257694787^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187129149 10000000000 42715257694787 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1260801157/10000000000 : ℝ)^4485 ≤ (1708033930577/25000000000000 : ℝ)^3461 := by
    have hnat : (1260801157 : ℕ)^4485*25000000000000^3461 ≤ 1708033930577^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260801157 10000000000 1708033930577 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1179641959/2000000000 : ℝ)^4485 ≤ (25226303286947/50000000000000 : ℝ)^3461 := by
    have hnat : (1179641959 : ℕ)^4485*50000000000000^3461 ≤ 25226303286947^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179641959 2000000000 25226303286947 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187129149/10000000000 : ℝ), (-1260801157/10000000000 : ℝ), (1179641959/2000000000 : ℝ)] ![(42715257694787/100000000000000 : ℝ), (1708033930577/25000000000000 : ℝ), (25226303286947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187129149/10000000000 : ℝ)|^4485 ≤ (42715257694787/100000000000000 : ℝ)^3461
        have hw : |(5187129149/10000000000 : ℝ)|=(5187129149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1260801157/10000000000 : ℝ)|^4485 ≤ (1708033930577/25000000000000 : ℝ)^3461
        have hw : |(-1260801157/10000000000 : ℝ)|=(1260801157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1179641959/2000000000 : ℝ)|^4485 ≤ (25226303286947/50000000000000 : ℝ)^3461
        have hw : |(1179641959/2000000000 : ℝ)|=(1179641959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2593564599/5000000000 : ℝ)*x 0 + (2949104843/5000000000 : ℝ)*x 1 + (-1260801253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2593564599/5000000000 : ℝ)^4485 ≤ (533940727721/1250000000000 : ℝ)^3461 := by
    have hnat : (2593564599 : ℕ)^4485*1250000000000^3461 ≤ 533940727721^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593564599 5000000000 533940727721 1250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2949104843/5000000000 : ℝ)^4485 ≤ (50452605365661/100000000000000 : ℝ)^3461 := by
    have hnat : (2949104843 : ℕ)^4485*100000000000000^3461 ≤ 50452605365661^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949104843 5000000000 50452605365661 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260801253/10000000000 : ℝ)^4485 ≤ (1366427279287/20000000000000 : ℝ)^3461 := by
    have hnat : (1260801253 : ℕ)^4485*20000000000000^3461 ≤ 1366427279287^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260801253 10000000000 1366427279287 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2593564599/5000000000 : ℝ), (2949104843/5000000000 : ℝ), (-1260801253/10000000000 : ℝ)] ![(533940727721/1250000000000 : ℝ), (50452605365661/100000000000000 : ℝ), (1366427279287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2593564599/5000000000 : ℝ)|^4485 ≤ (533940727721/1250000000000 : ℝ)^3461
        have hw : |(2593564599/5000000000 : ℝ)|=(2593564599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2949104843/5000000000 : ℝ)|^4485 ≤ (50452605365661/100000000000000 : ℝ)^3461
        have hw : |(2949104843/5000000000 : ℝ)|=(2949104843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1260801253/10000000000 : ℝ)|^4485 ≤ (1366427279287/20000000000000 : ℝ)^3461
        have hw : |(-1260801253/10000000000 : ℝ)|=(1260801253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s0_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166330649/400000000 : ℝ)*x 0 + (1361444787/2500000000 : ℝ)*x 1 + (31553303/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166330649/400000000 : ℝ)^4485 ≤ (32074547530627/100000000000000 : ℝ)^3461 := by
    have hnat : (166330649 : ℕ)^4485*100000000000000^3461 ≤ 32074547530627^3461*400000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166330649 400000000 32074547530627 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361444787/2500000000 : ℝ)^4485 ≤ (22747756534133/50000000000000 : ℝ)^3461 := by
    have hnat : (1361444787 : ℕ)^4485*50000000000000^3461 ≤ 22747756534133^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361444787 2500000000 22747756534133 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31553303/100000000 : ℝ)^4485 ≤ (4485987874849/20000000000000 : ℝ)^3461 := by
    have hnat : (31553303 : ℕ)^4485*20000000000000^3461 ≤ 4485987874849^3461*100000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31553303 100000000 4485987874849 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166330649/400000000 : ℝ), (1361444787/2500000000 : ℝ), (31553303/100000000 : ℝ)] ![(32074547530627/100000000000000 : ℝ), (22747756534133/50000000000000 : ℝ), (4485987874849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166330649/400000000 : ℝ)|^4485 ≤ (32074547530627/100000000000000 : ℝ)^3461
        have hw : |(166330649/400000000 : ℝ)|=(166330649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361444787/2500000000 : ℝ)|^4485 ≤ (22747756534133/50000000000000 : ℝ)^3461
        have hw : |(1361444787/2500000000 : ℝ)|=(1361444787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31553303/100000000 : ℝ)|^4485 ≤ (4485987874849/20000000000000 : ℝ)^3461
        have hw : |(31553303/100000000 : ℝ)|=(31553303/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25719/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4483/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4483 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4483*1^1024 ≤ 0^1024*1^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4483/1024 : ℝ) ≤ (90535025140727897/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4483 ≤ (90535025140727897/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4483*5000000000000000000^1024 ≤ 90535025140727897^1024*5^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 90535025140727897 5000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (90535025140727897/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4483 := by
      have hnat : (1 : ℕ)^1024*1^4483 ≤ 1^4483*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5090535025140727897/5000000000000000000 : ℝ) ≤ (10041073875764969/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (5090535025140727897/5000000000000000000 : ℝ)^1024 ≤ (10041073875764969/10000000000000000 : ℝ)^4483 := by
      have hnat : (5090535025140727897 : ℕ)^1024*10000000000000000^4483 ≤ 10041073875764969^4483*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5090535025140727897 5000000000000000000 10041073875764969 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041073875764969/10000000000000000 : ℝ)) (X := (5090535025140727897/5000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2590535025140727897/2500000000000000000 : ℝ) ≤ (5041073875764969/5000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (2590535025140727897/2500000000000000000 : ℝ)^1024 ≤ (5041073875764969/5000000000000000 : ℝ)^4483 := by
      have hnat : (2590535025140727897 : ℕ)^1024*5000000000000000^4483 ≤ 5041073875764969^4483*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2590535025140727897 2500000000000000000 5041073875764969 5000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041073875764969/5000000000000000 : ℝ)) (X := (2590535025140727897/2500000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(41073875764969/4000000000000000 : ℝ)*(0 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41073875764969/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(90535025140727897/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(41073875764969/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (1 : ℝ)+(41073875764969/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10041073875764969/10000000000000000 : ℝ) by norm_num, show 1+(90535025140727897/5000000000000000000 : ℝ)+(0 : ℝ)=(5090535025140727897/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(90535025140727897/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(41073875764969/4000000000000000 : ℝ)*(2/5 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41073875764969/4000000000000000 : ℝ)*(2/5 : ℝ)=(5041073875764969/5000000000000000 : ℝ) by norm_num, show 1+2*(90535025140727897/5000000000000000000 : ℝ)=(2590535025140727897/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(41073875764969/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41073875764969/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(41073875764969/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41073875764969/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(41073875764969/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41073875764969/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53284191/312500000 : ℝ)*X 0 0+(5926822717/10000000000 : ℝ)*X 0 1+(2423770971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((219276291/400000000 : ℝ)*X 1 0+(-2257294/9765625 : ℝ)*X 1 1+(605942807/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1096381391/2000000000 : ℝ)*X 2 0+(605942969/1250000000 : ℝ)*X 2 1+(-462293571/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2075016337/5000000000 : ℝ)*X 0 0+(3091271349/10000000000 : ℝ)*X 0 1+(2753809047/5000000000 : ℝ)*X 0 2+(2075016337/5000000000 : ℝ)*X 1 0+(3091271349/10000000000 : ℝ)*X 1 1+(2753809047/5000000000 : ℝ)*X 1 2+(2075016337/5000000000 : ℝ)*X 2 0+(3091271349/10000000000 : ℝ)*X 2 1+(2753809047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-170876969/1000000000 : ℝ)*X 0 0+(487516429/1000000000 : ℝ)*X 0 1+(2949104871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5187129149/10000000000 : ℝ)*X 1 0+(-1260801157/10000000000 : ℝ)*X 1 1+(1179641959/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2593564599/5000000000 : ℝ)*X 2 0+(2949104843/5000000000 : ℝ)*X 2 1+(-1260801253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((166330649/400000000 : ℝ)*X 0 0+(1361444787/2500000000 : ℝ)*X 0 1+(31553303/100000000 : ℝ)*X 0 2+(166330649/400000000 : ℝ)*X 1 0+(1361444787/2500000000 : ℝ)*X 1 1+(31553303/100000000 : ℝ)*X 1 2+(166330649/400000000 : ℝ)*X 2 0+(1361444787/2500000000 : ℝ)*X 2 1+(31553303/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8247532413089118630891/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4022993/500000000000 : ℝ)*(base19) + (109177713/25000000000000 : ℝ)*(base23) + (7098147/6250000000000 : ℝ)*(upper3) + (86011559/50000000000000 : ℝ)*(upper4) + (78101471/50000000000000 : ℝ)*(upper5) + (167549731724687/25000000000000 : ℝ)*(major0) + (167549731724687/25000000000000 : ℝ)*(major1) + (167549731724687/25000000000000 : ℝ)*(major2) + (926545062848427/100000000000000 : ℝ)*(sp0) + (926547576332357/100000000000000 : ℝ)*(sp1) + (185309588844021/20000000000000 : ℝ)*(sp2) + (51731086500197/12500000000000 : ℝ)*(sp3) + (331808253/10000000000000 : ℝ)*(sp4) + (387683303/50000000000000 : ℝ)*(sp7) + (206924733684091/50000000000000 : ℝ)*(f.failure) + (926548380930957/100000000000000 : ℝ)*(f.sum) + (304874589703/50000000000000000000000000000 : ℝ)*base65 + (102765069989703/100000000000000000000000000000 : ℝ)*base67 + (86151216710297/100000000000000000000000000000 : ℝ)*base70 + (144857547810297/100000000000000000000000000000 : ℝ)*base72 + (119733191089703/50000000000000000000000000000 : ℝ)*base73 + (310832846510297/100000000000000000000000000000 : ℝ)*base76 + (144270857810297/100000000000000000000000000000 : ℝ)*base78 + (207771340110297/100000000000000000000000000000 : ℝ)*base80 + (37887168639703/50000000000000000000000000000 : ℝ)*base81 + (18636031/2500000000000000000000 : ℝ)*base89 + (18636031/2500000000000000000000 : ℝ)*base91 + (18636031/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99704739687739572266277/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (882475603/100000000000000 : ℝ)*(base19) + (35869233/4000000000000 : ℝ)*(base23) + (4330251/5000000000000 : ℝ)*(base32) + (133799263/100000000000000 : ℝ)*(upper3) + (41098181/50000000000000 : ℝ)*(upper5) + (176758619016089/25000000000000 : ℝ)*(major0) + (176758619016089/25000000000000 : ℝ)*(major1) + (176758619016089/25000000000000 : ℝ)*(major2) + (1110505271/50000000000000 : ℝ)*(sp1) + (2309376611/100000000000000 : ℝ)*(sp2) + (977473310622417/100000000000000 : ℝ)*(sp4) + (61091887946017/6250000000000 : ℝ)*(sp5) + (977470104514981/100000000000000 : ℝ)*(sp6) + (21829771098081/5000000000000 : ℝ)*(sp7) + (5457443857083/1250000000000 : ℝ)*(f.failure) + (977473310622417/100000000000000 : ℝ)*(f.sum) + (2197805086241/50000000000000000000000000000 : ℝ)*base65 + (121813875413759/100000000000000000000000000000 : ℝ)*base68 + (420997752186241/100000000000000000000000000000 : ℝ)*base69 + (322587985786241/100000000000000000000000000000 : ℝ)*base71 + (132157241613759/50000000000000000000000000000 : ℝ)*base74 + (26420854386241/100000000000000000000000000000 : ℝ)*base75 + (44502069286241/100000000000000000000000000000 : ℝ)*base77 + (112054026213759/100000000000000000000000000000 : ℝ)*base80 + (96321223486241/50000000000000000000000000000 : ℝ)*base81 + (358303/62500000000000000000 : ℝ)*base89 + (358303/62500000000000000000 : ℝ)*base91 + (358303/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1494_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1494_s1_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863667479/10000000000 : ℝ)*x 0 + (5582770663/10000000000 : ℝ)*x 1 + (5089754529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863667479/10000000000 : ℝ)^4485 ≤ (2267376330211/20000000000000 : ℝ)^3461 := by
    have hnat : (1863667479 : ℕ)^4485*20000000000000^3461 ≤ 2267376330211^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863667479 10000000000 2267376330211 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5582770663/10000000000 : ℝ)^4485 ≤ (23492037349109/50000000000000 : ℝ)^3461 := by
    have hnat : (5582770663 : ℕ)^4485*50000000000000^3461 ≤ 23492037349109^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5582770663 10000000000 23492037349109 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5089754529/10000000000 : ℝ)^4485 ≤ (20839521821927/50000000000000 : ℝ)^3461 := by
    have hnat : (5089754529 : ℕ)^4485*50000000000000^3461 ≤ 20839521821927^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089754529 10000000000 20839521821927 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863667479/10000000000 : ℝ), (5582770663/10000000000 : ℝ), (5089754529/10000000000 : ℝ)] ![(2267376330211/20000000000000 : ℝ), (23492037349109/50000000000000 : ℝ), (20839521821927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863667479/10000000000 : ℝ)|^4485 ≤ (2267376330211/20000000000000 : ℝ)^3461
        have hw : |(-1863667479/10000000000 : ℝ)|=(1863667479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5582770663/10000000000 : ℝ)|^4485 ≤ (23492037349109/50000000000000 : ℝ)^3461
        have hw : |(5582770663/10000000000 : ℝ)|=(5582770663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5089754529/10000000000 : ℝ)|^4485 ≤ (20839521821927/50000000000000 : ℝ)^3461
        have hw : |(5089754529/10000000000 : ℝ)|=(5089754529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389935723/10000000000 : ℝ)*x 0 + (-132742007/625000000 : ℝ)*x 1 + (2544876491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389935723/10000000000 : ℝ)^4485 ≤ (22445934786551/50000000000000 : ℝ)^3461 := by
    have hnat : (5389935723 : ℕ)^4485*50000000000000^3461 ≤ 22445934786551^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389935723 10000000000 22445934786551 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132742007/625000000 : ℝ)^4485 ≤ (6714551595583/50000000000000 : ℝ)^3461 := by
    have hnat : (132742007 : ℕ)^4485*50000000000000^3461 ≤ 6714551595583^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132742007 625000000 6714551595583 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2544876491/5000000000 : ℝ)^4485 ≤ (10419756806919/25000000000000 : ℝ)^3461 := by
    have hnat : (2544876491 : ℕ)^4485*25000000000000^3461 ≤ 10419756806919^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544876491 5000000000 10419756806919 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389935723/10000000000 : ℝ), (-132742007/625000000 : ℝ), (2544876491/5000000000 : ℝ)] ![(22445934786551/50000000000000 : ℝ), (6714551595583/50000000000000 : ℝ), (10419756806919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389935723/10000000000 : ℝ)|^4485 ≤ (22445934786551/50000000000000 : ℝ)^3461
        have hw : |(5389935723/10000000000 : ℝ)|=(5389935723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132742007/625000000 : ℝ)|^4485 ≤ (6714551595583/50000000000000 : ℝ)^3461
        have hw : |(-132742007/625000000 : ℝ)|=(132742007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2544876491/5000000000 : ℝ)|^4485 ≤ (10419756806919/25000000000000 : ℝ)^3461
        have hw : |(2544876491/5000000000 : ℝ)|=(2544876491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389934791/10000000000 : ℝ)*x 0 + (1272438449/2500000000 : ℝ)*x 1 + (-424774457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389934791/10000000000 : ℝ)^4485 ≤ (22445929756981/50000000000000 : ℝ)^3461 := by
    have hnat : (5389934791 : ℕ)^4485*50000000000000^3461 ≤ 22445929756981^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389934791 10000000000 22445929756981 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272438449/2500000000 : ℝ)^4485 ≤ (651234935399/1562500000000 : ℝ)^3461 := by
    have hnat : (1272438449 : ℕ)^4485*1562500000000^3461 ≤ 651234935399^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272438449 2500000000 651234935399 1562500000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424774457/2000000000 : ℝ)^4485 ≤ (6714552304337/50000000000000 : ℝ)^3461 := by
    have hnat : (424774457 : ℕ)^4485*50000000000000^3461 ≤ 6714552304337^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424774457 2000000000 6714552304337 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389934791/10000000000 : ℝ), (1272438449/2500000000 : ℝ), (-424774457/2000000000 : ℝ)] ![(22445929756981/50000000000000 : ℝ), (651234935399/1562500000000 : ℝ), (6714552304337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389934791/10000000000 : ℝ)|^4485 ≤ (22445929756981/50000000000000 : ℝ)^3461
        have hw : |(5389934791/10000000000 : ℝ)|=(5389934791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1272438449/2500000000 : ℝ)|^4485 ≤ (651234935399/1562500000000 : ℝ)^3461
        have hw : |(1272438449/2500000000 : ℝ)|=(1272438449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424774457/2000000000 : ℝ)|^4485 ≤ (6714552304337/50000000000000 : ℝ)^3461
        have hw : |(-424774457/2000000000 : ℝ)|=(424774457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256174623/10000000000 : ℝ)*x 0 + (3734939083/10000000000 : ℝ)*x 1 + (1209683029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256174623/10000000000 : ℝ)^4485 ≤ (33056591402303/100000000000000 : ℝ)^3461 := by
    have hnat : (4256174623 : ℕ)^4485*100000000000000^3461 ≤ 33056591402303^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256174623 10000000000 33056591402303 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3734939083/10000000000 : ℝ)^4485 ≤ (3488556907909/12500000000000 : ℝ)^3461 := by
    have hnat : (3734939083 : ℕ)^4485*12500000000000^3461 ≤ 3488556907909^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734939083 10000000000 3488556907909 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209683029/2500000000 : ℝ)^4485 ≤ (19517476663631/50000000000000 : ℝ)^3461 := by
    have hnat : (1209683029 : ℕ)^4485*50000000000000^3461 ≤ 19517476663631^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209683029 2500000000 19517476663631 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256174623/10000000000 : ℝ), (3734939083/10000000000 : ℝ), (1209683029/2500000000 : ℝ)] ![(33056591402303/100000000000000 : ℝ), (3488556907909/12500000000000 : ℝ), (19517476663631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256174623/10000000000 : ℝ)|^4485 ≤ (33056591402303/100000000000000 : ℝ)^3461
        have hw : |(4256174623/10000000000 : ℝ)|=(4256174623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3734939083/10000000000 : ℝ)|^4485 ≤ (3488556907909/12500000000000 : ℝ)^3461
        have hw : |(3734939083/10000000000 : ℝ)|=(3734939083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209683029/2500000000 : ℝ)|^4485 ≤ (19517476663631/50000000000000 : ℝ)^3461
        have hw : |(1209683029/2500000000 : ℝ)|=(1209683029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-233000743/1250000000 : ℝ)*x 0 + (1019081809/2000000000 : ℝ)*x 1 + (1115404459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233000743/1250000000 : ℝ)^4485 ≤ (11339549808587/100000000000000 : ℝ)^3461 := by
    have hnat : (233000743 : ℕ)^4485*100000000000000^3461 ≤ 11339549808587^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233000743 1250000000 11339549808587 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019081809/2000000000 : ℝ)^4485 ≤ (20869528543517/50000000000000 : ℝ)^3461 := by
    have hnat : (1019081809 : ℕ)^4485*50000000000000^3461 ≤ 20869528543517^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019081809 2000000000 20869528543517 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115404459/2000000000 : ℝ)^4485 ≤ (1173034827259/2500000000000 : ℝ)^3461 := by
    have hnat : (1115404459 : ℕ)^4485*2500000000000^3461 ≤ 1173034827259^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115404459 2000000000 1173034827259 2500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233000743/1250000000 : ℝ), (1019081809/2000000000 : ℝ), (1115404459/2000000000 : ℝ)] ![(11339549808587/100000000000000 : ℝ), (20869528543517/50000000000000 : ℝ), (1173034827259/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233000743/1250000000 : ℝ)|^4485 ≤ (11339549808587/100000000000000 : ℝ)^3461
        have hw : |(-233000743/1250000000 : ℝ)|=(233000743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1019081809/2000000000 : ℝ)|^4485 ≤ (20869528543517/50000000000000 : ℝ)^3461
        have hw : |(1019081809/2000000000 : ℝ)|=(1019081809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1115404459/2000000000 : ℝ)|^4485 ≤ (1173034827259/2500000000000 : ℝ)^3461
        have hw : |(1115404459/2000000000 : ℝ)|=(1115404459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315091511/2500000000 : ℝ)*x 0 + (-32732057/200000000 : ℝ)*x 1 + (557702239/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315091511/2500000000 : ℝ)^4485 ≤ (43498416642079/100000000000000 : ℝ)^3461 := by
    have hnat : (1315091511 : ℕ)^4485*100000000000000^3461 ≤ 43498416642079^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315091511 2500000000 43498416642079 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32732057/200000000 : ℝ)^4485 ≤ (1916037843299/20000000000000 : ℝ)^3461 := by
    have hnat : (32732057 : ℕ)^4485*20000000000000^3461 ≤ 1916037843299^3461*200000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32732057 200000000 1916037843299 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557702239/1000000000 : ℝ)^4485 ≤ (9384278825221/20000000000000 : ℝ)^3461 := by
    have hnat : (557702239 : ℕ)^4485*20000000000000^3461 ≤ 9384278825221^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557702239 1000000000 9384278825221 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315091511/2500000000 : ℝ), (-32732057/200000000 : ℝ), (557702239/1000000000 : ℝ)] ![(43498416642079/100000000000000 : ℝ), (1916037843299/20000000000000 : ℝ), (9384278825221/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315091511/2500000000 : ℝ)|^4485 ≤ (43498416642079/100000000000000 : ℝ)^3461
        have hw : |(1315091511/2500000000 : ℝ)|=(1315091511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32732057/200000000 : ℝ)|^4485 ≤ (1916037843299/20000000000000 : ℝ)^3461
        have hw : |(-32732057/200000000 : ℝ)|=(32732057/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(557702239/1000000000 : ℝ)|^4485 ≤ (9384278825221/20000000000000 : ℝ)^3461
        have hw : |(557702239/1000000000 : ℝ)|=(557702239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263018299/500000000 : ℝ)*x 0 + (1394255599/2500000000 : ℝ)*x 1 + (-1636602933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263018299/500000000 : ℝ)^4485 ≤ (21749207978139/50000000000000 : ℝ)^3461 := by
    have hnat : (263018299 : ℕ)^4485*50000000000000^3461 ≤ 21749207978139^3461*500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263018299 500000000 21749207978139 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394255599/2500000000 : ℝ)^4485 ≤ (46921394191521/100000000000000 : ℝ)^3461 := by
    have hnat : (1394255599 : ℕ)^4485*100000000000000^3461 ≤ 46921394191521^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394255599 2500000000 46921394191521 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1636602933/10000000000 : ℝ)^4485 ≤ (4790094923051/50000000000000 : ℝ)^3461 := by
    have hnat : (1636602933 : ℕ)^4485*50000000000000^3461 ≤ 4790094923051^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636602933 10000000000 4790094923051 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263018299/500000000 : ℝ), (1394255599/2500000000 : ℝ), (-1636602933/10000000000 : ℝ)] ![(21749207978139/50000000000000 : ℝ), (46921394191521/100000000000000 : ℝ), (4790094923051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263018299/500000000 : ℝ)|^4485 ≤ (21749207978139/50000000000000 : ℝ)^3461
        have hw : |(263018299/500000000 : ℝ)|=(263018299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1394255599/2500000000 : ℝ)|^4485 ≤ (46921394191521/100000000000000 : ℝ)^3461
        have hw : |(1394255599/2500000000 : ℝ)|=(1394255599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1636602933/10000000000 : ℝ)|^4485 ≤ (4790094923051/50000000000000 : ℝ)^3461
        have hw : |(-1636602933/10000000000 : ℝ)|=(1636602933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s1_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256931231/10000000000 : ℝ)*x 0 + (1206517919/2500000000 : ℝ)*x 1 + (3747809217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256931231/10000000000 : ℝ)^4485 ≤ (1653210330567/5000000000000 : ℝ)^3461 := by
    have hnat : (4256931231 : ℕ)^4485*5000000000000^3461 ≤ 1653210330567^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256931231 10000000000 1653210330567 5000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206517919/2500000000 : ℝ)^4485 ≤ (38902652214813/100000000000000 : ℝ)^3461 := by
    have hnat : (1206517919 : ℕ)^4485*100000000000000^3461 ≤ 38902652214813^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206517919 2500000000 38902652214813 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3747809217/10000000000 : ℝ)^4485 ≤ (7008285290841/25000000000000 : ℝ)^3461 := by
    have hnat : (3747809217 : ℕ)^4485*25000000000000^3461 ≤ 7008285290841^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3747809217 10000000000 7008285290841 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256931231/10000000000 : ℝ), (1206517919/2500000000 : ℝ), (3747809217/10000000000 : ℝ)] ![(1653210330567/5000000000000 : ℝ), (38902652214813/100000000000000 : ℝ), (7008285290841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256931231/10000000000 : ℝ)|^4485 ≤ (1653210330567/5000000000000 : ℝ)^3461
        have hw : |(4256931231/10000000000 : ℝ)|=(4256931231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206517919/2500000000 : ℝ)|^4485 ≤ (38902652214813/100000000000000 : ℝ)^3461
        have hw : |(1206517919/2500000000 : ℝ)|=(1206517919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3747809217/10000000000 : ℝ)|^4485 ≤ (7008285290841/25000000000000 : ℝ)^3461
        have hw : |(3747809217/10000000000 : ℝ)|=(3747809217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2027/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18533/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2593/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (11369436696707/100000000000000000000 : ℝ) := by
    have hpowers : (2593/100000 : ℝ)^4483 ≤ (11369436696707/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2593 : ℕ)^4483*100000000000000000000^1024 ≤ 11369436696707^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2593 100000 11369436696707 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2593/100000 : ℝ)) (X := (11369436696707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25719/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (261898989007587557/100000000000000000000 : ℝ) := by
    have hpowers : (25719/100000 : ℝ)^4483 ≤ (261898989007587557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25719 : ℕ)^4483*100000000000000000000^1024 ≤ 261898989007587557^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25719 100000 261898989007587557 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25719/100000 : ℝ)) (X := (261898989007587557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000011369436696707/50000000000000000000 : ℝ) ≤ (10000000519397821/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50000011369436696707/50000000000000000000 : ℝ)^1024 ≤ (10000000519397821/10000000000000000 : ℝ)^4483 := by
      have hnat : (50000011369436696707 : ℕ)^1024*10000000000000000^4483 ≤ 10000000519397821^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000011369436696707 50000000000000000000 10000000519397821 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000519397821/10000000000000000 : ℝ)) (X := (50000011369436696707/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12532738794805535533/12500000000000000000 : ℝ) ≤ (5002988240385953/5000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (12532738794805535533/12500000000000000000 : ℝ)^1024 ≤ (5002988240385953/5000000000000000 : ℝ)^4483 := by
      have hnat : (12532738794805535533 : ℕ)^1024*5000000000000000^4483 ≤ 5002988240385953^4483*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12532738794805535533 12500000000000000000 5002988240385953 5000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002988240385953/5000000000000000 : ℝ)) (X := (12532738794805535533/12500000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50261898989007587557/50000000000000000000 : ℝ) ≤ (10011952442145991/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50261898989007587557/50000000000000000000 : ℝ)^1024 ≤ (10011952442145991/10000000000000000 : ℝ)^4483 := by
      have hnat : (50261898989007587557 : ℕ)^1024*10000000000000000^4483 ≤ 10011952442145991^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50261898989007587557 50000000000000000000 10011952442145991 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011952442145991/10000000000000000 : ℝ)) (X := (50261898989007587557/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11369436696707/100000000000000000000 : ℝ) ≤ ((57807255168977000909/57815000000000000000 : ℝ)+2*(1195192274817/462520000000000 : ℝ)*(2593/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (57807255168977000909/57815000000000000000 : ℝ)+2*(1195192274817/462520000000000 : ℝ)*(2593/100000 : ℝ)=(10000000519397821/10000000000000000 : ℝ) by norm_num, show 1+2*(11369436696707/100000000000000000000 : ℝ)=(50000011369436696707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(261898989007587557/100000000000000000000 : ℝ)+(11369436696707/100000000000000000000 : ℝ) ≤ ((57807255168977000909/57815000000000000000 : ℝ)+(1195192274817/462520000000000 : ℝ)*((25719/100000 : ℝ)+(2593/100000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (57807255168977000909/57815000000000000000 : ℝ)+(1195192274817/462520000000000 : ℝ)*((25719/100000 : ℝ)+(2593/100000 : ℝ))=(5002988240385953/5000000000000000 : ℝ) by norm_num, show 1+(261898989007587557/100000000000000000000 : ℝ)+(11369436696707/100000000000000000000 : ℝ)=(12532738794805535533/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(261898989007587557/100000000000000000000 : ℝ) ≤ ((57807255168977000909/57815000000000000000 : ℝ)+2*(1195192274817/462520000000000 : ℝ)*(25719/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (57807255168977000909/57815000000000000000 : ℝ)+2*(1195192274817/462520000000000 : ℝ)*(25719/100000 : ℝ)=(10011952442145991/10000000000000000 : ℝ) by norm_num, show 1+2*(261898989007587557/100000000000000000000 : ℝ)=(50261898989007587557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57807255168977000909/57815000000000000000 : ℝ)*(X 1 0+X 2 0)+(1195192274817/462520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2593/100000 : ℝ)) (hi := (25719/100000 : ℝ)) (c := (57807255168977000909/57815000000000000000 : ℝ)) (alpha := (1195192274817/462520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57807255168977000909/57815000000000000000 : ℝ)*(X 0 1+X 2 1)+(1195192274817/462520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2593/100000 : ℝ)) (hi := (25719/100000 : ℝ)) (c := (57807255168977000909/57815000000000000000 : ℝ)) (alpha := (1195192274817/462520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57807255168977000909/57815000000000000000 : ℝ)*(X 0 2+X 1 2)+(1195192274817/462520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2593/100000 : ℝ)) (hi := (25719/100000 : ℝ)) (c := (57807255168977000909/57815000000000000000 : ℝ)) (alpha := (1195192274817/462520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1863667479/10000000000 : ℝ)*X 0 0+(5582770663/10000000000 : ℝ)*X 0 1+(5089754529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5389935723/10000000000 : ℝ)*X 1 0+(-132742007/625000000 : ℝ)*X 1 1+(2544876491/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5389934791/10000000000 : ℝ)*X 2 0+(1272438449/2500000000 : ℝ)*X 2 1+(-424774457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4256174623/10000000000 : ℝ)*X 0 0+(3734939083/10000000000 : ℝ)*X 0 1+(1209683029/2500000000 : ℝ)*X 0 2+(4256174623/10000000000 : ℝ)*X 1 0+(3734939083/10000000000 : ℝ)*X 1 1+(1209683029/2500000000 : ℝ)*X 1 2+(4256174623/10000000000 : ℝ)*X 2 0+(3734939083/10000000000 : ℝ)*X 2 1+(1209683029/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-233000743/1250000000 : ℝ)*X 0 0+(1019081809/2000000000 : ℝ)*X 0 1+(1115404459/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1315091511/2500000000 : ℝ)*X 1 0+(-32732057/200000000 : ℝ)*X 1 1+(557702239/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263018299/500000000 : ℝ)*X 2 0+(1394255599/2500000000 : ℝ)*X 2 1+(-1636602933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256931231/10000000000 : ℝ)*X 0 0+(1206517919/2500000000 : ℝ)*X 0 1+(3747809217/10000000000 : ℝ)*X 0 2+(4256931231/10000000000 : ℝ)*X 1 0+(1206517919/2500000000 : ℝ)*X 1 1+(3747809217/10000000000 : ℝ)*X 1 2+(4256931231/10000000000 : ℝ)*X 2 0+(1206517919/2500000000 : ℝ)*X 2 1+(3747809217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1168139001702764265094186197/144537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121284971/50000000000000 : ℝ)*(base1) + (319335771/25000000000000 : ℝ)*(base19) + (115148217/12500000000000 : ℝ)*(base23) + (47490411/25000000000000 : ℝ)*(upper3) + (57354011/100000000000000 : ℝ)*(upper5) + (73357594798111/5000000000000 : ℝ)*(major0) + (73357594798111/5000000000000 : ℝ)*(major1) + (73357594798111/5000000000000 : ℝ)*(major2) + (507083475260629/25000000000000 : ℝ)*(sp0) + (202833238112949/10000000000000 : ℝ)*(sp1) + (507083127866963/25000000000000 : ℝ)*(sp2) + (452984057993167/50000000000000 : ℝ)*(sp3) + (45163797/20000000000000 : ℝ)*(sp6) + (7527493/500000000000 : ℝ)*(sp7) + (226492466013719/25000000000000 : ℝ)*(f.failure) + (1014166829236287/50000000000000 : ℝ)*(f.sum) + (52125941441/2890750000000000000000000000 : ℝ)*base66 + (202452194677107899/289075000000000000000000000000000 : ℝ)*base67 + (2815519851000742101/289075000000000000000000000000000 : ℝ)*base70 + (1036840232420042101/289075000000000000000000000000000 : ℝ)*base72 + (5597138223753/1445375000000000000000000000 : ℝ)*base73 + (2417487920740942101/289075000000000000000000000000000 : ℝ)*base76 + (766612333285192101/289075000000000000000000000000000 : ℝ)*base78 + (1186623600600307899/289075000000000000000000000000000 : ℝ)*base79 + (60420428111127/11563000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1827179/1250000000000000000000 : ℝ)*base89 + (1827179/1250000000000000000000 : ℝ)*base91 + (1827179/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (446883312817637722326901971/57815000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148289867/10000000000000 : ℝ)*(base19) + (388759611/25000000000000 : ℝ)*(base23) + (52907887/25000000000000 : ℝ)*(upper3) + (40378309/100000000000000 : ℝ)*(lower4) + (17198909/12500000000000 : ℝ)*(upper5) + (30037719597227/2000000000000 : ℝ)*(major0) + (30037719597227/2000000000000 : ℝ)*(major1) + (30037719597227/2000000000000 : ℝ)*(major2) + (4760986059/50000000000000 : ℝ)*(sp1) + (2590021291/25000000000000 : ℝ)*(sp2) + (259544182091391/12500000000000 : ℝ)*(sp4) + (103817122593017/5000000000000 : ℝ)*(sp5) + (12977134635047/625000000000 : ℝ)*(sp6) + (185483649068051/20000000000000 : ℝ)*(sp7) + (185483649068051/20000000000000 : ℝ)*(f.failure) + (259544182091391/12500000000000 : ℝ)*(f.sum) + (2972010086297/1445375000000000000000000000 : ℝ)*base65 + (314346102162054343/115630000000000000000000000000000 : ℝ)*base67 + (339236163804595657/115630000000000000000000000000000 : ℝ)*base70 + (310379988652484343/115630000000000000000000000000000 : ℝ)*base71 + (42263050290143/11563000000000000000000000000 : ℝ)*base73 + (34495060934324343/115630000000000000000000000000000 : ℝ)*base75 + (714825509150984343/115630000000000000000000000000000 : ℝ)*base77 + (782988113851465657/115630000000000000000000000000000 : ℝ)*base80 + (2056588934043/1156300000000000000000000000 : ℝ)*base82 + (10273609/1000000000000000000000 : ℝ)*base90 + (10273609/1000000000000000000000 : ℝ)*base92 + (10273609/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1494_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2027/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18533/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1494_s2_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11814573/62500000 : ℝ)*x 0 + (546391319/1000000000 : ℝ)*x 1 + (1297843337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11814573/62500000 : ℝ)^4485 ≤ (11547516284631/100000000000000 : ℝ)^3461 := by
    have hnat : (11814573 : ℕ)^4485*100000000000000^3461 ≤ 11547516284631^3461*62500000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11814573 62500000 11547516284631 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546391319/1000000000 : ℝ)^4485 ≤ (4569192945877/10000000000000 : ℝ)^3461 := by
    have hnat : (546391319 : ℕ)^4485*10000000000000^3461 ≤ 4569192945877^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546391319 1000000000 4569192945877 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297843337/2500000000 : ℝ)^4485 ≤ (42760554243297/100000000000000 : ℝ)^3461 := by
    have hnat : (1297843337 : ℕ)^4485*100000000000000^3461 ≤ 42760554243297^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297843337 2500000000 42760554243297 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11814573/62500000 : ℝ), (546391319/1000000000 : ℝ), (1297843337/2500000000 : ℝ)] ![(11547516284631/100000000000000 : ℝ), (4569192945877/10000000000000 : ℝ), (42760554243297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11814573/62500000 : ℝ)|^4485 ≤ (11547516284631/100000000000000 : ℝ)^3461
        have hw : |(-11814573/62500000 : ℝ)|=(11814573/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546391319/1000000000 : ℝ)|^4485 ≤ (4569192945877/10000000000000 : ℝ)^3461
        have hw : |(546391319/1000000000 : ℝ)|=(546391319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297843337/2500000000 : ℝ)|^4485 ≤ (42760554243297/100000000000000 : ℝ)^3461
        have hw : |(1297843337/2500000000 : ℝ)|=(1297843337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167497173/312500000 : ℝ)*x 0 + (-406157363/2000000000 : ℝ)*x 1 + (5191372903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167497173/312500000 : ℝ)^4485 ≤ (22284031143701/50000000000000 : ℝ)^3461 := by
    have hnat : (167497173 : ℕ)^4485*50000000000000^3461 ≤ 22284031143701^3461*312500000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167497173 312500000 22284031143701 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406157363/2000000000 : ℝ)^4485 ≤ (12671388199059/100000000000000 : ℝ)^3461 := by
    have hnat : (406157363 : ℕ)^4485*100000000000000^3461 ≤ 12671388199059^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406157363 2000000000 12671388199059 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191372903/10000000000 : ℝ)^4485 ≤ (1710421979737/4000000000000 : ℝ)^3461 := by
    have hnat : (5191372903 : ℕ)^4485*4000000000000^3461 ≤ 1710421979737^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191372903 10000000000 1710421979737 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167497173/312500000 : ℝ), (-406157363/2000000000 : ℝ), (5191372903/10000000000 : ℝ)] ![(22284031143701/50000000000000 : ℝ), (12671388199059/100000000000000 : ℝ), (1710421979737/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167497173/312500000 : ℝ)|^4485 ≤ (22284031143701/50000000000000 : ℝ)^3461
        have hw : |(167497173/312500000 : ℝ)|=(167497173/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406157363/2000000000 : ℝ)|^4485 ≤ (12671388199059/100000000000000 : ℝ)^3461
        have hw : |(-406157363/2000000000 : ℝ)|=(406157363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191372903/10000000000 : ℝ)|^4485 ≤ (1710421979737/4000000000000 : ℝ)^3461
        have hw : |(5191372903/10000000000 : ℝ)|=(5191372903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359909599/10000000000 : ℝ)*x 0 + (5191372619/10000000000 : ℝ)*x 1 + (-507696777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359909599/10000000000 : ℝ)^4485 ≤ (22284031483121/50000000000000 : ℝ)^3461 := by
    have hnat : (5359909599 : ℕ)^4485*50000000000000^3461 ≤ 22284031483121^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359909599 10000000000 22284031483121 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191372619/10000000000 : ℝ)^4485 ≤ (21380273231023/50000000000000 : ℝ)^3461 := by
    have hnat : (5191372619 : ℕ)^4485*50000000000000^3461 ≤ 21380273231023^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191372619 10000000000 21380273231023 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507696777/2500000000 : ℝ)^4485 ≤ (6335695284093/50000000000000 : ℝ)^3461 := by
    have hnat : (507696777 : ℕ)^4485*50000000000000^3461 ≤ 6335695284093^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507696777 2500000000 6335695284093 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359909599/10000000000 : ℝ), (5191372619/10000000000 : ℝ), (-507696777/2500000000 : ℝ)] ![(22284031483121/50000000000000 : ℝ), (21380273231023/50000000000000 : ℝ), (6335695284093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359909599/10000000000 : ℝ)|^4485 ≤ (22284031483121/50000000000000 : ℝ)^3461
        have hw : |(5359909599/10000000000 : ℝ)|=(5359909599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191372619/10000000000 : ℝ)|^4485 ≤ (21380273231023/50000000000000 : ℝ)^3461
        have hw : |(5191372619/10000000000 : ℝ)|=(5191372619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507696777/2500000000 : ℝ)|^4485 ≤ (6335695284093/50000000000000 : ℝ)^3461
        have hw : |(-507696777/2500000000 : ℝ)|=(507696777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068813069/2500000000 : ℝ)*x 0 + (3979535701/10000000000 : ℝ)*x 1 + (4589712827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068813069/2500000000 : ℝ)^4485 ≤ (33248728844391/100000000000000 : ℝ)^3461 := by
    have hnat : (1068813069 : ℕ)^4485*100000000000000^3461 ≤ 33248728844391^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068813069 2500000000 33248728844391 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979535701/10000000000 : ℝ)^4485 ≤ (30299504105941/100000000000000 : ℝ)^3461 := by
    have hnat : (3979535701 : ℕ)^4485*100000000000000^3461 ≤ 30299504105941^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979535701 10000000000 30299504105941 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4589712827/10000000000 : ℝ)^4485 ≤ (36451767034973/100000000000000 : ℝ)^3461 := by
    have hnat : (4589712827 : ℕ)^4485*100000000000000^3461 ≤ 36451767034973^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589712827 10000000000 36451767034973 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068813069/2500000000 : ℝ), (3979535701/10000000000 : ℝ), (4589712827/10000000000 : ℝ)] ![(33248728844391/100000000000000 : ℝ), (30299504105941/100000000000000 : ℝ), (36451767034973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068813069/2500000000 : ℝ)|^4485 ≤ (33248728844391/100000000000000 : ℝ)^3461
        have hw : |(1068813069/2500000000 : ℝ)|=(1068813069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979535701/10000000000 : ℝ)|^4485 ≤ (30299504105941/100000000000000 : ℝ)^3461
        have hw : |(3979535701/10000000000 : ℝ)|=(3979535701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4589712827/10000000000 : ℝ)|^4485 ≤ (36451767034973/100000000000000 : ℝ)^3461
        have hw : |(4589712827/10000000000 : ℝ)|=(4589712827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-945193729/5000000000 : ℝ)*x 0 + (5193112107/10000000000 : ℝ)*x 1 + (5462159641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945193729/5000000000 : ℝ)^4485 ≤ (11547957830933/100000000000000 : ℝ)^3461 := by
    have hnat : (945193729 : ℕ)^4485*100000000000000^3461 ≤ 11547957830933^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945193729 5000000000 11547957830933 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193112107/10000000000 : ℝ)^4485 ≤ (5347389306299/12500000000000 : ℝ)^3461 := by
    have hnat : (5193112107 : ℕ)^4485*12500000000000^3461 ≤ 5347389306299^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193112107 10000000000 5347389306299 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462159641/10000000000 : ℝ)^4485 ≤ (5709115962283/12500000000000 : ℝ)^3461 := by
    have hnat : (5462159641 : ℕ)^4485*12500000000000^3461 ≤ 5709115962283^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462159641 10000000000 5709115962283 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-945193729/5000000000 : ℝ), (5193112107/10000000000 : ℝ), (5462159641/10000000000 : ℝ)] ![(11547957830933/100000000000000 : ℝ), (5347389306299/12500000000000 : ℝ), (5709115962283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-945193729/5000000000 : ℝ)|^4485 ≤ (11547957830933/100000000000000 : ℝ)^3461
        have hw : |(-945193729/5000000000 : ℝ)|=(945193729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193112107/10000000000 : ℝ)|^4485 ≤ (5347389306299/12500000000000 : ℝ)^3461
        have hw : |(5193112107/10000000000 : ℝ)|=(5193112107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462159641/10000000000 : ℝ)|^4485 ≤ (5709115962283/12500000000000 : ℝ)^3461
        have hw : |(5462159641/10000000000 : ℝ)|=(5462159641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330533799/625000000 : ℝ)*x 0 + (-879999959/5000000000 : ℝ)*x 1 + (1092432131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330533799/625000000 : ℝ)^4485 ≤ (5475070759951/12500000000000 : ℝ)^3461 := by
    have hnat : (330533799 : ℕ)^4485*12500000000000^3461 ≤ 5475070759951^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330533799 625000000 5475070759951 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879999959/5000000000 : ℝ)^4485 ≤ (10526495226603/100000000000000 : ℝ)^3461 := by
    have hnat : (879999959 : ℕ)^4485*100000000000000^3461 ≤ 10526495226603^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879999959 5000000000 10526495226603 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092432131/2000000000 : ℝ)^4485 ≤ (22836469342811/50000000000000 : ℝ)^3461 := by
    have hnat : (1092432131 : ℕ)^4485*50000000000000^3461 ≤ 22836469342811^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092432131 2000000000 22836469342811 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330533799/625000000 : ℝ), (-879999959/5000000000 : ℝ), (1092432131/2000000000 : ℝ)] ![(5475070759951/12500000000000 : ℝ), (10526495226603/100000000000000 : ℝ), (22836469342811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330533799/625000000 : ℝ)|^4485 ≤ (5475070759951/12500000000000 : ℝ)^3461
        have hw : |(330533799/625000000 : ℝ)|=(330533799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-879999959/5000000000 : ℝ)|^4485 ≤ (10526495226603/100000000000000 : ℝ)^3461
        have hw : |(-879999959/5000000000 : ℝ)|=(879999959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092432131/2000000000 : ℝ)|^4485 ≤ (22836469342811/50000000000000 : ℝ)^3461
        have hw : |(1092432131/2000000000 : ℝ)|=(1092432131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057708243/2000000000 : ℝ)*x 0 + (5462159113/10000000000 : ℝ)*x 1 + (-440000369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057708243/2000000000 : ℝ)^4485 ≤ (10950142676339/25000000000000 : ℝ)^3461 := by
    have hnat : (1057708243 : ℕ)^4485*25000000000000^3461 ≤ 10950142676339^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057708243 2000000000 10950142676339 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462159113/10000000000 : ℝ)^4485 ≤ (45672921977037/100000000000000 : ℝ)^3461 := by
    have hnat : (5462159113 : ℕ)^4485*100000000000000^3461 ≤ 45672921977037^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462159113 10000000000 45672921977037 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440000369/2500000000 : ℝ)^4485 ≤ (10526507301947/100000000000000 : ℝ)^3461 := by
    have hnat : (440000369 : ℕ)^4485*100000000000000^3461 ≤ 10526507301947^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440000369 2500000000 10526507301947 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057708243/2000000000 : ℝ), (5462159113/10000000000 : ℝ), (-440000369/2500000000 : ℝ)] ![(10950142676339/25000000000000 : ℝ), (45672921977037/100000000000000 : ℝ), (10526507301947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057708243/2000000000 : ℝ)|^4485 ≤ (10950142676339/25000000000000 : ℝ)^3461
        have hw : |(1057708243/2000000000 : ℝ)|=(1057708243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462159113/10000000000 : ℝ)|^4485 ≤ (45672921977037/100000000000000 : ℝ)^3461
        have hw : |(5462159113/10000000000 : ℝ)|=(5462159113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440000369/2500000000 : ℝ)|^4485 ≤ (10526507301947/100000000000000 : ℝ)^3461
        have hw : |(-440000369/2500000000 : ℝ)|=(440000369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s2_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275382039/10000000000 : ℝ)*x 0 + (2292912091/5000000000 : ℝ)*x 1 + (3983458359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275382039/10000000000 : ℝ)^4485 ≤ (6650007320231/20000000000000 : ℝ)^3461 := by
    have hnat : (4275382039 : ℕ)^4485*20000000000000^3461 ≤ 6650007320231^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275382039 10000000000 6650007320231 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2292912091/5000000000 : ℝ)^4485 ≤ (4551468832189/12500000000000 : ℝ)^3461 := by
    have hnat : (2292912091 : ℕ)^4485*12500000000000^3461 ≤ 4551468832189^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292912091 5000000000 4551468832189 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983458359/10000000000 : ℝ)^4485 ≤ (6067642545723/20000000000000 : ℝ)^3461 := by
    have hnat : (3983458359 : ℕ)^4485*20000000000000^3461 ≤ 6067642545723^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983458359 10000000000 6067642545723 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275382039/10000000000 : ℝ), (2292912091/5000000000 : ℝ), (3983458359/10000000000 : ℝ)] ![(6650007320231/20000000000000 : ℝ), (4551468832189/12500000000000 : ℝ), (6067642545723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275382039/10000000000 : ℝ)|^4485 ≤ (6650007320231/20000000000000 : ℝ)^3461
        have hw : |(4275382039/10000000000 : ℝ)|=(4275382039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2292912091/5000000000 : ℝ)|^4485 ≤ (4551468832189/12500000000000 : ℝ)^3461
        have hw : |(2292912091/5000000000 : ℝ)|=(2292912091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983458359/10000000000 : ℝ)|^4485 ≤ (6067642545723/20000000000000 : ℝ)^3461
        have hw : |(3983458359/10000000000 : ℝ)|=(3983458359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2027/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5151/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2027/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2027/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2027/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2027/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2027/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2027/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2027/25000 : ℝ) ^ (4483/1024 : ℝ) ≤ (334449896952833/20000000000000000000 : ℝ) := by
    have hpowers : (2027/25000 : ℝ)^4483 ≤ (334449896952833/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2027 : ℕ)^4483*20000000000000000000^1024 ≤ 334449896952833^1024*25000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2027 25000 334449896952833 20000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2027/25000 : ℝ)) (X := (334449896952833/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18533/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (7798801613483961/12500000000000000000 : ℝ) := by
    have hpowers : (18533/100000 : ℝ)^4483 ≤ (7798801613483961/12500000000000000000 : ℝ)^1024 := by
      have hnat : (18533 : ℕ)^4483*12500000000000000000^1024 ≤ 7798801613483961^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18533 100000 7798801613483961 12500000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18533/100000 : ℝ)) (X := (7798801613483961/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000334449896952833/10000000000000000000 : ℝ) ≤ (10000076393547997/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (10000334449896952833/10000000000000000000 : ℝ)^1024 ≤ (10000076393547997/10000000000000000 : ℝ)^4483 := by
      have hnat : (10000334449896952833 : ℕ)^1024*10000000000000000^4483 ≤ 10000076393547997^4483*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000334449896952833 10000000000000000000 10000076393547997 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000076393547997/10000000000000000 : ℝ)) (X := (10000334449896952833/10000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100064062662392635853/100000000000000000000 : ℝ) ≤ (2000292589602863/2000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (100064062662392635853/100000000000000000000 : ℝ)^1024 ≤ (2000292589602863/2000000000000000 : ℝ)^4483 := by
      have hnat : (100064062662392635853 : ℕ)^1024*2000000000000000^4483 ≤ 2000292589602863^4483*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100064062662392635853 100000000000000000000 2000292589602863 2000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000292589602863/2000000000000000 : ℝ)) (X := (100064062662392635853/100000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6257798801613483961/6250000000000000000 : ℝ) ≤ (10002849502480633/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (6257798801613483961/6250000000000000000 : ℝ)^1024 ≤ (10002849502480633/10000000000000000 : ℝ)^4483 := by
      have hnat : (6257798801613483961 : ℕ)^1024*10000000000000000^4483 ≤ 10002849502480633^4483*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257798801613483961 6250000000000000000 10002849502480633 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002849502480633/10000000000000000 : ℝ)) (X := (6257798801613483961/6250000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(334449896952833/20000000000000000000 : ℝ) ≤ ((34742770678504018679/34750000000000000000 : ℝ)+2*(231092411053/173750000000000 : ℝ)*(2027/25000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (34742770678504018679/34750000000000000000 : ℝ)+2*(231092411053/173750000000000 : ℝ)*(2027/25000 : ℝ)=(10000076393547997/10000000000000000 : ℝ) by norm_num, show 1+2*(334449896952833/20000000000000000000 : ℝ)=(10000334449896952833/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7798801613483961/12500000000000000000 : ℝ)+(334449896952833/20000000000000000000 : ℝ) ≤ ((34742770678504018679/34750000000000000000 : ℝ)+(231092411053/173750000000000 : ℝ)*((18533/100000 : ℝ)+(2027/25000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (34742770678504018679/34750000000000000000 : ℝ)+(231092411053/173750000000000 : ℝ)*((18533/100000 : ℝ)+(2027/25000 : ℝ))=(2000292589602863/2000000000000000 : ℝ) by norm_num, show 1+(7798801613483961/12500000000000000000 : ℝ)+(334449896952833/20000000000000000000 : ℝ)=(100064062662392635853/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7798801613483961/12500000000000000000 : ℝ) ≤ ((34742770678504018679/34750000000000000000 : ℝ)+2*(231092411053/173750000000000 : ℝ)*(18533/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (34742770678504018679/34750000000000000000 : ℝ)+2*(231092411053/173750000000000 : ℝ)*(18533/100000 : ℝ)=(10002849502480633/10000000000000000 : ℝ) by norm_num, show 1+2*(7798801613483961/12500000000000000000 : ℝ)=(6257798801613483961/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34742770678504018679/34750000000000000000 : ℝ)*(X 1 0+X 2 0)+(231092411053/173750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2027/25000 : ℝ)) (hi := (18533/100000 : ℝ)) (c := (34742770678504018679/34750000000000000000 : ℝ)) (alpha := (231092411053/173750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34742770678504018679/34750000000000000000 : ℝ)*(X 0 1+X 2 1)+(231092411053/173750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2027/25000 : ℝ)) (hi := (18533/100000 : ℝ)) (c := (34742770678504018679/34750000000000000000 : ℝ)) (alpha := (231092411053/173750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34742770678504018679/34750000000000000000 : ℝ)*(X 0 2+X 1 2)+(231092411053/173750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2027/25000 : ℝ)) (hi := (18533/100000 : ℝ)) (c := (34742770678504018679/34750000000000000000 : ℝ)) (alpha := (231092411053/173750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-11814573/62500000 : ℝ)*X 0 0+(546391319/1000000000 : ℝ)*X 0 1+(1297843337/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167497173/312500000 : ℝ)*X 1 0+(-406157363/2000000000 : ℝ)*X 1 1+(5191372903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359909599/10000000000 : ℝ)*X 2 0+(5191372619/10000000000 : ℝ)*X 2 1+(-507696777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068813069/2500000000 : ℝ)*X 0 0+(3979535701/10000000000 : ℝ)*X 0 1+(4589712827/10000000000 : ℝ)*X 0 2+(1068813069/2500000000 : ℝ)*X 1 0+(3979535701/10000000000 : ℝ)*X 1 1+(4589712827/10000000000 : ℝ)*X 1 2+(1068813069/2500000000 : ℝ)*X 2 0+(3979535701/10000000000 : ℝ)*X 2 1+(4589712827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-945193729/5000000000 : ℝ)*X 0 0+(5193112107/10000000000 : ℝ)*X 0 1+(5462159641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330533799/625000000 : ℝ)*X 1 0+(-879999959/5000000000 : ℝ)*X 1 1+(1092432131/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057708243/2000000000 : ℝ)*X 2 0+(5462159113/10000000000 : ℝ)*X 2 1+(-440000369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275382039/10000000000 : ℝ)*X 0 0+(2292912091/5000000000 : ℝ)*X 0 1+(3983458359/10000000000 : ℝ)*X 0 2+(4275382039/10000000000 : ℝ)*X 1 0+(2292912091/5000000000 : ℝ)*X 1 1+(3983458359/10000000000 : ℝ)*X 1 2+(4275382039/10000000000 : ℝ)*X 2 0+(2292912091/5000000000 : ℝ)*X 2 1+(3983458359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4849312928966850967745402883/868750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2467404389/100000000000000 : ℝ)*(base19) + (11498699/500000000000 : ℝ)*(base23) + (36966089/100000000000000 : ℝ)*(upper2) + (93733907/25000000000000 : ℝ)*(upper3) + (149949007/100000000000000 : ℝ)*(upper4) + (1327034174163053/50000000000000 : ℝ)*(major0) + (1327034174163053/50000000000000 : ℝ)*(major1) + (1327034174163053/50000000000000 : ℝ)*(major2) + (1834609455170257/50000000000000 : ℝ)*(sp0) + (1834620191531583/50000000000000 : ℝ)*(sp1) + (1834620275363877/50000000000000 : ℝ)*(sp2) + (3277758031167/200000000000 : ℝ)*(sp3) + (74812897/312500000000 : ℝ)*(sp4) + (7322268193/50000000000000 : ℝ)*(sp7) + (327778732023977/20000000000000 : ℝ)*(f.failure) + (1834621425233777/50000000000000 : ℝ)*(f.sum) + (16004295947007/8687500000000000000000000000 : ℝ)*base66 + (7238316315484533013/1737500000000000000000000000000000 : ℝ)*base68 + (10690113556309533013/1737500000000000000000000000000000 : ℝ)*base70 + (20107970715259533013/1737500000000000000000000000000000 : ℝ)*base72 + (19341983476507/8687500000000000000000000000 : ℝ)*base74 + (20810664264484533013/1737500000000000000000000000000000 : ℝ)*base76 + (17964868141884533013/1737500000000000000000000000000000 : ℝ)*base78 + (18116655756159533013/1737500000000000000000000000000000 : ℝ)*base80 + (24733847165257/8687500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1843157/1000000000000000000000 : ℝ)*base89 + (1843157/1000000000000000000000 : ℝ)*base91 + (1843157/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17531347428500537604603358917/1737500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (520056359/100000000000000 : ℝ)*(base19) + (409490071/20000000000000 : ℝ)*(base23) + (70515037/25000000000000 : ℝ)*(upper3) + (12986121/2000000000000 : ℝ)*(lower4) + (2688468008742241/100000000000000 : ℝ)*(major0) + (2688468008742241/100000000000000 : ℝ)*(major1) + (2688468008742241/100000000000000 : ℝ)*(major2) + (1221682313/10000000000000 : ℝ)*(sp1) + (5987135619/50000000000000 : ℝ)*(sp2) + (1881076873/25000000000000 : ℝ)*(sp3) + (929200036765129/25000000000000 : ℝ)*(sp4) + (929196852545257/25000000000000 : ℝ)*(sp5) + (929196531334731/25000000000000 : ℝ)*(sp6) + (1660128009783663/100000000000000 : ℝ)*(sp7) + (332027106818231/20000000000000 : ℝ)*(f.failure) + (929200036765129/25000000000000 : ℝ)*(f.sum) + (120665786202171/17375000000000000000000000000 : ℝ)*base65 + (371409050035080361/3475000000000000000000000000000000 : ℝ)*base68 + (2405651492639919639/3475000000000000000000000000000000 : ℝ)*base69 + (2500621074239919639/3475000000000000000000000000000000 : ℝ)*base71 + (22939707473773/8687500000000000000000000000 : ℝ)*base73 + (32743504292010080361/3475000000000000000000000000000000 : ℝ)*base76 + (23527659176010080361/3475000000000000000000000000000000 : ℝ)*base78 + (18689452888985080361/3475000000000000000000000000000000 : ℝ)*base80 + (1326205923671/17375000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2682229/1000000000000000000000 : ℝ)*base90 + (2682229/1000000000000000000000 : ℝ)*base92 + (2682229/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1494_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2027/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1494_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1494_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1494_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1494_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1494_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
