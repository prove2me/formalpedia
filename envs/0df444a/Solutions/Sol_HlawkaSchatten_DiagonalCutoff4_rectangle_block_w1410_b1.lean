-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1410_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:44.11479+00:00
-- url     : https://prove2.me/submissions/52bff0f6-3208-4d1b-bad7-6463d6c4d022

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
theorem support_rectangle_w1410_s3_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-397094037/2000000000 : ℝ)*x 0 + (5419242103/10000000000 : ℝ)*x 1 + (2618599997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397094037/2000000000 : ℝ)^2185 ≤ (12105522531627/100000000000000 : ℝ)^1673 := by
    have hnat : (397094037 : ℕ)^2185*100000000000000^1673 ≤ 12105522531627^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397094037 2000000000 12105522531627 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419242103/10000000000 : ℝ)^2185 ≤ (44927669439017/100000000000000 : ℝ)^1673 := by
    have hnat : (5419242103 : ℕ)^2185*100000000000000^1673 ≤ 44927669439017^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419242103 10000000000 44927669439017 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618599997/5000000000 : ℝ)^2185 ≤ (42966808013057/100000000000000 : ℝ)^1673 := by
    have hnat : (2618599997 : ℕ)^2185*100000000000000^1673 ≤ 42966808013057^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618599997 5000000000 42966808013057 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397094037/2000000000 : ℝ), (5419242103/10000000000 : ℝ), (2618599997/5000000000 : ℝ)] ![(12105522531627/100000000000000 : ℝ), (44927669439017/100000000000000 : ℝ), (42966808013057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397094037/2000000000 : ℝ)|^2185 ≤ (12105522531627/100000000000000 : ℝ)^1673
        have hw : |(-397094037/2000000000 : ℝ)|=(397094037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419242103/10000000000 : ℝ)|^2185 ≤ (44927669439017/100000000000000 : ℝ)^1673
        have hw : |(5419242103/10000000000 : ℝ)|=(5419242103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618599997/5000000000 : ℝ)|^2185 ≤ (42966808013057/100000000000000 : ℝ)^1673
        have hw : |(2618599997/5000000000 : ℝ)|=(2618599997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675153183/5000000000 : ℝ)*x 0 + (-6494887/31250000 : ℝ)*x 1 + (5237199913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675153183/5000000000 : ℝ)^2185 ≤ (2209136018163/5000000000000 : ℝ)^1673 := by
    have hnat : (2675153183 : ℕ)^2185*5000000000000^1673 ≤ 2209136018163^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675153183 5000000000 2209136018163 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6494887/31250000 : ℝ)^2185 ≤ (12850472481497/100000000000000 : ℝ)^1673 := by
    have hnat : (6494887 : ℕ)^2185*100000000000000^1673 ≤ 12850472481497^1673*31250000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6494887 31250000 12850472481497 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237199913/10000000000 : ℝ)^2185 ≤ (42966807145147/100000000000000 : ℝ)^1673 := by
    have hnat : (5237199913 : ℕ)^2185*100000000000000^1673 ≤ 42966807145147^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237199913 10000000000 42966807145147 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675153183/5000000000 : ℝ), (-6494887/31250000 : ℝ), (5237199913/10000000000 : ℝ)] ![(2209136018163/5000000000000 : ℝ), (12850472481497/100000000000000 : ℝ), (42966807145147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675153183/5000000000 : ℝ)|^2185 ≤ (2209136018163/5000000000000 : ℝ)^1673
        have hw : |(2675153183/5000000000 : ℝ)|=(2675153183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6494887/31250000 : ℝ)|^2185 ≤ (12850472481497/100000000000000 : ℝ)^1673
        have hw : |(-6494887/31250000 : ℝ)|=(6494887/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237199913/10000000000 : ℝ)|^2185 ≤ (42966807145147/100000000000000 : ℝ)^1673
        have hw : |(5237199913/10000000000 : ℝ)|=(5237199913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66878829/125000000 : ℝ)*x 0 + (5237200017/10000000000 : ℝ)*x 1 + (-2078363763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66878829/125000000 : ℝ)^2185 ≤ (2209135993357/5000000000000 : ℝ)^1673 := by
    have hnat : (66878829 : ℕ)^2185*5000000000000^1673 ≤ 2209135993357^1673*125000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66878829 125000000 2209135993357 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237200017/10000000000 : ℝ)^2185 ≤ (85933616519/200000000000 : ℝ)^1673 := by
    have hnat : (5237200017 : ℕ)^2185*200000000000^1673 ≤ 85933616519^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237200017 10000000000 85933616519 200000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078363763/10000000000 : ℝ)^2185 ≤ (12850471859707/100000000000000 : ℝ)^1673 := by
    have hnat : (2078363763 : ℕ)^2185*100000000000000^1673 ≤ 12850471859707^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078363763 10000000000 12850471859707 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66878829/125000000 : ℝ), (5237200017/10000000000 : ℝ), (-2078363763/10000000000 : ℝ)] ![(2209135993357/5000000000000 : ℝ), (85933616519/200000000000 : ℝ), (12850471859707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66878829/125000000 : ℝ)|^2185 ≤ (2209135993357/5000000000000 : ℝ)^1673
        have hw : |(66878829/125000000 : ℝ)|=(66878829/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237200017/10000000000 : ℝ)|^2185 ≤ (85933616519/200000000000 : ℝ)^1673
        have hw : |(5237200017/10000000000 : ℝ)|=(5237200017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078363763/10000000000 : ℝ)|^2185 ≤ (12850471859707/100000000000000 : ℝ)^1673
        have hw : |(-2078363763/10000000000 : ℝ)|=(2078363763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2154213621/5000000000 : ℝ)*x 0 + (2058455491/5000000000 : ℝ)*x 1 + (4507989069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154213621/5000000000 : ℝ)^2185 ≤ (8324281565677/25000000000000 : ℝ)^1673 := by
    have hnat : (2154213621 : ℕ)^2185*25000000000000^1673 ≤ 8324281565677^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154213621 5000000000 8324281565677 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058455491/5000000000 : ℝ)^2185 ≤ (627546714789/2000000000000 : ℝ)^1673 := by
    have hnat : (2058455491 : ℕ)^2185*2000000000000^1673 ≤ 627546714789^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058455491 5000000000 627546714789 2000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507989069/10000000000 : ℝ)^2185 ≤ (35325537985481/100000000000000 : ℝ)^1673 := by
    have hnat : (4507989069 : ℕ)^2185*100000000000000^1673 ≤ 35325537985481^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507989069 10000000000 35325537985481 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154213621/5000000000 : ℝ), (2058455491/5000000000 : ℝ), (4507989069/10000000000 : ℝ)] ![(8324281565677/25000000000000 : ℝ), (627546714789/2000000000000 : ℝ), (35325537985481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154213621/5000000000 : ℝ)|^2185 ≤ (8324281565677/25000000000000 : ℝ)^1673
        have hw : |(2154213621/5000000000 : ℝ)|=(2154213621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2058455491/5000000000 : ℝ)|^2185 ≤ (627546714789/2000000000000 : ℝ)^1673
        have hw : |(2058455491/5000000000 : ℝ)|=(2058455491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507989069/10000000000 : ℝ)|^2185 ≤ (35325537985481/100000000000000 : ℝ)^1673
        have hw : |(4507989069/10000000000 : ℝ)|=(4507989069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-198548657/1000000000 : ℝ)*x 0 + (5237932677/10000000000 : ℝ)*x 1 + (5418504961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198548657/1000000000 : ℝ)^2185 ≤ (12105653005233/100000000000000 : ℝ)^1673 := by
    have hnat : (198548657 : ℕ)^2185*100000000000000^1673 ≤ 12105653005233^1673*1000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198548657 1000000000 12105653005233 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237932677/10000000000 : ℝ)^2185 ≤ (42974658829883/100000000000000 : ℝ)^1673 := by
    have hnat : (5237932677 : ℕ)^2185*100000000000000^1673 ≤ 42974658829883^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237932677 10000000000 42974658829883 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418504961/10000000000 : ℝ)^2185 ≤ (44919688151529/100000000000000 : ℝ)^1673 := by
    have hnat : (5418504961 : ℕ)^2185*100000000000000^1673 ≤ 44919688151529^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418504961 10000000000 44919688151529 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198548657/1000000000 : ℝ), (5237932677/10000000000 : ℝ), (5418504961/10000000000 : ℝ)] ![(12105653005233/100000000000000 : ℝ), (42974658829883/100000000000000 : ℝ), (44919688151529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198548657/1000000000 : ℝ)|^2185 ≤ (12105653005233/100000000000000 : ℝ)^1673
        have hw : |(-198548657/1000000000 : ℝ)|=(198548657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237932677/10000000000 : ℝ)|^2185 ≤ (42974658829883/100000000000000 : ℝ)^1673
        have hw : |(5237932677/10000000000 : ℝ)|=(5237932677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418504961/10000000000 : ℝ)|^2185 ≤ (44919688151529/100000000000000 : ℝ)^1673
        have hw : |(5418504961/10000000000 : ℝ)|=(5418504961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303070573/10000000000 : ℝ)*x 0 + (-1897058281/10000000000 : ℝ)*x 1 + (5418505229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303070573/10000000000 : ℝ)^2185 ≤ (21836980623209/50000000000000 : ℝ)^1673 := by
    have hnat : (5303070573 : ℕ)^2185*50000000000000^1673 ≤ 21836980623209^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303070573 10000000000 21836980623209 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1897058281/10000000000 : ℝ)^2185 ≤ (11406347690899/100000000000000 : ℝ)^1673 := by
    have hnat : (1897058281 : ℕ)^2185*100000000000000^1673 ≤ 11406347690899^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897058281 10000000000 11406347690899 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418505229/10000000000 : ℝ)^2185 ≤ (11229922763299/25000000000000 : ℝ)^1673 := by
    have hnat : (5418505229 : ℕ)^2185*25000000000000^1673 ≤ 11229922763299^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418505229 10000000000 11229922763299 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303070573/10000000000 : ℝ), (-1897058281/10000000000 : ℝ), (5418505229/10000000000 : ℝ)] ![(21836980623209/50000000000000 : ℝ), (11406347690899/100000000000000 : ℝ), (11229922763299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303070573/10000000000 : ℝ)|^2185 ≤ (21836980623209/50000000000000 : ℝ)^1673
        have hw : |(5303070573/10000000000 : ℝ)|=(5303070573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1897058281/10000000000 : ℝ)|^2185 ≤ (11406347690899/100000000000000 : ℝ)^1673
        have hw : |(-1897058281/10000000000 : ℝ)|=(1897058281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418505229/10000000000 : ℝ)|^2185 ≤ (11229922763299/25000000000000 : ℝ)^1673
        have hw : |(5418505229/10000000000 : ℝ)|=(5418505229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303071333/10000000000 : ℝ)*x 0 + (169328269/312500000 : ℝ)*x 1 + (-118566131/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303071333/10000000000 : ℝ)^2185 ≤ (2729623088811/6250000000000 : ℝ)^1673 := by
    have hnat : (5303071333 : ℕ)^2185*6250000000000^1673 ≤ 2729623088811^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303071333 10000000000 2729623088811 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169328269/312500000 : ℝ)^2185 ≤ (44919684329557/100000000000000 : ℝ)^1673 := by
    have hnat : (169328269 : ℕ)^2185*100000000000000^1673 ≤ 44919684329557^1673*312500000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169328269 312500000 44919684329557 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118566131/625000000 : ℝ)^2185 ≤ (11406346238141/100000000000000 : ℝ)^1673 := by
    have hnat : (118566131 : ℕ)^2185*100000000000000^1673 ≤ 11406346238141^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118566131 625000000 11406346238141 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303071333/10000000000 : ℝ), (169328269/312500000 : ℝ), (-118566131/625000000 : ℝ)] ![(2729623088811/6250000000000 : ℝ), (44919684329557/100000000000000 : ℝ), (11406346238141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303071333/10000000000 : ℝ)|^2185 ≤ (2729623088811/6250000000000 : ℝ)^1673
        have hw : |(5303071333/10000000000 : ℝ)|=(5303071333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169328269/312500000 : ℝ)|^2185 ≤ (44919684329557/100000000000000 : ℝ)^1673
        have hw : |(169328269/312500000 : ℝ)|=(169328269/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118566131/625000000 : ℝ)|^2185 ≤ (11406346238141/100000000000000 : ℝ)^1673
        have hw : |(-118566131/625000000 : ℝ)|=(118566131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s3_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4308462673/10000000000 : ℝ)*x 0 + (4506414763/10000000000 : ℝ)*x 1 + (823698703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308462673/10000000000 : ℝ)^2185 ≤ (16648741943679/50000000000000 : ℝ)^1673 := by
    have hnat : (4308462673 : ℕ)^2185*50000000000000^1673 ≤ 16648741943679^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308462673 10000000000 16648741943679 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506414763/10000000000 : ℝ)^2185 ≤ (4413678350587/12500000000000 : ℝ)^1673 := by
    have hnat : (4506414763 : ℕ)^2185*12500000000000^1673 ≤ 4413678350587^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506414763 10000000000 4413678350587 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823698703/2000000000 : ℝ)^2185 ≤ (31393089288361/100000000000000 : ℝ)^1673 := by
    have hnat : (823698703 : ℕ)^2185*100000000000000^1673 ≤ 31393089288361^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823698703 2000000000 31393089288361 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308462673/10000000000 : ℝ), (4506414763/10000000000 : ℝ), (823698703/2000000000 : ℝ)] ![(16648741943679/50000000000000 : ℝ), (4413678350587/12500000000000 : ℝ), (31393089288361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308462673/10000000000 : ℝ)|^2185 ≤ (16648741943679/50000000000000 : ℝ)^1673
        have hw : |(4308462673/10000000000 : ℝ)|=(4308462673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506414763/10000000000 : ℝ)|^2185 ≤ (4413678350587/12500000000000 : ℝ)^1673
        have hw : |(4506414763/10000000000 : ℝ)|=(4506414763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(823698703/2000000000 : ℝ)|^2185 ≤ (31393089288361/100000000000000 : ℝ)^1673
        have hw : |(823698703/2000000000 : ℝ)|=(823698703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11103/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14957/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1283/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1283/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1283/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1283/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1283/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1283/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1283/12500 : ℝ) ^ (4369/1024 : ℝ) ≤ (6048978568004069/100000000000000000000 : ℝ) := by
    have hpowers : (1283/12500 : ℝ)^4369 ≤ (6048978568004069/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1283 : ℕ)^4369*100000000000000000000^1024 ≤ 6048978568004069^1024*12500^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1283 12500 6048978568004069 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1283/12500 : ℝ)) (X := (6048978568004069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15859/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (2419777823655923/6250000000000000000 : ℝ) := by
    have hpowers : (15859/100000 : ℝ)^4369 ≤ (2419777823655923/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15859 : ℕ)^4369*6250000000000000000^1024 ≤ 2419777823655923^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15859 100000 2419777823655923 6250000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15859/100000 : ℝ)) (X := (2419777823655923/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006048978568004069/50000000000000000000 : ℝ) ≤ (1250035442133261/1250000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50006048978568004069/50000000000000000000 : ℝ)^1024 ≤ (1250035442133261/1250000000000000 : ℝ)^4369 := by
      have hnat : (50006048978568004069 : ℕ)^1024*1250000000000000^4369 ≤ 1250035442133261^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006048978568004069 50000000000000000000 1250035442133261 1250000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035442133261/1250000000000000 : ℝ)) (X := (50006048978568004069/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044765423746498837/100000000000000000000 : ℝ) ≤ (2500262256469243/2500000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (100044765423746498837/100000000000000000000 : ℝ)^1024 ≤ (2500262256469243/2500000000000000 : ℝ)^4369 := by
      have hnat : (100044765423746498837 : ℕ)^1024*2500000000000000^4369 ≤ 2500262256469243^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044765423746498837 100000000000000000000 2500262256469243 2500000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500262256469243/2500000000000000 : ℝ)) (X := (100044765423746498837/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127419777823655923/3125000000000000000 : ℝ) ≤ (625113407167991/625000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (3127419777823655923/3125000000000000000 : ℝ)^1024 ≤ (625113407167991/625000000000000 : ℝ)^4369 := by
      have hnat : (3127419777823655923 : ℕ)^1024*625000000000000^4369 ≤ 625113407167991^4369*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127419777823655923 3125000000000000000 625113407167991 625000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625113407167991/625000000000000 : ℝ)) (X := (3127419777823655923/3125000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6048978568004069/100000000000000000000 : ℝ) ≤ ((6991984054446866951/6993750000000000000 : ℝ)+2*(191372202721/139875000000000 : ℝ)*(1283/12500 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (6991984054446866951/6993750000000000000 : ℝ)+2*(191372202721/139875000000000 : ℝ)*(1283/12500 : ℝ)=(1250035442133261/1250000000000000 : ℝ) by norm_num, show 1+2*(6048978568004069/100000000000000000000 : ℝ)=(50006048978568004069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2419777823655923/6250000000000000000 : ℝ)+(6048978568004069/100000000000000000000 : ℝ) ≤ ((6991984054446866951/6993750000000000000 : ℝ)+(191372202721/139875000000000 : ℝ)*((15859/100000 : ℝ)+(1283/12500 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (6991984054446866951/6993750000000000000 : ℝ)+(191372202721/139875000000000 : ℝ)*((15859/100000 : ℝ)+(1283/12500 : ℝ))=(2500262256469243/2500000000000000 : ℝ) by norm_num, show 1+(2419777823655923/6250000000000000000 : ℝ)+(6048978568004069/100000000000000000000 : ℝ)=(100044765423746498837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2419777823655923/6250000000000000000 : ℝ) ≤ ((6991984054446866951/6993750000000000000 : ℝ)+2*(191372202721/139875000000000 : ℝ)*(15859/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (6991984054446866951/6993750000000000000 : ℝ)+2*(191372202721/139875000000000 : ℝ)*(15859/100000 : ℝ)=(625113407167991/625000000000000 : ℝ) by norm_num, show 1+2*(2419777823655923/6250000000000000000 : ℝ)=(3127419777823655923/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6991984054446866951/6993750000000000000 : ℝ)*(X 1 0+X 2 0)+(191372202721/139875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (1283/12500 : ℝ)) (hi := (15859/100000 : ℝ)) (c := (6991984054446866951/6993750000000000000 : ℝ)) (alpha := (191372202721/139875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6991984054446866951/6993750000000000000 : ℝ)*(X 0 1+X 2 1)+(191372202721/139875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (1283/12500 : ℝ)) (hi := (15859/100000 : ℝ)) (c := (6991984054446866951/6993750000000000000 : ℝ)) (alpha := (191372202721/139875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6991984054446866951/6993750000000000000 : ℝ)*(X 0 2+X 1 2)+(191372202721/139875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (1283/12500 : ℝ)) (hi := (15859/100000 : ℝ)) (c := (6991984054446866951/6993750000000000000 : ℝ)) (alpha := (191372202721/139875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-397094037/2000000000 : ℝ)*X 0 0+(5419242103/10000000000 : ℝ)*X 0 1+(2618599997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675153183/5000000000 : ℝ)*X 1 0+(-6494887/31250000 : ℝ)*X 1 1+(5237199913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66878829/125000000 : ℝ)*X 2 0+(5237200017/10000000000 : ℝ)*X 2 1+(-2078363763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154213621/5000000000 : ℝ)*X 0 0+(2058455491/5000000000 : ℝ)*X 0 1+(4507989069/10000000000 : ℝ)*X 0 2+(2154213621/5000000000 : ℝ)*X 1 0+(2058455491/5000000000 : ℝ)*X 1 1+(4507989069/10000000000 : ℝ)*X 1 2+(2154213621/5000000000 : ℝ)*X 2 0+(2058455491/5000000000 : ℝ)*X 2 1+(4507989069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-198548657/1000000000 : ℝ)*X 0 0+(5237932677/10000000000 : ℝ)*X 0 1+(5418504961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303070573/10000000000 : ℝ)*X 1 0+(-1897058281/10000000000 : ℝ)*X 1 1+(5418505229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303071333/10000000000 : ℝ)*X 2 0+(169328269/312500000 : ℝ)*X 2 1+(-118566131/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308462673/10000000000 : ℝ)*X 0 0+(4506414763/10000000000 : ℝ)*X 0 1+(823698703/2000000000 : ℝ)*X 0 2+(4308462673/10000000000 : ℝ)*X 1 0+(4506414763/10000000000 : ℝ)*X 1 1+(823698703/2000000000 : ℝ)*X 1 2+(4308462673/10000000000 : ℝ)*X 2 0+(4506414763/10000000000 : ℝ)*X 2 1+(823698703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86750438714039879893771841/29140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161096297/25000000000000 : ℝ)*(base19) + (530498591/100000000000000 : ℝ)*(base23) + (14802223/20000000000000 : ℝ)*(upper3) + (7132771/20000000000000 : ℝ)*(upper4) + (53152337/50000000000000 : ℝ)*(upper5) + (1006287049423117/25000000000000 : ℝ)*(major0) + (1006287049423117/25000000000000 : ℝ)*(major1) + (1006287049423117/25000000000000 : ℝ)*(major2) + (43945945818203/800000000000 : ℝ)*(sp0) + (1373313243573529/25000000000000 : ℝ)*(sp1) + (686656636022589/12500000000000 : ℝ)*(sp2) + (255703854135861/10000000000000 : ℝ)*(sp3) + (10391403929/100000000000000 : ℝ)*(sp4) + (4136115053/100000000000000 : ℝ)*(sp7) + (19976895917763/781250000000 : ℝ)*(f.failure) + (686656702334913/12500000000000 : ℝ)*(f.sum) + (1938634764709/874218750000000000000000000 : ℝ)*base66 + (674998070323212517/174843750000000000000000000000000 : ℝ)*base67 + (1492712410549306267/174843750000000000000000000000000 : ℝ)*base69 + (682388921338037483/174843750000000000000000000000000 : ℝ)*base72 + (133269062115187/27975000000000000000000000000 : ℝ)*base73 + (3254460347535087517/174843750000000000000000000000000 : ℝ)*base75 + (1498864248553212517/174843750000000000000000000000000 : ℝ)*base77 + (2843922454546025017/174843750000000000000000000000000 : ℝ)*base79 + (212962588512937/27975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (56311/78125000000000000000 : ℝ)*base89 + (56311/78125000000000000000 : ℝ)*base91 + (56311/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3825931263672305357856493/3642578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1993697807/100000000000000 : ℝ)*(base19) + (2929618351/100000000000000 : ℝ)*(base23) + (66323341/20000000000000 : ℝ)*(upper3) + (10780331/100000000000000 : ℝ)*(lower4) + (1739911/1000000000000 : ℝ)*(upper5) + (1014474561440173/25000000000000 : ℝ)*(major0) + (1014474561440173/25000000000000 : ℝ)*(major1) + (1014474561440173/25000000000000 : ℝ)*(major2) + (40275263123/100000000000000 : ℝ)*(sp1) + (13491294807/25000000000000 : ℝ)*(sp2) + (1384487190886799/25000000000000 : ℝ)*(sp4) + (5537906494586267/100000000000000 : ℝ)*(sp5) + (5537891868749617/100000000000000 : ℝ)*(sp6) + (80557740405093/3125000000000 : ℝ)*(sp7) + (80557740405093/3125000000000 : ℝ)*(f.failure) + (1384487190886799/25000000000000 : ℝ)*(f.sum) + (18260641835509/3496875000000000000000000000 : ℝ)*base66 + (452696664439052477/174843750000000000000000000000000 : ℝ)*base68 + (1040818868861552477/174843750000000000000000000000000 : ℝ)*base70 + (2962949098152021227/174843750000000000000000000000000 : ℝ)*base72 + (83279702307253/27975000000000000000000000000 : ℝ)*base73 + (39866215304364977/174843750000000000000000000000000 : ℝ)*base76 + (1270284728312646227/174843750000000000000000000000000 : ℝ)*base78 + (1649022767576552477/174843750000000000000000000000000 : ℝ)*base80 + (54292397637293/6993750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6805321/312500000000000000000 : ℝ)*base89 + (6805321/312500000000000000000 : ℝ)*base91 + (6805321/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1410_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14957/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1410_s4_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-79458827/400000000 : ℝ)*x 0 + (5410772437/10000000000 : ℝ)*x 1 + (2622505637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79458827/400000000 : ℝ)^2185 ≤ (12113490028561/100000000000000 : ℝ)^1673 := by
    have hnat : (79458827 : ℕ)^2185*100000000000000^1673 ≤ 12113490028561^1673*400000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79458827 400000000 12113490028561 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410772437/10000000000 : ℝ)^2185 ≤ (5604498188911/12500000000000 : ℝ)^1673 := by
    have hnat : (5410772437 : ℕ)^2185*12500000000000^1673 ≤ 5604498188911^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410772437 10000000000 5604498188911 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622505637/5000000000 : ℝ)^2185 ≤ (21525262222571/50000000000000 : ℝ)^1673 := by
    have hnat : (2622505637 : ℕ)^2185*50000000000000^1673 ≤ 21525262222571^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622505637 5000000000 21525262222571 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79458827/400000000 : ℝ), (5410772437/10000000000 : ℝ), (2622505637/5000000000 : ℝ)] ![(12113490028561/100000000000000 : ℝ), (5604498188911/12500000000000 : ℝ), (21525262222571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79458827/400000000 : ℝ)|^2185 ≤ (12113490028561/100000000000000 : ℝ)^1673
        have hw : |(-79458827/400000000 : ℝ)|=(79458827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410772437/10000000000 : ℝ)|^2185 ≤ (5604498188911/12500000000000 : ℝ)^1673
        have hw : |(5410772437/10000000000 : ℝ)|=(5410772437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622505637/5000000000 : ℝ)|^2185 ≤ (21525262222571/50000000000000 : ℝ)^1673
        have hw : |(2622505637/5000000000 : ℝ)|=(2622505637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534812557/1000000000 : ℝ)*x 0 + (-1035452281/5000000000 : ℝ)*x 1 + (5245011613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534812557/1000000000 : ℝ)^2185 ≤ (2759950090617/6250000000000 : ℝ)^1673 := by
    have hnat : (534812557 : ℕ)^2185*6250000000000^1673 ≤ 2759950090617^1673*1000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534812557 1000000000 2759950090617 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035452281/5000000000 : ℝ)^2185 ≤ (399695952027/3125000000000 : ℝ)^1673 := by
    have hnat : (1035452281 : ℕ)^2185*3125000000000^1673 ≤ 399695952027^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035452281 5000000000 399695952027 3125000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245011613/10000000000 : ℝ)^2185 ≤ (21525264039581/50000000000000 : ℝ)^1673 := by
    have hnat : (5245011613 : ℕ)^2185*50000000000000^1673 ≤ 21525264039581^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245011613 10000000000 21525264039581 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534812557/1000000000 : ℝ), (-1035452281/5000000000 : ℝ), (5245011613/10000000000 : ℝ)] ![(2759950090617/6250000000000 : ℝ), (399695952027/3125000000000 : ℝ), (21525264039581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534812557/1000000000 : ℝ)|^2185 ≤ (2759950090617/6250000000000 : ℝ)^1673
        have hw : |(534812557/1000000000 : ℝ)|=(534812557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035452281/5000000000 : ℝ)|^2185 ≤ (399695952027/3125000000000 : ℝ)^1673
        have hw : |(-1035452281/5000000000 : ℝ)|=(1035452281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245011613/10000000000 : ℝ)|^2185 ≤ (21525264039581/50000000000000 : ℝ)^1673
        have hw : |(5245011613/10000000000 : ℝ)|=(5245011613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348125731/10000000000 : ℝ)*x 0 + (5245010903/10000000000 : ℝ)*x 1 + (-2070905289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348125731/10000000000 : ℝ)^2185 ≤ (44159203186077/100000000000000 : ℝ)^1673 := by
    have hnat : (5348125731 : ℕ)^2185*100000000000000^1673 ≤ 44159203186077^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348125731 10000000000 44159203186077 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245010903/10000000000 : ℝ)^2185 ≤ (43050520468089/100000000000000 : ℝ)^1673 := by
    have hnat : (5245010903 : ℕ)^2185*100000000000000^1673 ≤ 43050520468089^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245010903 10000000000 43050520468089 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070905289/10000000000 : ℝ)^2185 ≤ (511611053163/4000000000000 : ℝ)^1673 := by
    have hnat : (2070905289 : ℕ)^2185*4000000000000^1673 ≤ 511611053163^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070905289 10000000000 511611053163 4000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348125731/10000000000 : ℝ), (5245010903/10000000000 : ℝ), (-2070905289/10000000000 : ℝ)] ![(44159203186077/100000000000000 : ℝ), (43050520468089/100000000000000 : ℝ), (511611053163/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348125731/10000000000 : ℝ)|^2185 ≤ (44159203186077/100000000000000 : ℝ)^1673
        have hw : |(5348125731/10000000000 : ℝ)|=(5348125731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245010903/10000000000 : ℝ)|^2185 ≤ (43050520468089/100000000000000 : ℝ)^1673
        have hw : |(5245010903/10000000000 : ℝ)|=(5245010903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070905289/10000000000 : ℝ)|^2185 ≤ (511611053163/4000000000000 : ℝ)^1673
        have hw : |(-2070905289/10000000000 : ℝ)|=(2070905289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4309038833/10000000000 : ℝ)*x 0 + (516790687/1250000000 : ℝ)*x 1 + (4490426923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309038833/10000000000 : ℝ)^2185 ≤ (33303299514753/100000000000000 : ℝ)^1673 := by
    have hnat : (4309038833 : ℕ)^2185*100000000000000^1673 ≤ 33303299514753^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309038833 10000000000 33303299514753 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516790687/1250000000 : ℝ)^2185 ≤ (31550792881593/100000000000000 : ℝ)^1673 := by
    have hnat : (516790687 : ℕ)^2185*100000000000000^1673 ≤ 31550792881593^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516790687 1250000000 31550792881593 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490426923/10000000000 : ℝ)^2185 ≤ (35145907597369/100000000000000 : ℝ)^1673 := by
    have hnat : (4490426923 : ℕ)^2185*100000000000000^1673 ≤ 35145907597369^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490426923 10000000000 35145907597369 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309038833/10000000000 : ℝ), (516790687/1250000000 : ℝ), (4490426923/10000000000 : ℝ)] ![(33303299514753/100000000000000 : ℝ), (31550792881593/100000000000000 : ℝ), (35145907597369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309038833/10000000000 : ℝ)|^2185 ≤ (33303299514753/100000000000000 : ℝ)^1673
        have hw : |(4309038833/10000000000 : ℝ)|=(4309038833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516790687/1250000000 : ℝ)|^2185 ≤ (31550792881593/100000000000000 : ℝ)^1673
        have hw : |(516790687/1250000000 : ℝ)|=(516790687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490426923/10000000000 : ℝ)|^2185 ≤ (35145907597369/100000000000000 : ℝ)^1673
        have hw : |(4490426923/10000000000 : ℝ)|=(4490426923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986482931/10000000000 : ℝ)*x 0 + (1311404761/2500000000 : ℝ)*x 1 + (2705080693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986482931/10000000000 : ℝ)^2185 ≤ (6056793818997/50000000000000 : ℝ)^1673 := by
    have hnat : (1986482931 : ℕ)^2185*50000000000000^1673 ≤ 6056793818997^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986482931 10000000000 6056793818997 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311404761/2500000000 : ℝ)^2185 ≤ (21528519873039/50000000000000 : ℝ)^1673 := by
    have hnat : (1311404761 : ℕ)^2185*50000000000000^1673 ≤ 21528519873039^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311404761 2500000000 21528519873039 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705080693/5000000000 : ℝ)^2185 ≤ (44829372596821/100000000000000 : ℝ)^1673 := by
    have hnat : (2705080693 : ℕ)^2185*100000000000000^1673 ≤ 44829372596821^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705080693 5000000000 44829372596821 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986482931/10000000000 : ℝ), (1311404761/2500000000 : ℝ), (2705080693/5000000000 : ℝ)] ![(6056793818997/50000000000000 : ℝ), (21528519873039/50000000000000 : ℝ), (44829372596821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986482931/10000000000 : ℝ)|^2185 ≤ (6056793818997/50000000000000 : ℝ)^1673
        have hw : |(-1986482931/10000000000 : ℝ)|=(1986482931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311404761/2500000000 : ℝ)|^2185 ≤ (21528519873039/50000000000000 : ℝ)^1673
        have hw : |(1311404761/2500000000 : ℝ)|=(1311404761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705080693/5000000000 : ℝ)|^2185 ≤ (44829372596821/100000000000000 : ℝ)^1673
        have hw : |(2705080693/5000000000 : ℝ)|=(2705080693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305114399/10000000000 : ℝ)*x 0 + (-238219273/1250000000 : ℝ)*x 1 + (2705080657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305114399/10000000000 : ℝ)^2185 ≤ (21847972964679/50000000000000 : ℝ)^1673 := by
    have hnat : (5305114399 : ℕ)^2185*50000000000000^1673 ≤ 21847972964679^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305114399 10000000000 21847972964679 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238219273/1250000000 : ℝ)^2185 ≤ (11474682236863/100000000000000 : ℝ)^1673 := by
    have hnat : (238219273 : ℕ)^2185*100000000000000^1673 ≤ 11474682236863^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238219273 1250000000 11474682236863 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705080657/5000000000 : ℝ)^2185 ≤ (11207342954409/25000000000000 : ℝ)^1673 := by
    have hnat : (2705080657 : ℕ)^2185*25000000000000^1673 ≤ 11207342954409^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705080657 5000000000 11207342954409 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305114399/10000000000 : ℝ), (-238219273/1250000000 : ℝ), (2705080657/5000000000 : ℝ)] ![(21847972964679/50000000000000 : ℝ), (11474682236863/100000000000000 : ℝ), (11207342954409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305114399/10000000000 : ℝ)|^2185 ≤ (21847972964679/50000000000000 : ℝ)^1673
        have hw : |(5305114399/10000000000 : ℝ)|=(5305114399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238219273/1250000000 : ℝ)|^2185 ≤ (11474682236863/100000000000000 : ℝ)^1673
        have hw : |(-238219273/1250000000 : ℝ)|=(238219273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705080657/5000000000 : ℝ)|^2185 ≤ (11207342954409/25000000000000 : ℝ)^1673
        have hw : |(2705080657/5000000000 : ℝ)|=(2705080657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305114407/10000000000 : ℝ)*x 0 + (676270169/1250000000 : ℝ)*x 1 + (-1905754121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305114407/10000000000 : ℝ)^2185 ≤ (5461993251927/12500000000000 : ℝ)^1673 := by
    have hnat : (5305114407 : ℕ)^2185*12500000000000^1673 ≤ 5461993251927^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305114407 10000000000 5461993251927 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676270169/1250000000 : ℝ)^2185 ≤ (44829372228873/100000000000000 : ℝ)^1673 := by
    have hnat : (676270169 : ℕ)^2185*100000000000000^1673 ≤ 44829372228873^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676270169 1250000000 44829372228873 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1905754121/10000000000 : ℝ)^2185 ≤ (11474681741447/100000000000000 : ℝ)^1673 := by
    have hnat : (1905754121 : ℕ)^2185*100000000000000^1673 ≤ 11474681741447^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905754121 10000000000 11474681741447 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305114407/10000000000 : ℝ), (676270169/1250000000 : ℝ), (-1905754121/10000000000 : ℝ)] ![(5461993251927/12500000000000 : ℝ), (44829372228873/100000000000000 : ℝ), (11474681741447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305114407/10000000000 : ℝ)|^2185 ≤ (5461993251927/12500000000000 : ℝ)^1673
        have hw : |(5305114407/10000000000 : ℝ)|=(5305114407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676270169/1250000000 : ℝ)|^2185 ≤ (44829372228873/100000000000000 : ℝ)^1673
        have hw : |(676270169/1250000000 : ℝ)|=(676270169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1905754121/10000000000 : ℝ)|^2185 ≤ (11474681741447/100000000000000 : ℝ)^1673
        have hw : |(-1905754121/10000000000 : ℝ)|=(1905754121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s4_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2154532927/5000000000 : ℝ)*x 0 + (224456053/500000000 : ℝ)*x 1 + (4135637309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154532927/5000000000 : ℝ)^2185 ≤ (6660714452879/20000000000000 : ℝ)^1673 := by
    have hnat : (2154532927 : ℕ)^2185*20000000000000^1673 ≤ 6660714452879^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154532927 5000000000 6660714452879 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224456053/500000000 : ℝ)^2185 ≤ (7026511890451/20000000000000 : ℝ)^1673 := by
    have hnat : (224456053 : ℕ)^2185*20000000000000^1673 ≤ 7026511890451^1673*500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224456053 500000000 7026511890451 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135637309/10000000000 : ℝ)^2185 ≤ (7890967063949/25000000000000 : ℝ)^1673 := by
    have hnat : (4135637309 : ℕ)^2185*25000000000000^1673 ≤ 7890967063949^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135637309 10000000000 7890967063949 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154532927/5000000000 : ℝ), (224456053/500000000 : ℝ), (4135637309/10000000000 : ℝ)] ![(6660714452879/20000000000000 : ℝ), (7026511890451/20000000000000 : ℝ), (7890967063949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154532927/5000000000 : ℝ)|^2185 ≤ (6660714452879/20000000000000 : ℝ)^1673
        have hw : |(2154532927/5000000000 : ℝ)|=(2154532927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224456053/500000000 : ℝ)|^2185 ≤ (7026511890451/20000000000000 : ℝ)^1673
        have hw : |(224456053/500000000 : ℝ)|=(224456053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135637309/10000000000 : ℝ)|^2185 ≤ (7890967063949/25000000000000 : ℝ)^1673
        have hw : |(4135637309/10000000000 : ℝ)|=(4135637309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (739/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11103/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (8458128178270519/100000000000000000000 : ℝ) := by
    have hpowers : (11103/100000 : ℝ)^4369 ≤ (8458128178270519/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11103 : ℕ)^4369*100000000000000000000^1024 ≤ 8458128178270519^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11103 100000 8458128178270519 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11103/100000 : ℝ)) (X := (8458128178270519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14957/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (7539286305067163/25000000000000000000 : ℝ) := by
    have hpowers : (14957/100000 : ℝ)^4369 ≤ (7539286305067163/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14957 : ℕ)^4369*25000000000000000000^1024 ≤ 7539286305067163^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14957 100000 7539286305067163 25000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14957/100000 : ℝ)) (X := (7539286305067163/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008458128178270519/50000000000000000000 : ℝ) ≤ (5000198227567863/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50008458128178270519/50000000000000000000 : ℝ)^1024 ≤ (5000198227567863/5000000000000000 : ℝ)^4369 := by
      have hnat : (50008458128178270519 : ℕ)^1024*5000000000000000^4369 ≤ 5000198227567863^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008458128178270519 50000000000000000000 5000198227567863 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000198227567863/5000000000000000 : ℝ)) (X := (50008458128178270519/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038615273398539171/100000000000000000000 : ℝ) ≤ (5000452462760921/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (100038615273398539171/100000000000000000000 : ℝ)^1024 ≤ (5000452462760921/5000000000000000 : ℝ)^4369 := by
      have hnat : (100038615273398539171 : ℕ)^1024*5000000000000000^4369 ≤ 5000452462760921^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038615273398539171 100000000000000000000 5000452462760921 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000452462760921/5000000000000000 : ℝ)) (X := (100038615273398539171/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507539286305067163/12500000000000000000 : ℝ) ≤ (5000706697953979/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (12507539286305067163/12500000000000000000 : ℝ)^1024 ≤ (5000706697953979/5000000000000000 : ℝ)^4369 := by
      have hnat : (12507539286305067163 : ℕ)^1024*5000000000000000^4369 ≤ 5000706697953979^4369*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507539286305067163 12500000000000000000 5000706697953979 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000706697953979/5000000000000000 : ℝ)) (X := (12507539286305067163/12500000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8458128178270519/100000000000000000000 : ℝ) ≤ ((9632559211174749027/9635000000000000000 : ℝ)+2*(127117596529/96350000000000 : ℝ)*(11103/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (9632559211174749027/9635000000000000000 : ℝ)+2*(127117596529/96350000000000 : ℝ)*(11103/100000 : ℝ)=(5000198227567863/5000000000000000 : ℝ) by norm_num, show 1+2*(8458128178270519/100000000000000000000 : ℝ)=(50008458128178270519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7539286305067163/25000000000000000000 : ℝ)+(8458128178270519/100000000000000000000 : ℝ) ≤ ((9632559211174749027/9635000000000000000 : ℝ)+(127117596529/96350000000000 : ℝ)*((14957/100000 : ℝ)+(11103/100000 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (9632559211174749027/9635000000000000000 : ℝ)+(127117596529/96350000000000 : ℝ)*((14957/100000 : ℝ)+(11103/100000 : ℝ))=(5000452462760921/5000000000000000 : ℝ) by norm_num, show 1+(7539286305067163/25000000000000000000 : ℝ)+(8458128178270519/100000000000000000000 : ℝ)=(100038615273398539171/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7539286305067163/25000000000000000000 : ℝ) ≤ ((9632559211174749027/9635000000000000000 : ℝ)+2*(127117596529/96350000000000 : ℝ)*(14957/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (9632559211174749027/9635000000000000000 : ℝ)+2*(127117596529/96350000000000 : ℝ)*(14957/100000 : ℝ)=(5000706697953979/5000000000000000 : ℝ) by norm_num, show 1+2*(7539286305067163/25000000000000000000 : ℝ)=(12507539286305067163/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9632559211174749027/9635000000000000000 : ℝ)*(X 1 0+X 2 0)+(127117596529/96350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (14957/100000 : ℝ)) (c := (9632559211174749027/9635000000000000000 : ℝ)) (alpha := (127117596529/96350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9632559211174749027/9635000000000000000 : ℝ)*(X 0 1+X 2 1)+(127117596529/96350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (14957/100000 : ℝ)) (c := (9632559211174749027/9635000000000000000 : ℝ)) (alpha := (127117596529/96350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9632559211174749027/9635000000000000000 : ℝ)*(X 0 2+X 1 2)+(127117596529/96350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (14957/100000 : ℝ)) (c := (9632559211174749027/9635000000000000000 : ℝ)) (alpha := (127117596529/96350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-79458827/400000000 : ℝ)*X 0 0+(5410772437/10000000000 : ℝ)*X 0 1+(2622505637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534812557/1000000000 : ℝ)*X 1 0+(-1035452281/5000000000 : ℝ)*X 1 1+(5245011613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348125731/10000000000 : ℝ)*X 2 0+(5245010903/10000000000 : ℝ)*X 2 1+(-2070905289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309038833/10000000000 : ℝ)*X 0 0+(516790687/1250000000 : ℝ)*X 0 1+(4490426923/10000000000 : ℝ)*X 0 2+(4309038833/10000000000 : ℝ)*X 1 0+(516790687/1250000000 : ℝ)*X 1 1+(4490426923/10000000000 : ℝ)*X 1 2+(4309038833/10000000000 : ℝ)*X 2 0+(516790687/1250000000 : ℝ)*X 2 1+(4490426923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1986482931/10000000000 : ℝ)*X 0 0+(1311404761/2500000000 : ℝ)*X 0 1+(2705080693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305114399/10000000000 : ℝ)*X 1 0+(-238219273/1250000000 : ℝ)*X 1 1+(2705080657/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305114407/10000000000 : ℝ)*X 2 0+(676270169/1250000000 : ℝ)*X 2 1+(-1905754121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2154532927/5000000000 : ℝ)*X 0 0+(224456053/500000000 : ℝ)*X 0 1+(4135637309/10000000000 : ℝ)*X 0 2+(2154532927/5000000000 : ℝ)*X 1 0+(224456053/500000000 : ℝ)*X 1 1+(4135637309/10000000000 : ℝ)*X 1 2+(2154532927/5000000000 : ℝ)*X 2 0+(224456053/500000000 : ℝ)*X 2 1+(4135637309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (946959597878257341975168129/60218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (541631199/100000000000000 : ℝ)*(base19) + (670369677/100000000000000 : ℝ)*(base23) + (8335821/20000000000000 : ℝ)*(upper2) + (182297/62500000000 : ℝ)*(upper3) + (1105126000202409/25000000000000 : ℝ)*(major0) + (1105126000202409/25000000000000 : ℝ)*(major1) + (1105126000202409/25000000000000 : ℝ)*(major2) + (6032798100423281/100000000000000 : ℝ)*(sp0) + (60328078755887/1000000000000 : ℝ)*(sp1) + (6032791482213867/100000000000000 : ℝ)*(sp2) + (1404095882716073/50000000000000 : ℝ)*(sp3) + (5158398309/50000000000000 : ℝ)*(sp4) + (3252927271/20000000000000 : ℝ)*(sp6) + (7294789619/100000000000000 : ℝ)*(sp7) + (702049765055441/25000000000000 : ℝ)*(f.failure) + (6032808417219899/100000000000000 : ℝ)*(f.sum) + (80681274531097/9635000000000000000000000000 : ℝ)*base66 + (1662797721039968957/240875000000000000000000000000000 : ℝ)*base68 + (887988362927718957/240875000000000000000000000000000 : ℝ)*base70 + (2587055497911593957/240875000000000000000000000000000 : ℝ)*base72 + (10257440282793/2408750000000000000000000000 : ℝ)*base74 + (352164468585968957/240875000000000000000000000000000 : ℝ)*base76 + (4321625100145843957/240875000000000000000000000000000 : ℝ)*base78 + (1751739120417031043/240875000000000000000000000000000 : ℝ)*base79 + (38532651966597/9635000000000000000000000000 : ℝ)*base82 + (5495877/2500000000000000000000 : ℝ)*base89 + (5495877/2500000000000000000000 : ℝ)*base91 + (5495877/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (844308336561223822759405713/120437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59303533/5000000000000 : ℝ)*(base19) + (357181801/25000000000000 : ℝ)*(base23) + (5689813/4000000000000 : ℝ)*(upper3) + (9518961/10000000000000 : ℝ)*(lower4) + (12835019/10000000000000 : ℝ)*(upper5) + (2226611239422373/50000000000000 : ℝ)*(major0) + (2226611239422373/50000000000000 : ℝ)*(major1) + (2226611239422373/50000000000000 : ℝ)*(major2) + (10850284779/50000000000000 : ℝ)*(sp1) + (14184309527/50000000000000 : ℝ)*(sp2) + (6077460703691533/100000000000000 : ℝ)*(sp4) + (1519359454262829/25000000000000 : ℝ)*(sp5) + (243097236253811/4000000000000 : ℝ)*(sp6) + (282898402031981/10000000000000 : ℝ)*(sp7) + (282898402031981/10000000000000 : ℝ)*(f.failure) + (6077460703691533/100000000000000 : ℝ)*(f.sum) + (2950804948027/9635000000000000000000000000 : ℝ)*base66 + (3315366056745518929/481750000000000000000000000000000 : ℝ)*base68 + (246369480433518929/481750000000000000000000000000000 : ℝ)*base70 + (1078895556811518929/481750000000000000000000000000000 : ℝ)*base72 + (482530328013/150546875000000000000000000 : ℝ)*base74 + (5212499732328518929/481750000000000000000000000000000 : ℝ)*base76 + (1472127971157768929/481750000000000000000000000000000 : ℝ)*base78 + (9667794945011981071/481750000000000000000000000000000 : ℝ)*base79 + (7535541577447/9635000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2565743/1000000000000000000000 : ℝ)*base90 + (2565743/1000000000000000000000 : ℝ)*base92 + (2565743/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1410_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (739/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1410_s5_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986626889/10000000000 : ℝ)*x 0 + (5409413143/10000000000 : ℝ)*x 1 + (1049253483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986626889/10000000000 : ℝ)^2185 ≤ (6057367082209/50000000000000 : ℝ)^1673 := by
    have hnat : (1986626889 : ℕ)^2185*50000000000000^1673 ≤ 6057367082209^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986626889 10000000000 6057367082209 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409413143/10000000000 : ℝ)^2185 ≤ (44821275274781/100000000000000 : ℝ)^1673 := by
    have hnat : (5409413143 : ℕ)^2185*100000000000000^1673 ≤ 44821275274781^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409413143 10000000000 44821275274781 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049253483/2000000000 : ℝ)^2185 ≤ (2153199527243/5000000000000 : ℝ)^1673 := by
    have hnat : (1049253483 : ℕ)^2185*5000000000000^1673 ≤ 2153199527243^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049253483 2000000000 2153199527243 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986626889/10000000000 : ℝ), (5409413143/10000000000 : ℝ), (1049253483/2000000000 : ℝ)] ![(6057367082209/50000000000000 : ℝ), (44821275274781/100000000000000 : ℝ), (2153199527243/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986626889/10000000000 : ℝ)|^2185 ≤ (6057367082209/50000000000000 : ℝ)^1673
        have hw : |(-1986626889/10000000000 : ℝ)|=(1986626889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409413143/10000000000 : ℝ)|^2185 ≤ (44821275274781/100000000000000 : ℝ)^1673
        have hw : |(5409413143/10000000000 : ℝ)|=(5409413143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049253483/2000000000 : ℝ)|^2185 ≤ (2153199527243/5000000000000 : ℝ)^1673
        have hw : |(1049253483/2000000000 : ℝ)|=(1049253483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347774983/10000000000 : ℝ)*x 0 + (-2069703941/10000000000 : ℝ)*x 1 + (5246267593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347774983/10000000000 : ℝ)^2185 ≤ (44155420799053/100000000000000 : ℝ)^1673 := by
    have hnat : (5347774983 : ℕ)^2185*100000000000000^1673 ≤ 44155420799053^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347774983 10000000000 44155420799053 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069703941/10000000000 : ℝ)^2185 ≤ (1278058673771/10000000000000 : ℝ)^1673 := by
    have hnat : (2069703941 : ℕ)^2185*10000000000000^1673 ≤ 1278058673771^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069703941 10000000000 1278058673771 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246267593/10000000000 : ℝ)^2185 ≤ (5382999056641/12500000000000 : ℝ)^1673 := by
    have hnat : (5246267593 : ℕ)^2185*12500000000000^1673 ≤ 5382999056641^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246267593 10000000000 5382999056641 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347774983/10000000000 : ℝ), (-2069703941/10000000000 : ℝ), (5246267593/10000000000 : ℝ)] ![(44155420799053/100000000000000 : ℝ), (1278058673771/10000000000000 : ℝ), (5382999056641/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347774983/10000000000 : ℝ)|^2185 ≤ (44155420799053/100000000000000 : ℝ)^1673
        have hw : |(5347774983/10000000000 : ℝ)|=(5347774983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069703941/10000000000 : ℝ)|^2185 ≤ (1278058673771/10000000000000 : ℝ)^1673
        have hw : |(-2069703941/10000000000 : ℝ)|=(2069703941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246267593/10000000000 : ℝ)|^2185 ≤ (5382999056641/12500000000000 : ℝ)^1673
        have hw : |(5246267593/10000000000 : ℝ)|=(5246267593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069555009/2000000000 : ℝ)*x 0 + (5246267489/10000000000 : ℝ)*x 1 + (-2069703997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069555009/2000000000 : ℝ)^2185 ≤ (44155421467641/100000000000000 : ℝ)^1673 := by
    have hnat : (1069555009 : ℕ)^2185*100000000000000^1673 ≤ 44155421467641^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069555009 2000000000 44155421467641 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246267489/10000000000 : ℝ)^2185 ≤ (8612798267637/20000000000000 : ℝ)^1673 := by
    have hnat : (5246267489 : ℕ)^2185*20000000000000^1673 ≤ 8612798267637^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246267489 10000000000 8612798267637 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069703997/10000000000 : ℝ)^2185 ≤ (399393349667/3125000000000 : ℝ)^1673 := by
    have hnat : (2069703997 : ℕ)^2185*3125000000000^1673 ≤ 399393349667^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069703997 10000000000 399393349667 3125000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069555009/2000000000 : ℝ), (5246267489/10000000000 : ℝ), (-2069703997/10000000000 : ℝ)] ![(44155421467641/100000000000000 : ℝ), (8612798267637/20000000000000 : ℝ), (399393349667/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069555009/2000000000 : ℝ)|^2185 ≤ (44155421467641/100000000000000 : ℝ)^1673
        have hw : |(1069555009/2000000000 : ℝ)|=(1069555009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246267489/10000000000 : ℝ)|^2185 ≤ (8612798267637/20000000000000 : ℝ)^1673
        have hw : |(5246267489/10000000000 : ℝ)|=(5246267489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069703997/10000000000 : ℝ)|^2185 ≤ (399393349667/3125000000000 : ℝ)^1673
        have hw : |(-2069703997/10000000000 : ℝ)|=(2069703997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077283231/2500000000 : ℝ)*x 0 + (4137122777/10000000000 : ℝ)*x 1 + (224380301/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077283231/2500000000 : ℝ)^2185 ≤ (16652124635207/50000000000000 : ℝ)^1673 := by
    have hnat : (1077283231 : ℕ)^2185*50000000000000^1673 ≤ 16652124635207^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077283231 2500000000 16652124635207 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137122777/10000000000 : ℝ)^2185 ≤ (986833626643/3125000000000 : ℝ)^1673 := by
    have hnat : (4137122777 : ℕ)^2185*3125000000000^1673 ≤ 986833626643^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137122777 10000000000 986833626643 3125000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224380301/500000000 : ℝ)^2185 ≤ (35117074650783/100000000000000 : ℝ)^1673 := by
    have hnat : (224380301 : ℕ)^2185*100000000000000^1673 ≤ 35117074650783^1673*500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224380301 500000000 35117074650783 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077283231/2500000000 : ℝ), (4137122777/10000000000 : ℝ), (224380301/500000000 : ℝ)] ![(16652124635207/50000000000000 : ℝ), (986833626643/3125000000000 : ℝ), (35117074650783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077283231/2500000000 : ℝ)|^2185 ≤ (16652124635207/50000000000000 : ℝ)^1673
        have hw : |(1077283231/2500000000 : ℝ)|=(1077283231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137122777/10000000000 : ℝ)|^2185 ≤ (986833626643/3125000000000 : ℝ)^1673
        have hw : |(4137122777/10000000000 : ℝ)|=(4137122777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224380301/500000000 : ℝ)|^2185 ≤ (35117074650783/100000000000000 : ℝ)^1673
        have hw : |(224380301/500000000 : ℝ)|=(224380301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986638401/10000000000 : ℝ)*x 0 + (262342819/500000000 : ℝ)*x 1 + (270441059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986638401/10000000000 : ℝ)^2185 ≤ (3028706462669/25000000000000 : ℝ)^1673 := by
    have hnat : (1986638401 : ℕ)^2185*25000000000000^1673 ≤ 3028706462669^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986638401 10000000000 3028706462669 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262342819/500000000 : ℝ)^2185 ≤ (2153515235761/5000000000000 : ℝ)^1673 := by
    have hnat : (262342819 : ℕ)^2185*5000000000000^1673 ≤ 2153515235761^1673*500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262342819 500000000 2153515235761 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270441059/500000000 : ℝ)^2185 ≤ (11203717355891/25000000000000 : ℝ)^1673 := by
    have hnat : (270441059 : ℕ)^2185*25000000000000^1673 ≤ 11203717355891^1673*500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270441059 500000000 11203717355891 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986638401/10000000000 : ℝ), (262342819/500000000 : ℝ), (270441059/500000000 : ℝ)] ![(3028706462669/25000000000000 : ℝ), (2153515235761/5000000000000 : ℝ), (11203717355891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986638401/10000000000 : ℝ)|^2185 ≤ (3028706462669/25000000000000 : ℝ)^1673
        have hw : |(-1986638401/10000000000 : ℝ)|=(1986638401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262342819/500000000 : ℝ)|^2185 ≤ (2153515235761/5000000000000 : ℝ)^1673
        have hw : |(262342819/500000000 : ℝ)|=(262342819/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270441059/500000000 : ℝ)|^2185 ≤ (11203717355891/25000000000000 : ℝ)^1673
        have hw : |(270441059/500000000 : ℝ)|=(270441059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326360467/2500000000 : ℝ)*x 0 + (-1907150269/10000000000 : ℝ)*x 1 + (270441059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326360467/2500000000 : ℝ)^2185 ≤ (8739893726729/20000000000000 : ℝ)^1673 := by
    have hnat : (1326360467 : ℕ)^2185*20000000000000^1673 ≤ 8739893726729^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326360467 2500000000 8739893726729 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1907150269/10000000000 : ℝ)^2185 ≤ (11485661920293/100000000000000 : ℝ)^1673 := by
    have hnat : (1907150269 : ℕ)^2185*100000000000000^1673 ≤ 11485661920293^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907150269 10000000000 11485661920293 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270441059/500000000 : ℝ)^2185 ≤ (11203717355891/25000000000000 : ℝ)^1673 := by
    have hnat : (270441059 : ℕ)^2185*25000000000000^1673 ≤ 11203717355891^1673*500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270441059 500000000 11203717355891 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326360467/2500000000 : ℝ), (-1907150269/10000000000 : ℝ), (270441059/500000000 : ℝ)] ![(8739893726729/20000000000000 : ℝ), (11485661920293/100000000000000 : ℝ), (11203717355891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326360467/2500000000 : ℝ)|^2185 ≤ (8739893726729/20000000000000 : ℝ)^1673
        have hw : |(1326360467/2500000000 : ℝ)|=(1326360467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1907150269/10000000000 : ℝ)|^2185 ≤ (11485661920293/100000000000000 : ℝ)^1673
        have hw : |(-1907150269/10000000000 : ℝ)|=(1907150269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270441059/500000000 : ℝ)|^2185 ≤ (11203717355891/25000000000000 : ℝ)^1673
        have hw : |(270441059/500000000 : ℝ)|=(270441059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652720933/5000000000 : ℝ)*x 0 + (5408821183/10000000000 : ℝ)*x 1 + (-1907150269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652720933/5000000000 : ℝ)^2185 ≤ (4369946861213/10000000000000 : ℝ)^1673 := by
    have hnat : (2652720933 : ℕ)^2185*10000000000000^1673 ≤ 4369946861213^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652720933 5000000000 4369946861213 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408821183/10000000000 : ℝ)^2185 ≤ (44814869456027/100000000000000 : ℝ)^1673 := by
    have hnat : (5408821183 : ℕ)^2185*100000000000000^1673 ≤ 44814869456027^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408821183 10000000000 44814869456027 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1907150269/10000000000 : ℝ)^2185 ≤ (11485661920293/100000000000000 : ℝ)^1673 := by
    have hnat : (1907150269 : ℕ)^2185*100000000000000^1673 ≤ 11485661920293^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907150269 10000000000 11485661920293 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652720933/5000000000 : ℝ), (5408821183/10000000000 : ℝ), (-1907150269/10000000000 : ℝ)] ![(4369946861213/10000000000000 : ℝ), (44814869456027/100000000000000 : ℝ), (11485661920293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652720933/5000000000 : ℝ)|^2185 ≤ (4369946861213/10000000000000 : ℝ)^1673
        have hw : |(2652720933/5000000000 : ℝ)|=(2652720933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408821183/10000000000 : ℝ)|^2185 ≤ (44814869456027/100000000000000 : ℝ)^1673
        have hw : |(5408821183/10000000000 : ℝ)|=(5408821183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1907150269/10000000000 : ℝ)|^2185 ≤ (11485661920293/100000000000000 : ℝ)^1673
        have hw : |(-1907150269/10000000000 : ℝ)|=(1907150269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s5_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077289411/2500000000 : ℝ)*x 0 + (4486340957/10000000000 : ℝ)*x 1 + (4138394573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077289411/2500000000 : ℝ)^2185 ≤ (33304498795437/100000000000000 : ℝ)^1673 := by
    have hnat : (1077289411 : ℕ)^2185*100000000000000^1673 ≤ 33304498795437^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077289411 2500000000 33304498795437 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486340957/10000000000 : ℝ)^2185 ≤ (109700456313/312500000000 : ℝ)^1673 := by
    have hnat : (4486340957 : ℕ)^2185*312500000000^1673 ≤ 109700456313^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486340957 10000000000 109700456313 312500000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138394573/10000000000 : ℝ)^2185 ≤ (31591355166109/100000000000000 : ℝ)^1673 := by
    have hnat : (4138394573 : ℕ)^2185*100000000000000^1673 ≤ 31591355166109^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138394573 10000000000 31591355166109 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077289411/2500000000 : ℝ), (4486340957/10000000000 : ℝ), (4138394573/10000000000 : ℝ)] ![(33304498795437/100000000000000 : ℝ), (109700456313/312500000000 : ℝ), (31591355166109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077289411/2500000000 : ℝ)|^2185 ≤ (33304498795437/100000000000000 : ℝ)^1673
        have hw : |(1077289411/2500000000 : ℝ)|=(1077289411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486340957/10000000000 : ℝ)|^2185 ≤ (109700456313/312500000000 : ℝ)^1673
        have hw : |(4486340957/10000000000 : ℝ)|=(4486340957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138394573/10000000000 : ℝ)|^2185 ≤ (31591355166109/100000000000000 : ℝ)^1673
        have hw : |(4138394573/10000000000 : ℝ)|=(4138394573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (353/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (9010993494336929/100000000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^4369 ≤ (9010993494336929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11269 : ℕ)^4369*100000000000000000000^1024 ≤ 9010993494336929^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 9010993494336929 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (9010993494336929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (739/5000 : ℝ) ^ (4369/1024 : ℝ) ≤ (716591498775461/2500000000000000000 : ℝ) := by
    have hpowers : (739/5000 : ℝ)^4369 ≤ (716591498775461/2500000000000000000 : ℝ)^1024 := by
      have hnat : (739 : ℕ)^4369*2500000000000000000^1024 ≤ 716591498775461^1024*5000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        739 5000 716591498775461 2500000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (739/5000 : ℝ)) (X := (716591498775461/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009010993494336929/50000000000000000000 : ℝ) ≤ (1250052795953401/1250000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50009010993494336929/50000000000000000000 : ℝ)^1024 ≤ (1250052795953401/1250000000000000 : ℝ)^4369 := by
      have hnat : (50009010993494336929 : ℕ)^1024*1250000000000000^4369 ≤ 1250052795953401^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009010993494336929 50000000000000000000 1250052795953401 1250000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250052795953401/1250000000000000 : ℝ)) (X := (50009010993494336929/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037674653445355369/100000000000000000000 : ℝ) ≤ (2000176577168321/2000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (100037674653445355369/100000000000000000000 : ℝ)^1024 ≤ (2000176577168321/2000000000000000 : ℝ)^4369 := by
      have hnat : (100037674653445355369 : ℕ)^1024*2000000000000000^4369 ≤ 2000176577168321^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037674653445355369 100000000000000000000 2000176577168321 2000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000176577168321/2000000000000000 : ℝ)) (X := (100037674653445355369/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250716591498775461/1250000000000000000 : ℝ) ≤ (5000671702028001/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (1250716591498775461/1250000000000000000 : ℝ)^1024 ≤ (5000671702028001/5000000000000000 : ℝ)^4369 := by
      have hnat : (1250716591498775461 : ℕ)^1024*5000000000000000^4369 ≤ 5000671702028001^4369*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250716591498775461 1250000000000000000 5000671702028001 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000671702028001/5000000000000000 : ℝ)) (X := (1250716591498775461/1250000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9010993494336929/100000000000000000000 : ℝ) ≤ ((17550551886611523851/17555000000000000000 : ℝ)+2*(460518214397/351100000000000 : ℝ)*(11269/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (17550551886611523851/17555000000000000000 : ℝ)+2*(460518214397/351100000000000 : ℝ)*(11269/100000 : ℝ)=(1250052795953401/1250000000000000 : ℝ) by norm_num, show 1+2*(9010993494336929/100000000000000000000 : ℝ)=(50009010993494336929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(716591498775461/2500000000000000000 : ℝ)+(9010993494336929/100000000000000000000 : ℝ) ≤ ((17550551886611523851/17555000000000000000 : ℝ)+(460518214397/351100000000000 : ℝ)*((739/5000 : ℝ)+(11269/100000 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (17550551886611523851/17555000000000000000 : ℝ)+(460518214397/351100000000000 : ℝ)*((739/5000 : ℝ)+(11269/100000 : ℝ))=(2000176577168321/2000000000000000 : ℝ) by norm_num, show 1+(716591498775461/2500000000000000000 : ℝ)+(9010993494336929/100000000000000000000 : ℝ)=(100037674653445355369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(716591498775461/2500000000000000000 : ℝ) ≤ ((17550551886611523851/17555000000000000000 : ℝ)+2*(460518214397/351100000000000 : ℝ)*(739/5000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (17550551886611523851/17555000000000000000 : ℝ)+2*(460518214397/351100000000000 : ℝ)*(739/5000 : ℝ)=(5000671702028001/5000000000000000 : ℝ) by norm_num, show 1+2*(716591498775461/2500000000000000000 : ℝ)=(1250716591498775461/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17550551886611523851/17555000000000000000 : ℝ)*(X 1 0+X 2 0)+(460518214397/351100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (17550551886611523851/17555000000000000000 : ℝ)) (alpha := (460518214397/351100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17550551886611523851/17555000000000000000 : ℝ)*(X 0 1+X 2 1)+(460518214397/351100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (17550551886611523851/17555000000000000000 : ℝ)) (alpha := (460518214397/351100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17550551886611523851/17555000000000000000 : ℝ)*(X 0 2+X 1 2)+(460518214397/351100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (739/5000 : ℝ)) (c := (17550551886611523851/17555000000000000000 : ℝ)) (alpha := (460518214397/351100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986626889/10000000000 : ℝ)*X 0 0+(5409413143/10000000000 : ℝ)*X 0 1+(1049253483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347774983/10000000000 : ℝ)*X 1 0+(-2069703941/10000000000 : ℝ)*X 1 1+(5246267593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069555009/2000000000 : ℝ)*X 2 0+(5246267489/10000000000 : ℝ)*X 2 1+(-2069703997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077283231/2500000000 : ℝ)*X 0 0+(4137122777/10000000000 : ℝ)*X 0 1+(224380301/500000000 : ℝ)*X 0 2+(1077283231/2500000000 : ℝ)*X 1 0+(4137122777/10000000000 : ℝ)*X 1 1+(224380301/500000000 : ℝ)*X 1 2+(1077283231/2500000000 : ℝ)*X 2 0+(4137122777/10000000000 : ℝ)*X 2 1+(224380301/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1986638401/10000000000 : ℝ)*X 0 0+(262342819/500000000 : ℝ)*X 0 1+(270441059/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326360467/2500000000 : ℝ)*X 1 0+(-1907150269/10000000000 : ℝ)*X 1 1+(270441059/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652720933/5000000000 : ℝ)*X 2 0+(5408821183/10000000000 : ℝ)*X 2 1+(-1907150269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077289411/2500000000 : ℝ)*X 0 0+(4486340957/10000000000 : ℝ)*X 0 1+(4138394573/10000000000 : ℝ)*X 0 2+(1077289411/2500000000 : ℝ)*X 1 0+(4486340957/10000000000 : ℝ)*X 1 1+(4138394573/10000000000 : ℝ)*X 1 2+(1077289411/2500000000 : ℝ)*X 2 0+(4486340957/10000000000 : ℝ)*X 2 1+(4138394573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (487106928481726988691046701/54859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1669194877/100000000000000 : ℝ)*(base19) + (1627285877/100000000000000 : ℝ)*(base23) + (15103823/25000000000000 : ℝ)*(lower2) + (150566157/50000000000000 : ℝ)*(upper3) + (40120799/25000000000000 : ℝ)*(upper5) + (561425346906133/12500000000000 : ℝ)*(major0) + (561425346906133/12500000000000 : ℝ)*(major1) + (561425346906133/12500000000000 : ℝ)*(major2) + (1225905912345391/20000000000000 : ℝ)*(sp0) + (1532391223373207/25000000000000 : ℝ)*(sp1) + (6129564935401827/100000000000000 : ℝ)*(sp2) + (713304902877987/25000000000000 : ℝ)*(sp3) + (148003843/400000000000 : ℝ)*(sp4) + (19080325399/100000000000000 : ℝ)*(sp7) + (2853238691837347/100000000000000 : ℝ)*(f.failure) + (1225913312537541/20000000000000 : ℝ)*(f.sum) + (11196645997057/17555000000000000000000000000 : ℝ)*base66 + (2421633241912478183/219437500000000000000000000000000 : ℝ)*base67 + (1091187649475728183/219437500000000000000000000000000 : ℝ)*base69 + (2215595291718228183/219437500000000000000000000000000 : ℝ)*base71 + (44959181060903/17555000000000000000000000000 : ℝ)*base73 + (1108007663647334317/219437500000000000000000000000000 : ℝ)*base76 + (1686819975674415683/219437500000000000000000000000000 : ℝ)*base77 + (1824796631961353183/219437500000000000000000000000000 : ℝ)*base79 + (902615434833/4388750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (32615359/10000000000000000000000 : ℝ)*base89 + (32615359/10000000000000000000000 : ℝ)*base91 + (32615359/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203401563892263577495503/17555000000000000000000000000 : ℝ) := by norm_num
    linear_combination (986465897/50000000000000 : ℝ)*(base19) + (1068333109/50000000000000 : ℝ)*(base23) + (23700177/10000000000000 : ℝ)*(upper3) + (37588443/50000000000000 : ℝ)*(lower4) + (47520387/20000000000000 : ℝ)*(upper5) + (4524092627980487/100000000000000 : ℝ)*(major0) + (4524092627980487/100000000000000 : ℝ)*(major1) + (4524092627980487/100000000000000 : ℝ)*(major2) + (2057187751/5000000000000 : ℝ)*(sp1) + (220985799/500000000000 : ℝ)*(sp2) + (6174179402510521/100000000000000 : ℝ)*(sp4) + (6174136285823707/100000000000000 : ℝ)*(sp5) + (6174133068684503/100000000000000 : ℝ)*(sp6) + (1437002733616361/50000000000000 : ℝ)*(sp7) + (1437002733616361/50000000000000 : ℝ)*(f.failure) + (6174179402510521/100000000000000 : ℝ)*(f.sum) + (23926263298127/8777500000000000000000000000 : ℝ)*base65 + (2123077679693045437/1755500000000000000000000000000000 : ℝ)*base67 + (31036006295842954563/1755500000000000000000000000000000 : ℝ)*base70 + (7513362601658045437/1755500000000000000000000000000000 : ℝ)*base71 + (47389188730767/8777500000000000000000000000 : ℝ)*base73 + (39404731695712954563/1755500000000000000000000000000000 : ℝ)*base76 + (4954959639717045437/1755500000000000000000000000000000 : ℝ)*base77 + (21614785015036454563/1755500000000000000000000000000000 : ℝ)*base80 + (45103558190053/8777500000000000000000000000 : ℝ)*base82 + (22877117/5000000000000000000000 : ℝ)*base89 + (22877117/5000000000000000000000 : ℝ)*base91 + (22877117/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1410_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1410_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1410_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1410_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1410_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1410_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
