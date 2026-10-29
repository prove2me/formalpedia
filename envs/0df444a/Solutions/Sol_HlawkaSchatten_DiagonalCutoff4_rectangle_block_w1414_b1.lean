-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1414_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:30.488022+00:00
-- url     : https://prove2.me/submissions/3c9dceda-d73e-4f8e-8045-6d6af53ea4d0

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
theorem support_rectangle_w1414_s3_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982210253/10000000000 : ℝ)*x 0 + (54188277/100000000 : ℝ)*x 1 + (5237487253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982210253/10000000000 : ℝ)^2187 ≤ (6043358013373/50000000000000 : ℝ)^1675 := by
    have hnat : (1982210253 : ℕ)^2187*50000000000000^1675 ≤ 6043358013373^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982210253 10000000000 6043358013373 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54188277/100000000 : ℝ)^2187 ≤ (44933241640199/100000000000000 : ℝ)^1675 := by
    have hnat : (54188277 : ℕ)^2187*100000000000000^1675 ≤ 44933241640199^1675*100000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54188277 100000000 44933241640199 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237487253/10000000000 : ℝ)^2187 ≤ (10745010581363/25000000000000 : ℝ)^1675 := by
    have hnat : (5237487253 : ℕ)^2187*25000000000000^1675 ≤ 10745010581363^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237487253 10000000000 10745010581363 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982210253/10000000000 : ℝ), (54188277/100000000 : ℝ), (5237487253/10000000000 : ℝ)] ![(6043358013373/50000000000000 : ℝ), (44933241640199/100000000000000 : ℝ), (10745010581363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982210253/10000000000 : ℝ)|^2187 ≤ (6043358013373/50000000000000 : ℝ)^1675
        have hw : |(-1982210253/10000000000 : ℝ)|=(1982210253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54188277/100000000 : ℝ)|^2187 ≤ (44933241640199/100000000000000 : ℝ)^1675
        have hw : |(54188277/100000000 : ℝ)|=(54188277/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237487253/10000000000 : ℝ)|^2187 ≤ (10745010581363/25000000000000 : ℝ)^1675
        have hw : |(5237487253/10000000000 : ℝ)|=(5237487253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350173119/10000000000 : ℝ)*x 0 + (-2074738607/10000000000 : ℝ)*x 1 + (1047497433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350173119/10000000000 : ℝ)^2187 ≤ (44191382168927/100000000000000 : ℝ)^1675 := by
    have hnat : (5350173119 : ℕ)^2187*100000000000000^1675 ≤ 44191382168927^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350173119 10000000000 44191382168927 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074738607/10000000000 : ℝ)^2187 ≤ (6414288214919/50000000000000 : ℝ)^1675 := by
    have hnat : (2074738607 : ℕ)^2187*50000000000000^1675 ≤ 6414288214919^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074738607 10000000000 6414288214919 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047497433/2000000000 : ℝ)^2187 ≤ (42980041382563/100000000000000 : ℝ)^1675 := by
    have hnat : (1047497433 : ℕ)^2187*100000000000000^1675 ≤ 42980041382563^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047497433 2000000000 42980041382563 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350173119/10000000000 : ℝ), (-2074738607/10000000000 : ℝ), (1047497433/2000000000 : ℝ)] ![(44191382168927/100000000000000 : ℝ), (6414288214919/50000000000000 : ℝ), (42980041382563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350173119/10000000000 : ℝ)|^2187 ≤ (44191382168927/100000000000000 : ℝ)^1675
        have hw : |(5350173119/10000000000 : ℝ)|=(5350173119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074738607/10000000000 : ℝ)|^2187 ≤ (6414288214919/50000000000000 : ℝ)^1675
        have hw : |(-2074738607/10000000000 : ℝ)|=(2074738607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047497433/2000000000 : ℝ)|^2187 ≤ (42980041382563/100000000000000 : ℝ)^1675
        have hw : |(1047497433/2000000000 : ℝ)|=(1047497433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675086529/5000000000 : ℝ)*x 0 + (1047497457/2000000000 : ℝ)*x 1 + (-2074738531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675086529/5000000000 : ℝ)^2187 ≤ (44191381511067/100000000000000 : ℝ)^1675 := by
    have hnat : (2675086529 : ℕ)^2187*100000000000000^1675 ≤ 44191381511067^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675086529 5000000000 44191381511067 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047497457/2000000000 : ℝ)^2187 ≤ (268625266677/625000000000 : ℝ)^1675 := by
    have hnat : (1047497457 : ℕ)^2187*625000000000^1675 ≤ 268625266677^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047497457 2000000000 268625266677 625000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074738531/10000000000 : ℝ)^2187 ≤ (12828575816271/100000000000000 : ℝ)^1675 := by
    have hnat : (2074738531 : ℕ)^2187*100000000000000^1675 ≤ 12828575816271^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074738531 10000000000 12828575816271 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675086529/5000000000 : ℝ), (1047497457/2000000000 : ℝ), (-2074738531/10000000000 : ℝ)] ![(44191381511067/100000000000000 : ℝ), (268625266677/625000000000 : ℝ), (12828575816271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675086529/5000000000 : ℝ)|^2187 ≤ (44191381511067/100000000000000 : ℝ)^1675
        have hw : |(2675086529/5000000000 : ℝ)|=(2675086529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047497457/2000000000 : ℝ)|^2187 ≤ (268625266677/625000000000 : ℝ)^1675
        have hw : |(1047497457/2000000000 : ℝ)|=(1047497457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074738531/10000000000 : ℝ)|^2187 ≤ (12828575816271/100000000000000 : ℝ)^1675
        have hw : |(-2074738531/10000000000 : ℝ)|=(2074738531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4307434199/10000000000 : ℝ)*x 0 + (4116359279/10000000000 : ℝ)*x 1 + (563313037/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307434199/10000000000 : ℝ)^2187 ≤ (33297349649769/100000000000000 : ℝ)^1675 := by
    have hnat : (4307434199 : ℕ)^2187*100000000000000^1675 ≤ 33297349649769^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307434199 10000000000 33297349649769 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4116359279/10000000000 : ℝ)^2187 ≤ (7845505321817/25000000000000 : ℝ)^1675 := by
    have hnat : (4116359279 : ℕ)^2187*25000000000000^1675 ≤ 7845505321817^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116359279 10000000000 7845505321817 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563313037/1250000000 : ℝ)^2187 ≤ (4415078630091/12500000000000 : ℝ)^1675 := by
    have hnat : (563313037 : ℕ)^2187*12500000000000^1675 ≤ 4415078630091^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563313037 1250000000 4415078630091 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307434199/10000000000 : ℝ), (4116359279/10000000000 : ℝ), (563313037/1250000000 : ℝ)] ![(33297349649769/100000000000000 : ℝ), (7845505321817/25000000000000 : ℝ), (4415078630091/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307434199/10000000000 : ℝ)|^2187 ≤ (33297349649769/100000000000000 : ℝ)^1675
        have hw : |(4307434199/10000000000 : ℝ)|=(4307434199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4116359279/10000000000 : ℝ)|^2187 ≤ (7845505321817/25000000000000 : ℝ)^1675
        have hw : |(4116359279/10000000000 : ℝ)|=(4116359279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563313037/1250000000 : ℝ)|^2187 ≤ (4415078630091/12500000000000 : ℝ)^1675
        have hw : |(563313037/1250000000 : ℝ)|=(563313037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-991112979/5000000000 : ℝ)*x 0 + (5238215981/10000000000 : ℝ)*x 1 + (1083618987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991112979/5000000000 : ℝ)^2187 ≤ (755427566349/6250000000000 : ℝ)^1675 := by
    have hnat : (991112979 : ℕ)^2187*6250000000000^1675 ≤ 755427566349^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991112979 5000000000 755427566349 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238215981/10000000000 : ℝ)^2187 ≤ (42987850554117/100000000000000 : ℝ)^1675 := by
    have hnat : (5238215981 : ℕ)^2187*100000000000000^1675 ≤ 42987850554117^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238215981 10000000000 42987850554117 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083618987/2000000000 : ℝ)^2187 ≤ (11231327093067/25000000000000 : ℝ)^1675 := by
    have hnat : (1083618987 : ℕ)^2187*25000000000000^1675 ≤ 11231327093067^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083618987 2000000000 11231327093067 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-991112979/5000000000 : ℝ), (5238215981/10000000000 : ℝ), (1083618987/2000000000 : ℝ)] ![(755427566349/6250000000000 : ℝ), (42987850554117/100000000000000 : ℝ), (11231327093067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-991112979/5000000000 : ℝ)|^2187 ≤ (755427566349/6250000000000 : ℝ)^1675
        have hw : |(-991112979/5000000000 : ℝ)|=(991112979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238215981/10000000000 : ℝ)|^2187 ≤ (42987850554117/100000000000000 : ℝ)^1675
        have hw : |(5238215981/10000000000 : ℝ)|=(5238215981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083618987/2000000000 : ℝ)|^2187 ≤ (11231327093067/25000000000000 : ℝ)^1675
        have hw : |(1083618987/2000000000 : ℝ)|=(1083618987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303100127/10000000000 : ℝ)*x 0 + (-189413091/1000000000 : ℝ)*x 1 + (5418094943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303100127/10000000000 : ℝ)^2187 ≤ (21842201604523/50000000000000 : ℝ)^1675 := by
    have hnat : (5303100127 : ℕ)^2187*50000000000000^1675 ≤ 21842201604523^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303100127 10000000000 21842201604523 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189413091/1000000000 : ℝ)^2187 ≤ (11390288309271/100000000000000 : ℝ)^1675 := by
    have hnat : (189413091 : ℕ)^2187*100000000000000^1675 ≤ 11390288309271^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189413091 1000000000 11390288309271 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418094943/10000000000 : ℝ)^2187 ≤ (22462654229439/50000000000000 : ℝ)^1675 := by
    have hnat : (5418094943 : ℕ)^2187*50000000000000^1675 ≤ 22462654229439^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418094943 10000000000 22462654229439 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303100127/10000000000 : ℝ), (-189413091/1000000000 : ℝ), (5418094943/10000000000 : ℝ)] ![(21842201604523/50000000000000 : ℝ), (11390288309271/100000000000000 : ℝ), (22462654229439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303100127/10000000000 : ℝ)|^2187 ≤ (21842201604523/50000000000000 : ℝ)^1675
        have hw : |(5303100127/10000000000 : ℝ)|=(5303100127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189413091/1000000000 : ℝ)|^2187 ≤ (11390288309271/100000000000000 : ℝ)^1675
        have hw : |(-189413091/1000000000 : ℝ)|=(189413091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418094943/10000000000 : ℝ)|^2187 ≤ (22462654229439/50000000000000 : ℝ)^1675
        have hw : |(5418094943/10000000000 : ℝ)|=(5418094943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662887497/1250000000 : ℝ)*x 0 + (2709047559/5000000000 : ℝ)*x 1 + (-473532719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662887497/1250000000 : ℝ)^2187 ≤ (21842200792483/50000000000000 : ℝ)^1675 := by
    have hnat : (662887497 : ℕ)^2187*50000000000000^1675 ≤ 21842200792483^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662887497 1250000000 21842200792483 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709047559/5000000000 : ℝ)^2187 ≤ (44925310353473/100000000000000 : ℝ)^1675 := by
    have hnat : (2709047559 : ℕ)^2187*100000000000000^1675 ≤ 44925310353473^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709047559 5000000000 44925310353473 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473532719/2500000000 : ℝ)^2187 ≤ (2847572010579/25000000000000 : ℝ)^1675 := by
    have hnat : (473532719 : ℕ)^2187*25000000000000^1675 ≤ 2847572010579^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473532719 2500000000 2847572010579 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662887497/1250000000 : ℝ), (2709047559/5000000000 : ℝ), (-473532719/2500000000 : ℝ)] ![(21842200792483/50000000000000 : ℝ), (44925310353473/100000000000000 : ℝ), (2847572010579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662887497/1250000000 : ℝ)|^2187 ≤ (21842200792483/50000000000000 : ℝ)^1675
        have hw : |(662887497/1250000000 : ℝ)|=(662887497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709047559/5000000000 : ℝ)|^2187 ≤ (44925310353473/100000000000000 : ℝ)^1675
        have hw : |(2709047559/5000000000 : ℝ)|=(2709047559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-473532719/2500000000 : ℝ)|^2187 ≤ (2847572010579/25000000000000 : ℝ)^1675
        have hw : |(-473532719/2500000000 : ℝ)|=(473532719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s3_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (538433537/1250000000 : ℝ)*x 0 + (4504936787/10000000000 : ℝ)*x 1 + (4117936031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538433537/1250000000 : ℝ)^2187 ≤ (33297693794941/100000000000000 : ℝ)^1675 := by
    have hnat : (538433537 : ℕ)^2187*100000000000000^1675 ≤ 33297693794941^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538433537 1250000000 33297693794941 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504936787/10000000000 : ℝ)^2187 ≤ (7060917769729/20000000000000 : ℝ)^1675 := by
    have hnat : (4504936787 : ℕ)^2187*20000000000000^1675 ≤ 7060917769729^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504936787 10000000000 7060917769729 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4117936031/10000000000 : ℝ)^2187 ≤ (1255908693563/4000000000000 : ℝ)^1675 := by
    have hnat : (4117936031 : ℕ)^2187*4000000000000^1675 ≤ 1255908693563^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117936031 10000000000 1255908693563 4000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538433537/1250000000 : ℝ), (4504936787/10000000000 : ℝ), (4117936031/10000000000 : ℝ)] ![(33297693794941/100000000000000 : ℝ), (7060917769729/20000000000000 : ℝ), (1255908693563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538433537/1250000000 : ℝ)|^2187 ≤ (33297693794941/100000000000000 : ℝ)^1675
        have hw : |(538433537/1250000000 : ℝ)|=(538433537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504936787/10000000000 : ℝ)|^2187 ≤ (7060917769729/20000000000000 : ℝ)^1675
        have hw : |(4504936787/10000000000 : ℝ)|=(4504936787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4117936031/10000000000 : ℝ)|^2187 ≤ (1255908693563/4000000000000 : ℝ)^1675
        have hw : |(4117936031/10000000000 : ℝ)|=(4117936031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2223/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2991/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15847/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5143/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15847/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5143/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15847/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5143/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15847/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5143/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15847/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5143/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15847/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5143/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5143/50000 : ℝ) ^ (4373/1024 : ℝ) ≤ (6050496955860331/100000000000000000000 : ℝ) := by
    have hpowers : (5143/50000 : ℝ)^4373 ≤ (6050496955860331/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5143 : ℕ)^4373*100000000000000000000^1024 ≤ 6050496955860331^1024*50000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5143 50000 6050496955860331 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5143/50000 : ℝ)) (X := (6050496955860331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15847/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (3831489682828703/10000000000000000000 : ℝ) := by
    have hpowers : (15847/100000 : ℝ)^4373 ≤ (3831489682828703/10000000000000000000 : ℝ)^1024 := by
      have hnat : (15847 : ℕ)^4373*10000000000000000000^1024 ≤ 3831489682828703^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15847 100000 3831489682828703 10000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15847/100000 : ℝ)) (X := (3831489682828703/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006050496955860331/50000000000000000000 : ℝ) ≤ (10000283348813789/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50006050496955860331/50000000000000000000 : ℝ)^1024 ≤ (10000283348813789/10000000000000000 : ℝ)^4373 := by
      have hnat : (50006050496955860331 : ℕ)^1024*10000000000000000^4373 ≤ 10000283348813789^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006050496955860331 50000000000000000000 10000283348813789 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283348813789/10000000000000000 : ℝ)) (X := (50006050496955860331/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044365393784147361/100000000000000000000 : ℝ) ≤ (10001038702205253/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (100044365393784147361/100000000000000000000 : ℝ)^1024 ≤ (10001038702205253/10000000000000000 : ℝ)^4373 := by
      have hnat : (100044365393784147361 : ℕ)^1024*10000000000000000^4373 ≤ 10001038702205253^4373*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044365393784147361 100000000000000000000 10001038702205253 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001038702205253/10000000000000000 : ℝ)) (X := (100044365393784147361/100000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003831489682828703/5000000000000000000 : ℝ) ≤ (10001794055596717/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (5003831489682828703/5000000000000000000 : ℝ)^1024 ≤ (10001794055596717/10000000000000000 : ℝ)^4373 := by
      have hnat : (5003831489682828703 : ℕ)^1024*10000000000000000^4373 ≤ 10001794055596717^4373*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003831489682828703 5000000000000000000 10001794055596717 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001794055596717/10000000000000000 : ℝ)) (X := (5003831489682828703/5000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6050496955860331/100000000000000000000 : ℝ) ≤ ((55596036572784283221/55610000000000000000 : ℝ)+2*(94419173933/69512500000000 : ℝ)*(5143/50000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (55596036572784283221/55610000000000000000 : ℝ)+2*(94419173933/69512500000000 : ℝ)*(5143/50000 : ℝ)=(10000283348813789/10000000000000000 : ℝ) by norm_num, show 1+2*(6050496955860331/100000000000000000000 : ℝ)=(50006050496955860331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3831489682828703/10000000000000000000 : ℝ)+(6050496955860331/100000000000000000000 : ℝ) ≤ ((55596036572784283221/55610000000000000000 : ℝ)+(94419173933/69512500000000 : ℝ)*((15847/100000 : ℝ)+(5143/50000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (55596036572784283221/55610000000000000000 : ℝ)+(94419173933/69512500000000 : ℝ)*((15847/100000 : ℝ)+(5143/50000 : ℝ))=(10001038702205253/10000000000000000 : ℝ) by norm_num, show 1+(3831489682828703/10000000000000000000 : ℝ)+(6050496955860331/100000000000000000000 : ℝ)=(100044365393784147361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3831489682828703/10000000000000000000 : ℝ) ≤ ((55596036572784283221/55610000000000000000 : ℝ)+2*(94419173933/69512500000000 : ℝ)*(15847/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (55596036572784283221/55610000000000000000 : ℝ)+2*(94419173933/69512500000000 : ℝ)*(15847/100000 : ℝ)=(10001794055596717/10000000000000000 : ℝ) by norm_num, show 1+2*(3831489682828703/10000000000000000000 : ℝ)=(5003831489682828703/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55596036572784283221/55610000000000000000 : ℝ)*(X 1 0+X 2 0)+(94419173933/69512500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (5143/50000 : ℝ)) (hi := (15847/100000 : ℝ)) (c := (55596036572784283221/55610000000000000000 : ℝ)) (alpha := (94419173933/69512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55596036572784283221/55610000000000000000 : ℝ)*(X 0 1+X 2 1)+(94419173933/69512500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (5143/50000 : ℝ)) (hi := (15847/100000 : ℝ)) (c := (55596036572784283221/55610000000000000000 : ℝ)) (alpha := (94419173933/69512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55596036572784283221/55610000000000000000 : ℝ)*(X 0 2+X 1 2)+(94419173933/69512500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (5143/50000 : ℝ)) (hi := (15847/100000 : ℝ)) (c := (55596036572784283221/55610000000000000000 : ℝ)) (alpha := (94419173933/69512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1982210253/10000000000 : ℝ)*X 0 0+(54188277/100000000 : ℝ)*X 0 1+(5237487253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350173119/10000000000 : ℝ)*X 1 0+(-2074738607/10000000000 : ℝ)*X 1 1+(1047497433/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675086529/5000000000 : ℝ)*X 2 0+(1047497457/2000000000 : ℝ)*X 2 1+(-2074738531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307434199/10000000000 : ℝ)*X 0 0+(4116359279/10000000000 : ℝ)*X 0 1+(563313037/1250000000 : ℝ)*X 0 2+(4307434199/10000000000 : ℝ)*X 1 0+(4116359279/10000000000 : ℝ)*X 1 1+(563313037/1250000000 : ℝ)*X 1 2+(4307434199/10000000000 : ℝ)*X 2 0+(4116359279/10000000000 : ℝ)*X 2 1+(563313037/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-991112979/5000000000 : ℝ)*X 0 0+(5238215981/10000000000 : ℝ)*X 0 1+(1083618987/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303100127/10000000000 : ℝ)*X 1 0+(-189413091/1000000000 : ℝ)*X 1 1+(5418094943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662887497/1250000000 : ℝ)*X 2 0+(2709047559/5000000000 : ℝ)*X 2 1+(-473532719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538433537/1250000000 : ℝ)*X 0 0+(4504936787/10000000000 : ℝ)*X 0 1+(4117936031/10000000000 : ℝ)*X 0 2+(538433537/1250000000 : ℝ)*X 1 0+(4504936787/10000000000 : ℝ)*X 1 1+(4117936031/10000000000 : ℝ)*X 1 2+(538433537/1250000000 : ℝ)*X 2 0+(4504936787/10000000000 : ℝ)*X 2 1+(4117936031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2798180491502625996331822173/347562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1520036561/100000000000000 : ℝ)*(base19) + (1447492371/100000000000000 : ℝ)*(base23) + (79909679/50000000000000 : ℝ)*(upper3) + (2586843/50000000000000 : ℝ)*(upper4) + (115145871/50000000000000 : ℝ)*(upper5) + (504857450174243/12500000000000 : ℝ)*(major0) + (504857450174243/12500000000000 : ℝ)*(major1) + (504857450174243/12500000000000 : ℝ)*(major2) + (5514515724372139/100000000000000 : ℝ)*(sp0) + (220581710034079/4000000000000 : ℝ)*(sp1) + (1102908564679233/20000000000000 : ℝ)*(sp2) + (160197661581253/6250000000000 : ℝ)*(sp3) + (7136629099/25000000000000 : ℝ)*(sp4) + (12078236959/100000000000000 : ℝ)*(sp7) + (160198416471063/6250000000000 : ℝ)*(f.failure) + (1102908854177707/20000000000000 : ℝ)*(f.sum) + (107527688522189/27805000000000000000000000000 : ℝ)*base66 + (8376000079428851703/695125000000000000000000000000000 : ℝ)*base67 + (17451799917210976703/695125000000000000000000000000000 : ℝ)*base69 + (7053926173811351703/695125000000000000000000000000000 : ℝ)*base71 + (14710369708121/6951250000000000000000000000 : ℝ)*base74 + (13715848903044976703/695125000000000000000000000000000 : ℝ)*base75 + (4933473397218226703/695125000000000000000000000000000 : ℝ)*base77 + (4637557180467726703/695125000000000000000000000000000 : ℝ)*base79 + (26202102434597/13902500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1292539/625000000000000000000 : ℝ)*base90 + (1292539/625000000000000000000 : ℝ)*base92 + (1292539/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26236977007085559831081/2780500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1042321393/100000000000000 : ℝ)*(base19) + (1072145113/100000000000000 : ℝ)*(base23) + (26664417/20000000000000 : ℝ)*(upper3) + (83215359/100000000000000 : ℝ)*(lower4) + (26659917/20000000000000 : ℝ)*(upper5) + (407163250326063/10000000000000 : ℝ)*(major0) + (407163250326063/10000000000000 : ℝ)*(major1) + (407163250326063/10000000000000 : ℝ)*(major2) + (9653712557/50000000000000 : ℝ)*(sp1) + (11411146791/50000000000000 : ℝ)*(sp2) + (347455713559873/6250000000000 : ℝ)*(sp4) + (5559271067211461/100000000000000 : ℝ)*(sp5) + (694908440314909/12500000000000 : ℝ)*(sp6) + (2583973275027807/100000000000000 : ℝ)*(sp7) + (2583973275027807/100000000000000 : ℝ)*(f.failure) + (347455713559873/6250000000000 : ℝ)*(f.sum) + (3255160167093/695125000000000000000000000 : ℝ)*base66 + (3136752110310611077/556100000000000000000000000000000 : ℝ)*base68 + (237004612071388923/556100000000000000000000000000000 : ℝ)*base69 + (4848733914345411077/556100000000000000000000000000000 : ℝ)*base72 + (12705948922503/5561000000000000000000000000 : ℝ)*base73 + (3461988973058088923/556100000000000000000000000000000 : ℝ)*base75 + (4065848056796911077/556100000000000000000000000000000 : ℝ)*base78 + (2110978765405588923/556100000000000000000000000000000 : ℝ)*base79 + (18234694899919/5561000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (44814429/10000000000000000000000 : ℝ)*base89 + (44814429/10000000000000000000000 : ℝ)*base91 + (44814429/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1414_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1414_s4_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-6197473/31250000 : ℝ)*x 0 + (5410525439/10000000000 : ℝ)*x 1 + (655642951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6197473/31250000 : ℝ)^2187 ≤ (6047263829541/50000000000000 : ℝ)^1675 := by
    have hnat : (6197473 : ℕ)^2187*50000000000000^1675 ≤ 6047263829541^1675*31250000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6197473 31250000 6047263829541 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410525439/10000000000 : ℝ)^2187 ≤ (44843376548917/100000000000000 : ℝ)^1675 := by
    have hnat : (5410525439 : ℕ)^2187*100000000000000^1675 ≤ 44843376548917^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410525439 10000000000 44843376548917 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655642951/1250000000 : ℝ)^2187 ≤ (21531047890981/50000000000000 : ℝ)^1675 := by
    have hnat : (655642951 : ℕ)^2187*50000000000000^1675 ≤ 21531047890981^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655642951 1250000000 21531047890981 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6197473/31250000 : ℝ), (5410525439/10000000000 : ℝ), (655642951/1250000000 : ℝ)] ![(6047263829541/50000000000000 : ℝ), (44843376548917/100000000000000 : ℝ), (21531047890981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6197473/31250000 : ℝ)|^2187 ≤ (6047263829541/50000000000000 : ℝ)^1675
        have hw : |(-6197473/31250000 : ℝ)|=(6197473/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410525439/10000000000 : ℝ)|^2187 ≤ (44843376548917/100000000000000 : ℝ)^1675
        have hw : |(5410525439/10000000000 : ℝ)|=(5410525439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655642951/1250000000 : ℝ)|^2187 ≤ (21531047890981/50000000000000 : ℝ)^1675
        have hw : |(655642951/1250000000 : ℝ)|=(655642951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348034121/10000000000 : ℝ)*x 0 + (-516857001/2500000000 : ℝ)*x 1 + (5245143703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348034121/10000000000 : ℝ)^2187 ≤ (2760519709861/6250000000000 : ℝ)^1675 := by
    have hnat : (5348034121 : ℕ)^2187*6250000000000^1675 ≤ 2760519709861^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348034121 10000000000 2760519709861 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516857001/2500000000 : ℝ)^2187 ≤ (12769587826707/100000000000000 : ℝ)^1675 := by
    have hnat : (516857001 : ℕ)^2187*100000000000000^1675 ≤ 12769587826707^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516857001 2500000000 12769587826707 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245143703/10000000000 : ℝ)^2187 ≤ (10765524200077/25000000000000 : ℝ)^1675 := by
    have hnat : (5245143703 : ℕ)^2187*25000000000000^1675 ≤ 10765524200077^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245143703 10000000000 10765524200077 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348034121/10000000000 : ℝ), (-516857001/2500000000 : ℝ), (5245143703/10000000000 : ℝ)] ![(2760519709861/6250000000000 : ℝ), (12769587826707/100000000000000 : ℝ), (10765524200077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348034121/10000000000 : ℝ)|^2187 ≤ (2760519709861/6250000000000 : ℝ)^1675
        have hw : |(5348034121/10000000000 : ℝ)|=(5348034121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516857001/2500000000 : ℝ)|^2187 ≤ (12769587826707/100000000000000 : ℝ)^1675
        have hw : |(-516857001/2500000000 : ℝ)|=(516857001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245143703/10000000000 : ℝ)|^2187 ≤ (10765524200077/25000000000000 : ℝ)^1675
        have hw : |(5245143703/10000000000 : ℝ)|=(5245143703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348034123/10000000000 : ℝ)*x 0 + (1049028713/2000000000 : ℝ)*x 1 + (-258428523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348034123/10000000000 : ℝ)^2187 ≤ (44168315379343/100000000000000 : ℝ)^1675 := by
    have hnat : (5348034123 : ℕ)^2187*100000000000000^1675 ≤ 44168315379343^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348034123 10000000000 44168315379343 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049028713/2000000000 : ℝ)^2187 ≤ (43062095321027/100000000000000 : ℝ)^1675 := by
    have hnat : (1049028713 : ℕ)^2187*100000000000000^1675 ≤ 43062095321027^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049028713 2000000000 43062095321027 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258428523/1250000000 : ℝ)^2187 ≤ (12769589278327/100000000000000 : ℝ)^1675 := by
    have hnat : (258428523 : ℕ)^2187*100000000000000^1675 ≤ 12769589278327^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258428523 1250000000 12769589278327 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348034123/10000000000 : ℝ), (1049028713/2000000000 : ℝ), (-258428523/1250000000 : ℝ)] ![(44168315379343/100000000000000 : ℝ), (43062095321027/100000000000000 : ℝ), (12769589278327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348034123/10000000000 : ℝ)|^2187 ≤ (44168315379343/100000000000000 : ℝ)^1675
        have hw : |(5348034123/10000000000 : ℝ)|=(5348034123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049028713/2000000000 : ℝ)|^2187 ≤ (43062095321027/100000000000000 : ℝ)^1675
        have hw : |(1049028713/2000000000 : ℝ)|=(1049028713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258428523/1250000000 : ℝ)|^2187 ≤ (12769589278327/100000000000000 : ℝ)^1675
        have hw : |(-258428523/1250000000 : ℝ)|=(258428523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4308033439/10000000000 : ℝ)*x 0 + (826690793/2000000000 : ℝ)*x 1 + (4489264627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308033439/10000000000 : ℝ)^2187 ≤ (832584949333/2500000000000 : ℝ)^1675 := by
    have hnat : (4308033439 : ℕ)^2187*2500000000000^1675 ≤ 832584949333^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308033439 10000000000 832584949333 2500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826690793/2000000000 : ℝ)^2187 ≤ (1972018203023/6250000000000 : ℝ)^1675 := by
    have hnat : (826690793 : ℕ)^2187*6250000000000^1675 ≤ 1972018203023^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826690793 2000000000 1972018203023 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489264627/10000000000 : ℝ)^2187 ≤ (4393038846423/12500000000000 : ℝ)^1675 := by
    have hnat : (4489264627 : ℕ)^2187*12500000000000^1675 ≤ 4393038846423^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489264627 10000000000 4393038846423 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308033439/10000000000 : ℝ), (826690793/2000000000 : ℝ), (4489264627/10000000000 : ℝ)] ![(832584949333/2500000000000 : ℝ), (1972018203023/6250000000000 : ℝ), (4393038846423/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308033439/10000000000 : ℝ)|^2187 ≤ (832584949333/2500000000000 : ℝ)^1675
        have hw : |(4308033439/10000000000 : ℝ)|=(4308033439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826690793/2000000000 : ℝ)|^2187 ≤ (1972018203023/6250000000000 : ℝ)^1675
        have hw : |(826690793/2000000000 : ℝ)|=(826690793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489264627/10000000000 : ℝ)|^2187 ≤ (4393038846423/12500000000000 : ℝ)^1675
        have hw : |(4489264627/10000000000 : ℝ)|=(4489264627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-495800863/2500000000 : ℝ)*x 0 + (5245750047/10000000000 : ℝ)*x 1 + (5409915809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495800863/2500000000 : ℝ)^2187 ≤ (3023655985919/25000000000000 : ℝ)^1675 := by
    have hnat : (495800863 : ℕ)^2187*25000000000000^1675 ≤ 3023655985919^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495800863 2500000000 3023655985919 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245750047/10000000000 : ℝ)^2187 ≤ (21534298289057/50000000000000 : ℝ)^1675 := by
    have hnat : (5245750047 : ℕ)^2187*50000000000000^1675 ≤ 21534298289057^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245750047 10000000000 21534298289057 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409915809/10000000000 : ℝ)^2187 ≤ (22418389734951/50000000000000 : ℝ)^1675 := by
    have hnat : (5409915809 : ℕ)^2187*50000000000000^1675 ≤ 22418389734951^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409915809 10000000000 22418389734951 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-495800863/2500000000 : ℝ), (5245750047/10000000000 : ℝ), (5409915809/10000000000 : ℝ)] ![(3023655985919/25000000000000 : ℝ), (21534298289057/50000000000000 : ℝ), (22418389734951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-495800863/2500000000 : ℝ)|^2187 ≤ (3023655985919/25000000000000 : ℝ)^1675
        have hw : |(-495800863/2500000000 : ℝ)|=(495800863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245750047/10000000000 : ℝ)|^2187 ≤ (21534298289057/50000000000000 : ℝ)^1675
        have hw : |(5245750047/10000000000 : ℝ)|=(5245750047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409915809/10000000000 : ℝ)|^2187 ≤ (22418389734951/50000000000000 : ℝ)^1675
        have hw : |(5409915809/10000000000 : ℝ)|=(5409915809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326275877/2500000000 : ℝ)*x 0 + (-1902655823/10000000000 : ℝ)*x 1 + (270495791/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326275877/2500000000 : ℝ)^2187 ≤ (10926487953687/25000000000000 : ℝ)^1675 := by
    have hnat : (1326275877 : ℕ)^2187*25000000000000^1675 ≤ 10926487953687^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326275877 2500000000 10926487953687 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902655823/10000000000 : ℝ)^2187 ≤ (716079287007/6250000000000 : ℝ)^1675 := by
    have hnat : (1902655823 : ℕ)^2187*6250000000000^1675 ≤ 716079287007^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902655823 10000000000 716079287007 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270495791/500000000 : ℝ)^2187 ≤ (5604597448617/12500000000000 : ℝ)^1675 := by
    have hnat : (270495791 : ℕ)^2187*12500000000000^1675 ≤ 5604597448617^1675*500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270495791 500000000 5604597448617 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326275877/2500000000 : ℝ), (-1902655823/10000000000 : ℝ), (270495791/500000000 : ℝ)] ![(10926487953687/25000000000000 : ℝ), (716079287007/6250000000000 : ℝ), (5604597448617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326275877/2500000000 : ℝ)|^2187 ≤ (10926487953687/25000000000000 : ℝ)^1675
        have hw : |(1326275877/2500000000 : ℝ)|=(1326275877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1902655823/10000000000 : ℝ)|^2187 ≤ (716079287007/6250000000000 : ℝ)^1675
        have hw : |(-1902655823/10000000000 : ℝ)|=(1902655823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270495791/500000000 : ℝ)|^2187 ≤ (5604597448617/12500000000000 : ℝ)^1675
        have hw : |(270495791/500000000 : ℝ)|=(270495791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305103519/10000000000 : ℝ)*x 0 + (1352478953/2500000000 : ℝ)*x 1 + (-951327909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305103519/10000000000 : ℝ)^2187 ≤ (2731621995817/6250000000000 : ℝ)^1675 := by
    have hnat : (5305103519 : ℕ)^2187*6250000000000^1675 ≤ 2731621995817^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305103519 10000000000 2731621995817 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352478953/2500000000 : ℝ)^2187 ≤ (22418389751183/50000000000000 : ℝ)^1675 := by
    have hnat : (1352478953 : ℕ)^2187*50000000000000^1675 ≤ 22418389751183^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352478953 2500000000 22418389751183 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (951327909/5000000000 : ℝ)^2187 ≤ (14321585691/125000000000 : ℝ)^1675 := by
    have hnat : (951327909 : ℕ)^2187*125000000000^1675 ≤ 14321585691^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951327909 5000000000 14321585691 125000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305103519/10000000000 : ℝ), (1352478953/2500000000 : ℝ), (-951327909/5000000000 : ℝ)] ![(2731621995817/6250000000000 : ℝ), (22418389751183/50000000000000 : ℝ), (14321585691/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305103519/10000000000 : ℝ)|^2187 ≤ (2731621995817/6250000000000 : ℝ)^1675
        have hw : |(5305103519/10000000000 : ℝ)|=(5305103519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352478953/2500000000 : ℝ)|^2187 ≤ (22418389751183/50000000000000 : ℝ)^1675
        have hw : |(1352478953/2500000000 : ℝ)|=(1352478953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-951327909/5000000000 : ℝ)|^2187 ≤ (14321585691/125000000000 : ℝ)^1675
        have hw : |(-951327909/5000000000 : ℝ)|=(951327909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s4_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077014911/2500000000 : ℝ)*x 0 + (4487959917/10000000000 : ℝ)*x 1 + (1033691341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077014911/2500000000 : ℝ)^2187 ≤ (8325915618687/25000000000000 : ℝ)^1675 := by
    have hnat : (1077014911 : ℕ)^2187*25000000000000^1675 ≤ 8325915618687^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077014911 2500000000 8325915618687 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487959917/10000000000 : ℝ)^2187 ≤ (35130975296231/100000000000000 : ℝ)^1675 := by
    have hnat : (4487959917 : ℕ)^2187*100000000000000^1675 ≤ 35130975296231^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487959917 10000000000 35130975296231 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033691341/2500000000 : ℝ)^2187 ≤ (31565362214019/100000000000000 : ℝ)^1675 := by
    have hnat : (1033691341 : ℕ)^2187*100000000000000^1675 ≤ 31565362214019^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033691341 2500000000 31565362214019 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077014911/2500000000 : ℝ), (4487959917/10000000000 : ℝ), (1033691341/2500000000 : ℝ)] ![(8325915618687/25000000000000 : ℝ), (35130975296231/100000000000000 : ℝ), (31565362214019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077014911/2500000000 : ℝ)|^2187 ≤ (8325915618687/25000000000000 : ℝ)^1675
        have hw : |(1077014911/2500000000 : ℝ)|=(1077014911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487959917/10000000000 : ℝ)|^2187 ≤ (35130975296231/100000000000000 : ℝ)^1675
        have hw : |(4487959917/10000000000 : ℝ)|=(4487959917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033691341/2500000000 : ℝ)|^2187 ≤ (31565362214019/100000000000000 : ℝ)^1675
        have hw : |(1033691341/2500000000 : ℝ)|=(1033691341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2991/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2991/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2991/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2991/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2991/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2991/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2223/20000 : ℝ) ^ (4373/1024 : ℝ) ≤ (8424592927544249/100000000000000000000 : ℝ) := by
    have hpowers : (2223/20000 : ℝ)^4373 ≤ (8424592927544249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2223 : ℕ)^4373*100000000000000000000^1024 ≤ 8424592927544249^1024*20000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2223 20000 8424592927544249 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2223/20000 : ℝ)) (X := (8424592927544249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2991/20000 : ℝ) ^ (4373/1024 : ℝ) ≤ (29917062476388239/100000000000000000000 : ℝ) := by
    have hpowers : (2991/20000 : ℝ)^4373 ≤ (29917062476388239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2991 : ℕ)^4373*100000000000000000000^1024 ≤ 29917062476388239^1024*20000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2991 20000 29917062476388239 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2991/20000 : ℝ)) (X := (29917062476388239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008424592927544249/50000000000000000000 : ℝ) ≤ (2500098630535393/2500000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50008424592927544249/50000000000000000000 : ℝ)^1024 ≤ (2500098630535393/2500000000000000 : ℝ)^4373 := by
      have hnat : (50008424592927544249 : ℕ)^1024*2500000000000000^4373 ≤ 2500098630535393^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008424592927544249 50000000000000000000 2500098630535393 2500000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500098630535393/2500000000000000 : ℝ)) (X := (50008424592927544249/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504792706925491561/12500000000000000000 : ℝ) ≤ (2000179538495879/2000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (12504792706925491561/12500000000000000000 : ℝ)^1024 ≤ (2000179538495879/2000000000000000 : ℝ)^4373 := by
      have hnat : (12504792706925491561 : ℕ)^1024*2000000000000000^4373 ≤ 2000179538495879^4373*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504792706925491561 12500000000000000000 2000179538495879 2000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000179538495879/2000000000000000 : ℝ)) (X := (12504792706925491561/12500000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029917062476388239/50000000000000000000 : ℝ) ≤ (5000700431408609/5000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50029917062476388239/50000000000000000000 : ℝ)^1024 ≤ (5000700431408609/5000000000000000 : ℝ)^4373 := by
      have hnat : (50029917062476388239 : ℕ)^1024*5000000000000000^4373 ≤ 5000700431408609^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029917062476388239 50000000000000000000 5000700431408609 5000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000700431408609/5000000000000000 : ℝ)) (X := (50029917062476388239/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8424592927544249/100000000000000000000 : ℝ) ≤ ((1279677649613794373/1280000000000000000 : ℝ)+2*(167723445941/128000000000000 : ℝ)*(2223/20000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (1279677649613794373/1280000000000000000 : ℝ)+2*(167723445941/128000000000000 : ℝ)*(2223/20000 : ℝ)=(2500098630535393/2500000000000000 : ℝ) by norm_num, show 1+2*(8424592927544249/100000000000000000000 : ℝ)=(50008424592927544249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29917062476388239/100000000000000000000 : ℝ)+(8424592927544249/100000000000000000000 : ℝ) ≤ ((1279677649613794373/1280000000000000000 : ℝ)+(167723445941/128000000000000 : ℝ)*((2991/20000 : ℝ)+(2223/20000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (1279677649613794373/1280000000000000000 : ℝ)+(167723445941/128000000000000 : ℝ)*((2991/20000 : ℝ)+(2223/20000 : ℝ))=(2000179538495879/2000000000000000 : ℝ) by norm_num, show 1+(29917062476388239/100000000000000000000 : ℝ)+(8424592927544249/100000000000000000000 : ℝ)=(12504792706925491561/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29917062476388239/100000000000000000000 : ℝ) ≤ ((1279677649613794373/1280000000000000000 : ℝ)+2*(167723445941/128000000000000 : ℝ)*(2991/20000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (1279677649613794373/1280000000000000000 : ℝ)+2*(167723445941/128000000000000 : ℝ)*(2991/20000 : ℝ)=(5000700431408609/5000000000000000 : ℝ) by norm_num, show 1+2*(29917062476388239/100000000000000000000 : ℝ)=(50029917062476388239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1279677649613794373/1280000000000000000 : ℝ)*(X 1 0+X 2 0)+(167723445941/128000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (1279677649613794373/1280000000000000000 : ℝ)) (alpha := (167723445941/128000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1279677649613794373/1280000000000000000 : ℝ)*(X 0 1+X 2 1)+(167723445941/128000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (1279677649613794373/1280000000000000000 : ℝ)) (alpha := (167723445941/128000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1279677649613794373/1280000000000000000 : ℝ)*(X 0 2+X 1 2)+(167723445941/128000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (1279677649613794373/1280000000000000000 : ℝ)) (alpha := (167723445941/128000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-6197473/31250000 : ℝ)*X 0 0+(5410525439/10000000000 : ℝ)*X 0 1+(655642951/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348034121/10000000000 : ℝ)*X 1 0+(-516857001/2500000000 : ℝ)*X 1 1+(5245143703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348034123/10000000000 : ℝ)*X 2 0+(1049028713/2000000000 : ℝ)*X 2 1+(-258428523/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308033439/10000000000 : ℝ)*X 0 0+(826690793/2000000000 : ℝ)*X 0 1+(4489264627/10000000000 : ℝ)*X 0 2+(4308033439/10000000000 : ℝ)*X 1 0+(826690793/2000000000 : ℝ)*X 1 1+(4489264627/10000000000 : ℝ)*X 1 2+(4308033439/10000000000 : ℝ)*X 2 0+(826690793/2000000000 : ℝ)*X 2 1+(4489264627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-495800863/2500000000 : ℝ)*X 0 0+(5245750047/10000000000 : ℝ)*X 0 1+(5409915809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326275877/2500000000 : ℝ)*X 1 0+(-1902655823/10000000000 : ℝ)*X 1 1+(270495791/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305103519/10000000000 : ℝ)*X 2 0+(1352478953/2500000000 : ℝ)*X 2 1+(-951327909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077014911/2500000000 : ℝ)*X 0 0+(4487959917/10000000000 : ℝ)*X 0 1+(1033691341/2500000000 : ℝ)*X 0 2+(1077014911/2500000000 : ℝ)*X 1 0+(4487959917/10000000000 : ℝ)*X 1 1+(1033691341/2500000000 : ℝ)*X 1 2+(1077014911/2500000000 : ℝ)*X 2 0+(4487959917/10000000000 : ℝ)*X 2 1+(1033691341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2431173577222605977409/640000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67456893/20000000000000 : ℝ)*(base19) + (366758081/100000000000000 : ℝ)*(base23) + (5133427/20000000000000 : ℝ)*(upper2) + (106650813/100000000000000 : ℝ)*(upper3) + (442856102438581/10000000000000 : ℝ)*(major0) + (442856102438581/10000000000000 : ℝ)*(major1) + (442856102438581/10000000000000 : ℝ)*(major2) + (120932499090257/2000000000000 : ℝ)*(sp0) + (120932627277649/2000000000000 : ℝ)*(sp1) + (6046628745609891/100000000000000 : ℝ)*(sp2) + (1405243099445109/50000000000000 : ℝ)*(sp3) + (1349330813/20000000000000 : ℝ)*(sp4) + (2588798943/100000000000000 : ℝ)*(sp6) + (2011045429/50000000000000 : ℝ)*(sp7) + (702622555245269/25000000000000 : ℝ)*(f.failure) + (1209326340233383/20000000000000 : ℝ)*(f.sum) + (2556302309639/640000000000000000000000000 : ℝ)*base66 + (88403551472314713/12800000000000000000000000000000 : ℝ)*base67 + (31075514409285287/12800000000000000000000000000000 : ℝ)*base70 + (91214747081914713/12800000000000000000000000000000 : ℝ)*base71 + (467020698119/640000000000000000000000000 : ℝ)*base74 + (85100934761285287/12800000000000000000000000000000 : ℝ)*base76 + (9627360713914713/12800000000000000000000000000000 : ℝ)*base77 + (119720684380485287/12800000000000000000000000000000 : ℝ)*base80 + (3830585065479/640000000000000000000000000 : ℝ)*base82 + (3969857/2500000000000000000000 : ℝ)*base90 + (3969857/2500000000000000000000 : ℝ)*base92 + (3969857/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137143825889328918136805673/32000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348949531/50000000000000 : ℝ)*(base19) + (778549477/100000000000000 : ℝ)*(base23) + (16838591/20000000000000 : ℝ)*(upper3) + (30871361/100000000000000 : ℝ)*(lower4) + (11564931/12500000000000 : ℝ)*(upper5) + (2230676124339789/50000000000000 : ℝ)*(major0) + (2230676124339789/50000000000000 : ℝ)*(major1) + (2230676124339789/50000000000000 : ℝ)*(major2) + (3684621187/25000000000000 : ℝ)*(sp1) + (7976500281/50000000000000 : ℝ)*(sp2) + (6091403894098089/100000000000000 : ℝ)*(sp4) + (6091388457714279/100000000000000 : ℝ)*(sp5) + (121827743250961/2000000000000 : ℝ)*(sp6) + (1415650230201451/50000000000000 : ℝ)*(sp7) + (1415650230201451/50000000000000 : ℝ)*(f.failure) + (6091403894098089/100000000000000 : ℝ)*(f.sum) + (9417749134449/3200000000000000000000000000 : ℝ)*base65 + (1260725875995302703/64000000000000000000000000000000 : ℝ)*base68 + (1285150580763302703/64000000000000000000000000000000 : ℝ)*base70 + (516727463899302703/64000000000000000000000000000000 : ℝ)*base72 + (1908701633551/3200000000000000000000000000 : ℝ)*base74 + (1493659164635302703/64000000000000000000000000000000 : ℝ)*base76 + (1127869085403302703/64000000000000000000000000000000 : ℝ)*base78 + (1691195632603302703/64000000000000000000000000000000 : ℝ)*base80 + (343482382449/3200000000000000000000000000 : ℝ)*base81 + (57165697/5000000000000000000000 : ℝ)*base89 + (57165697/5000000000000000000000 : ℝ)*base91 + (57165697/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1414_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1414_s5_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983341883/10000000000 : ℝ)*x 0 + (540919619/1000000000 : ℝ)*x 1 + (2623186811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983341883/10000000000 : ℝ)^2187 ≤ (377991444897/3125000000000 : ℝ)^1675 := by
    have hnat : (1983341883 : ℕ)^2187*3125000000000^1675 ≤ 377991444897^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983341883 10000000000 377991444897 3125000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540919619/1000000000 : ℝ)^2187 ≤ (22414496221567/50000000000000 : ℝ)^1675 := by
    have hnat : (540919619 : ℕ)^2187*50000000000000^1675 ≤ 22414496221567^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540919619 1000000000 22414496221567 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623186811/5000000000 : ℝ)^2187 ≤ (43075281305243/100000000000000 : ℝ)^1675 := by
    have hnat : (2623186811 : ℕ)^2187*100000000000000^1675 ≤ 43075281305243^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623186811 5000000000 43075281305243 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983341883/10000000000 : ℝ), (540919619/1000000000 : ℝ), (2623186811/5000000000 : ℝ)] ![(377991444897/3125000000000 : ℝ), (22414496221567/50000000000000 : ℝ), (43075281305243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983341883/10000000000 : ℝ)|^2187 ≤ (377991444897/3125000000000 : ℝ)^1675
        have hw : |(-1983341883/10000000000 : ℝ)|=(1983341883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540919619/1000000000 : ℝ)|^2187 ≤ (22414496221567/50000000000000 : ℝ)^1675
        have hw : |(540919619/1000000000 : ℝ)|=(540919619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623186811/5000000000 : ℝ)|^2187 ≤ (43075281305243/100000000000000 : ℝ)^1675
        have hw : |(2623186811/5000000000 : ℝ)|=(2623186811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347691673/10000000000 : ℝ)*x 0 + (-2066252487/10000000000 : ℝ)*x 1 + (1311593111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347691673/10000000000 : ℝ)^2187 ≤ (4416462268333/10000000000000 : ℝ)^1675 := by
    have hnat : (5347691673 : ℕ)^2187*10000000000000^1675 ≤ 4416462268333^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347691673 10000000000 4416462268333 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066252487/10000000000 : ℝ)^2187 ≤ (6380054314041/50000000000000 : ℝ)^1675 := by
    have hnat : (2066252487 : ℕ)^2187*50000000000000^1675 ≤ 6380054314041^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066252487 10000000000 6380054314041 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311593111/2500000000 : ℝ)^2187 ≤ (2692204292303/6250000000000 : ℝ)^1675 := by
    have hnat : (1311593111 : ℕ)^2187*6250000000000^1675 ≤ 2692204292303^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311593111 2500000000 2692204292303 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347691673/10000000000 : ℝ), (-2066252487/10000000000 : ℝ), (1311593111/2500000000 : ℝ)] ![(4416462268333/10000000000000 : ℝ), (6380054314041/50000000000000 : ℝ), (2692204292303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347691673/10000000000 : ℝ)|^2187 ≤ (4416462268333/10000000000000 : ℝ)^1675
        have hw : |(5347691673/10000000000 : ℝ)|=(5347691673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066252487/10000000000 : ℝ)|^2187 ≤ (6380054314041/50000000000000 : ℝ)^1675
        have hw : |(-2066252487/10000000000 : ℝ)|=(2066252487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311593111/2500000000 : ℝ)|^2187 ≤ (2692204292303/6250000000000 : ℝ)^1675
        have hw : |(1311593111/2500000000 : ℝ)|=(1311593111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267384559/500000000 : ℝ)*x 0 + (1311593323/2500000000 : ℝ)*x 1 + (-1033126009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267384559/500000000 : ℝ)^2187 ≤ (552057717091/1250000000000 : ℝ)^1675 := by
    have hnat : (267384559 : ℕ)^2187*1250000000000^1675 ≤ 552057717091^1675*500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267384559 500000000 552057717091 1250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311593323/2500000000 : ℝ)^2187 ≤ (43075277767577/100000000000000 : ℝ)^1675 := by
    have hnat : (1311593323 : ℕ)^2187*100000000000000^1675 ≤ 43075277767577^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311593323 2500000000 43075277767577 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033126009/5000000000 : ℝ)^2187 ≤ (6380052423231/50000000000000 : ℝ)^1675 := by
    have hnat : (1033126009 : ℕ)^2187*50000000000000^1675 ≤ 6380052423231^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033126009 5000000000 6380052423231 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267384559/500000000 : ℝ), (1311593323/2500000000 : ℝ), (-1033126009/5000000000 : ℝ)] ![(552057717091/1250000000000 : ℝ), (43075277767577/100000000000000 : ℝ), (6380052423231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267384559/500000000 : ℝ)|^2187 ≤ (552057717091/1250000000000 : ℝ)^1675
        have hw : |(267384559/500000000 : ℝ)|=(267384559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311593323/2500000000 : ℝ)|^2187 ≤ (43075277767577/100000000000000 : ℝ)^1675
        have hw : |(1311593323/2500000000 : ℝ)|=(1311593323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033126009/5000000000 : ℝ)|^2187 ≤ (6380052423231/50000000000000 : ℝ)^1675
        have hw : |(-1033126009/5000000000 : ℝ)|=(1033126009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4308124013/10000000000 : ℝ)*x 0 + (517024327/1250000000 : ℝ)*x 1 + (897300463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308124013/10000000000 : ℝ)^2187 ≤ (16652156094217/50000000000000 : ℝ)^1675 := by
    have hnat : (4308124013 : ℕ)^2187*50000000000000^1675 ≤ 16652156094217^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308124013 10000000000 16652156094217 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517024327/1250000000 : ℝ)^2187 ≤ (6315921857271/20000000000000 : ℝ)^1675 := by
    have hnat : (517024327 : ℕ)^2187*20000000000000^1675 ≤ 6315921857271^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517024327 1250000000 6315921857271 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897300463/2000000000 : ℝ)^2187 ≤ (17558039254673/50000000000000 : ℝ)^1675 := by
    have hnat : (897300463 : ℕ)^2187*50000000000000^1675 ≤ 17558039254673^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897300463 2000000000 17558039254673 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308124013/10000000000 : ℝ), (517024327/1250000000 : ℝ), (897300463/2000000000 : ℝ)] ![(16652156094217/50000000000000 : ℝ), (6315921857271/20000000000000 : ℝ), (17558039254673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308124013/10000000000 : ℝ)|^2187 ≤ (16652156094217/50000000000000 : ℝ)^1675
        have hw : |(4308124013/10000000000 : ℝ)|=(4308124013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517024327/1250000000 : ℝ)|^2187 ≤ (6315921857271/20000000000000 : ℝ)^1675
        have hw : |(517024327/1250000000 : ℝ)|=(517024327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897300463/2000000000 : ℝ)|^2187 ≤ (17558039254673/50000000000000 : ℝ)^1675
        have hw : |(897300463/2000000000 : ℝ)|=(897300463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983353359/10000000000 : ℝ)*x 0 + (1049392177/2000000000 : ℝ)*x 1 + (5408605923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983353359/10000000000 : ℝ)^2187 ≤ (1209581761841/10000000000000 : ℝ)^1675 := by
    have hnat : (1983353359 : ℕ)^2187*10000000000000^1675 ≤ 1209581761841^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983353359 10000000000 1209581761841 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049392177/2000000000 : ℝ)^2187 ≤ (21540788494809/50000000000000 : ℝ)^1675 := by
    have hnat : (1049392177 : ℕ)^2187*50000000000000^1675 ≤ 21540788494809^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049392177 2000000000 21540788494809 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408605923/10000000000 : ℝ)^2187 ≤ (700353209001/1562500000000 : ℝ)^1675 := by
    have hnat : (5408605923 : ℕ)^2187*1562500000000^1675 ≤ 700353209001^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408605923 10000000000 700353209001 1562500000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983353359/10000000000 : ℝ), (1049392177/2000000000 : ℝ), (5408605923/10000000000 : ℝ)] ![(1209581761841/10000000000000 : ℝ), (21540788494809/50000000000000 : ℝ), (700353209001/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983353359/10000000000 : ℝ)|^2187 ≤ (1209581761841/10000000000000 : ℝ)^1675
        have hw : |(-1983353359/10000000000 : ℝ)|=(1983353359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049392177/2000000000 : ℝ)|^2187 ≤ (21540788494809/50000000000000 : ℝ)^1675
        have hw : |(1049392177/2000000000 : ℝ)|=(1049392177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408605923/10000000000 : ℝ)|^2187 ≤ (700353209001/1562500000000 : ℝ)^1675
        have hw : |(5408605923/10000000000 : ℝ)|=(5408605923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305424597/10000000000 : ℝ)*x 0 + (-476004791/2500000000 : ℝ)*x 1 + (5408605923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305424597/10000000000 : ℝ)^2187 ≤ (21854702858877/50000000000000 : ℝ)^1675 := by
    have hnat : (5305424597 : ℕ)^2187*50000000000000^1675 ≤ 21854702858877^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305424597 10000000000 21854702858877 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476004791/2500000000 : ℝ)^2187 ≤ (11467988890601/100000000000000 : ℝ)^1675 := by
    have hnat : (476004791 : ℕ)^2187*100000000000000^1675 ≤ 11467988890601^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476004791 2500000000 11467988890601 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408605923/10000000000 : ℝ)^2187 ≤ (700353209001/1562500000000 : ℝ)^1675 := by
    have hnat : (5408605923 : ℕ)^2187*1562500000000^1675 ≤ 700353209001^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408605923 10000000000 700353209001 1562500000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305424597/10000000000 : ℝ), (-476004791/2500000000 : ℝ), (5408605923/10000000000 : ℝ)] ![(21854702858877/50000000000000 : ℝ), (11467988890601/100000000000000 : ℝ), (700353209001/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305424597/10000000000 : ℝ)|^2187 ≤ (21854702858877/50000000000000 : ℝ)^1675
        have hw : |(5305424597/10000000000 : ℝ)|=(5305424597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476004791/2500000000 : ℝ)|^2187 ≤ (11467988890601/100000000000000 : ℝ)^1675
        have hw : |(-476004791/2500000000 : ℝ)|=(476004791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408605923/10000000000 : ℝ)|^2187 ≤ (700353209001/1562500000000 : ℝ)^1675
        have hw : |(5408605923/10000000000 : ℝ)|=(5408605923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061084919/2000000000 : ℝ)*x 0 + (216344237/400000000 : ℝ)*x 1 + (-476004791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061084919/2000000000 : ℝ)^2187 ≤ (546367571203/1250000000000 : ℝ)^1675 := by
    have hnat : (1061084919 : ℕ)^2187*1250000000000^1675 ≤ 546367571203^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061084919 2000000000 546367571203 1250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216344237/400000000 : ℝ)^2187 ≤ (8964521079541/20000000000000 : ℝ)^1675 := by
    have hnat : (216344237 : ℕ)^2187*20000000000000^1675 ≤ 8964521079541^1675*400000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216344237 400000000 8964521079541 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476004791/2500000000 : ℝ)^2187 ≤ (11467988890601/100000000000000 : ℝ)^1675 := by
    have hnat : (476004791 : ℕ)^2187*100000000000000^1675 ≤ 11467988890601^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476004791 2500000000 11467988890601 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061084919/2000000000 : ℝ), (216344237/400000000 : ℝ), (-476004791/2500000000 : ℝ)] ![(546367571203/1250000000000 : ℝ), (8964521079541/20000000000000 : ℝ), (11467988890601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061084919/2000000000 : ℝ)|^2187 ≤ (546367571203/1250000000000 : ℝ)^1675
        have hw : |(1061084919/2000000000 : ℝ)|=(1061084919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216344237/400000000 : ℝ)|^2187 ≤ (8964521079541/20000000000000 : ℝ)^1675
        have hw : |(216344237/400000000 : ℝ)|=(216344237/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476004791/2500000000 : ℝ)|^2187 ≤ (11467988890601/100000000000000 : ℝ)^1675
        have hw : |(-476004791/2500000000 : ℝ)|=(476004791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s5_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2154074703/5000000000 : ℝ)*x 0 + (1121309289/2500000000 : ℝ)*x 1 + (2068732891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154074703/5000000000 : ℝ)^2187 ≤ (1665228424777/5000000000000 : ℝ)^1675 := by
    have hnat : (2154074703 : ℕ)^2187*5000000000000^1675 ≤ 1665228424777^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154074703 5000000000 1665228424777 5000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121309289/2500000000 : ℝ)^2187 ≤ (17551574850807/50000000000000 : ℝ)^1675 := by
    have hnat : (1121309289 : ℕ)^2187*50000000000000^1675 ≤ 17551574850807^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121309289 2500000000 17551574850807 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068732891/5000000000 : ℝ)^2187 ≤ (31592281789993/100000000000000 : ℝ)^1675 := by
    have hnat : (2068732891 : ℕ)^2187*100000000000000^1675 ≤ 31592281789993^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068732891 5000000000 31592281789993 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154074703/5000000000 : ℝ), (1121309289/2500000000 : ℝ), (2068732891/5000000000 : ℝ)] ![(1665228424777/5000000000000 : ℝ), (17551574850807/50000000000000 : ℝ), (31592281789993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154074703/5000000000 : ℝ)|^2187 ≤ (1665228424777/5000000000000 : ℝ)^1675
        have hw : |(2154074703/5000000000 : ℝ)|=(2154074703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121309289/2500000000 : ℝ)|^2187 ≤ (17551574850807/50000000000000 : ℝ)^1675
        have hw : |(1121309289/2500000000 : ℝ)|=(1121309289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068732891/5000000000 : ℝ)|^2187 ≤ (31592281789993/100000000000000 : ℝ)^1675
        have hw : |(2068732891/5000000000 : ℝ)|=(2068732891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2261/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (358735346520051/4000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^4373 ≤ (358735346520051/4000000000000000000 : ℝ)^1024 := by
      have hnat : (11279 : ℕ)^4373*4000000000000000000^1024 ≤ 358735346520051^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 358735346520051 4000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (358735346520051/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14781/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (28458608670177127/100000000000000000000 : ℝ) := by
    have hpowers : (14781/100000 : ℝ)^4373 ≤ (28458608670177127/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14781 : ℕ)^4373*100000000000000000000^1024 ≤ 28458608670177127^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14781 100000 28458608670177127 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14781/100000 : ℝ)) (X := (28458608670177127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000358735346520051/2000000000000000000 : ℝ) ≤ (250010499650329/250000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (2000358735346520051/2000000000000000000 : ℝ)^1024 ≤ (250010499650329/250000000000000 : ℝ)^4373 := by
      have hnat : (2000358735346520051 : ℕ)^1024*250000000000000^4373 ≤ 250010499650329^4373*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000358735346520051 2000000000000000000 250010499650329 250000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250010499650329/250000000000000 : ℝ)) (X := (2000358735346520051/2000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018713496166589201/50000000000000000000 : ℝ) ≤ (2500219070139437/2500000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50018713496166589201/50000000000000000000 : ℝ)^1024 ≤ (2500219070139437/2500000000000000 : ℝ)^4373 := by
      have hnat : (50018713496166589201 : ℕ)^1024*2500000000000000^4373 ≤ 2500219070139437^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018713496166589201 50000000000000000000 2500219070139437 2500000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500219070139437/2500000000000000 : ℝ)) (X := (50018713496166589201/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028458608670177127/50000000000000000000 : ℝ) ≤ (78135410742987/78125000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50028458608670177127/50000000000000000000 : ℝ)^1024 ≤ (78135410742987/78125000000000 : ℝ)^4373 := by
      have hnat : (50028458608670177127 : ℕ)^1024*78125000000000^4373 ≤ 78135410742987^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028458608670177127 50000000000000000000 78135410742987 78125000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78135410742987/78125000000000 : ℝ)) (X := (50028458608670177127/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(358735346520051/4000000000000000000 : ℝ) ≤ ((257435130137362281/257500000000000000 : ℝ)+2*(6710213891/5150000000000 : ℝ)*(11279/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (257435130137362281/257500000000000000 : ℝ)+2*(6710213891/5150000000000 : ℝ)*(11279/100000 : ℝ)=(250010499650329/250000000000000 : ℝ) by norm_num, show 1+2*(358735346520051/4000000000000000000 : ℝ)=(2000358735346520051/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28458608670177127/100000000000000000000 : ℝ)+(358735346520051/4000000000000000000 : ℝ) ≤ ((257435130137362281/257500000000000000 : ℝ)+(6710213891/5150000000000 : ℝ)*((14781/100000 : ℝ)+(11279/100000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (257435130137362281/257500000000000000 : ℝ)+(6710213891/5150000000000 : ℝ)*((14781/100000 : ℝ)+(11279/100000 : ℝ))=(2500219070139437/2500000000000000 : ℝ) by norm_num, show 1+(28458608670177127/100000000000000000000 : ℝ)+(358735346520051/4000000000000000000 : ℝ)=(50018713496166589201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28458608670177127/100000000000000000000 : ℝ) ≤ ((257435130137362281/257500000000000000 : ℝ)+2*(6710213891/5150000000000 : ℝ)*(14781/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (257435130137362281/257500000000000000 : ℝ)+2*(6710213891/5150000000000 : ℝ)*(14781/100000 : ℝ)=(78135410742987/78125000000000 : ℝ) by norm_num, show 1+2*(28458608670177127/100000000000000000000 : ℝ)=(50028458608670177127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (257435130137362281/257500000000000000 : ℝ)*(X 1 0+X 2 0)+(6710213891/5150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (257435130137362281/257500000000000000 : ℝ)) (alpha := (6710213891/5150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (257435130137362281/257500000000000000 : ℝ)*(X 0 1+X 2 1)+(6710213891/5150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (257435130137362281/257500000000000000 : ℝ)) (alpha := (6710213891/5150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (257435130137362281/257500000000000000 : ℝ)*(X 0 2+X 1 2)+(6710213891/5150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (257435130137362281/257500000000000000 : ℝ)) (alpha := (6710213891/5150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1983341883/10000000000 : ℝ)*X 0 0+(540919619/1000000000 : ℝ)*X 0 1+(2623186811/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347691673/10000000000 : ℝ)*X 1 0+(-2066252487/10000000000 : ℝ)*X 1 1+(1311593111/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267384559/500000000 : ℝ)*X 2 0+(1311593323/2500000000 : ℝ)*X 2 1+(-1033126009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308124013/10000000000 : ℝ)*X 0 0+(517024327/1250000000 : ℝ)*X 0 1+(897300463/2000000000 : ℝ)*X 0 2+(4308124013/10000000000 : ℝ)*X 1 0+(517024327/1250000000 : ℝ)*X 1 1+(897300463/2000000000 : ℝ)*X 1 2+(4308124013/10000000000 : ℝ)*X 2 0+(517024327/1250000000 : ℝ)*X 2 1+(897300463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1983353359/10000000000 : ℝ)*X 0 0+(1049392177/2000000000 : ℝ)*X 0 1+(5408605923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305424597/10000000000 : ℝ)*X 1 0+(-476004791/2500000000 : ℝ)*X 1 1+(5408605923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061084919/2000000000 : ℝ)*X 2 0+(216344237/400000000 : ℝ)*X 2 1+(-476004791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2154074703/5000000000 : ℝ)*X 0 0+(1121309289/2500000000 : ℝ)*X 0 1+(2068732891/5000000000 : ℝ)*X 0 2+(2154074703/5000000000 : ℝ)*X 1 0+(1121309289/2500000000 : ℝ)*X 1 1+(2068732891/5000000000 : ℝ)*X 1 2+(2154074703/5000000000 : ℝ)*X 2 0+(1121309289/2500000000 : ℝ)*X 2 1+(2068732891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1947084973979221385051499/321875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1214771569/100000000000000 : ℝ)*(base19) + (384341097/100000000000000 : ℝ)*(base23) + (40412171/25000000000000 : ℝ)*(upper4) + (12935869/10000000000000 : ℝ)*(upper5) + (224907621570793/5000000000000 : ℝ)*(major0) + (224907621570793/5000000000000 : ℝ)*(major1) + (224907621570793/5000000000000 : ℝ)*(major2) + (767706220353207/12500000000000 : ℝ)*(sp0) + (6141639546879799/100000000000000 : ℝ)*(sp1) + (6141645190319191/100000000000000 : ℝ)*(sp2) + (1427322665326051/50000000000000 : ℝ)*(sp3) + (9001174289/100000000000000 : ℝ)*(sp5) + (4188165369/100000000000000 : ℝ)*(sp6) + (2391928521/25000000000000 : ℝ)*(sp7) + (1427327449183093/50000000000000 : ℝ)*(f.failure) + (767706220353207/12500000000000 : ℝ)*(f.sum) + (382625230621/51500000000000000000000000 : ℝ)*base66 + (11960243958991167/1287500000000000000000000000000 : ℝ)*base68 + (5823629199266167/1287500000000000000000000000000 : ℝ)*base70 + (2647575106733833/1287500000000000000000000000000 : ℝ)*base71 + (322669168477/103000000000000000000000000 : ℝ)*base74 + (17760462030678667/1287500000000000000000000000000 : ℝ)*base76 + (6012775199828667/1287500000000000000000000000000 : ℝ)*base78 + (35394298559878667/1287500000000000000000000000000 : ℝ)*base80 + (30759819439/12875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33347871/5000000000000000000000 : ℝ)*base89 + (33347871/5000000000000000000000 : ℝ)*base91 + (33347871/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1411907807714765672838153/643750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38232741/10000000000000 : ℝ)*(base19) + (204986729/50000000000000 : ℝ)*(base23) + (46274041/100000000000000 : ℝ)*(upper3) + (13495357/100000000000000 : ℝ)*(lower4) + (45305839/100000000000000 : ℝ)*(upper5) + (226546165134193/5000000000000 : ℝ)*(major0) + (226546165134193/5000000000000 : ℝ)*(major1) + (226546165134193/5000000000000 : ℝ)*(major2) + (3983997021/50000000000000 : ℝ)*(sp1) + (8538117137/100000000000000 : ℝ)*(sp2) + (1237278862215531/20000000000000 : ℝ)*(sp4) + (6186385960756203/100000000000000 : ℝ)*(sp5) + (6186385362987059/100000000000000 : ℝ)*(sp6) + (2875452221181561/100000000000000 : ℝ)*(sp7) + (2875452221181561/100000000000000 : ℝ)*(f.failure) + (1237278862215531/20000000000000 : ℝ)*(f.sum) + (81301808741/103000000000000000000000000 : ℝ)*base65 + (8897488736311733/1287500000000000000000000000000 : ℝ)*base67 + (8218343975961733/1287500000000000000000000000000 : ℝ)*base69 + (6227039882611733/1287500000000000000000000000000 : ℝ)*base71 + (308166925697/51500000000000000000000000 : ℝ)*base73 + (6076177719011733/1287500000000000000000000000000 : ℝ)*base75 + (9067869611061733/1287500000000000000000000000000 : ℝ)*base77 + (467576172411733/1287500000000000000000000000000 : ℝ)*base79 + (26977412503/12875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (83794133/10000000000000000000000 : ℝ)*base90 + (83794133/10000000000000000000000 : ℝ)*base92 + (83794133/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1414_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1414_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1414_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1414_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1414_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15847/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1414_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
