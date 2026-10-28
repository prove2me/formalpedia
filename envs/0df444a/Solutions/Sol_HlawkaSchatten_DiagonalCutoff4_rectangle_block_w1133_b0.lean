-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:27:44.565992+00:00
-- url     : https://prove2.me/submissions/31ee56ef-7768-4286-a286-96fc816529ff

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
theorem support_rectangle_w1133_s0_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-947331427/5000000000 : ℝ)*x 0 + (757051561/1250000000 : ℝ)*x 1 + (2389666453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947331427/5000000000 : ℝ)^4163 ≤ (172055868591/1562500000000 : ℝ)^3139 := by
    have hnat : (947331427 : ℕ)^4163*1562500000000^3139 ≤ 172055868591^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947331427 5000000000 172055868591 1562500000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757051561/1250000000 : ℝ)^4163 ≤ (803507829473/1562500000000 : ℝ)^3139 := by
    have hnat : (757051561 : ℕ)^4163*1562500000000^3139 ≤ 803507829473^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757051561 1250000000 803507829473 1562500000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389666453/5000000000 : ℝ)^4163 ≤ (37563923309393/100000000000000 : ℝ)^3139 := by
    have hnat : (2389666453 : ℕ)^4163*100000000000000^3139 ≤ 37563923309393^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389666453 5000000000 37563923309393 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947331427/5000000000 : ℝ), (757051561/1250000000 : ℝ), (2389666453/5000000000 : ℝ)] ![(172055868591/1562500000000 : ℝ), (803507829473/1562500000000 : ℝ), (37563923309393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947331427/5000000000 : ℝ)|^4163 ≤ (172055868591/1562500000000 : ℝ)^3139
        have hw : |(-947331427/5000000000 : ℝ)|=(947331427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(757051561/1250000000 : ℝ)|^4163 ≤ (803507829473/1562500000000 : ℝ)^3139
        have hw : |(757051561/1250000000 : ℝ)|=(757051561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2389666453/5000000000 : ℝ)|^4163 ≤ (37563923309393/100000000000000 : ℝ)^3139
        have hw : |(2389666453/5000000000 : ℝ)|=(2389666453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5517299447/10000000000 : ℝ)*x 0 + (-2627815293/10000000000 : ℝ)*x 1 + (1194833347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517299447/10000000000 : ℝ)^4163 ≤ (45443625208063/100000000000000 : ℝ)^3139 := by
    have hnat : (5517299447 : ℕ)^4163*100000000000000^3139 ≤ 45443625208063^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517299447 10000000000 45443625208063 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627815293/10000000000 : ℝ)^4163 ≤ (16992446448499/100000000000000 : ℝ)^3139 := by
    have hnat : (2627815293 : ℕ)^4163*100000000000000^3139 ≤ 16992446448499^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627815293 10000000000 16992446448499 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194833347/2500000000 : ℝ)^4163 ≤ (1878196416679/5000000000000 : ℝ)^3139 := by
    have hnat : (1194833347 : ℕ)^4163*5000000000000^3139 ≤ 1878196416679^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194833347 2500000000 1878196416679 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517299447/10000000000 : ℝ), (-2627815293/10000000000 : ℝ), (1194833347/2500000000 : ℝ)] ![(45443625208063/100000000000000 : ℝ), (16992446448499/100000000000000 : ℝ), (1878196416679/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517299447/10000000000 : ℝ)|^4163 ≤ (45443625208063/100000000000000 : ℝ)^3139
        have hw : |(5517299447/10000000000 : ℝ)|=(5517299447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2627815293/10000000000 : ℝ)|^4163 ≤ (16992446448499/100000000000000 : ℝ)^3139
        have hw : |(-2627815293/10000000000 : ℝ)|=(2627815293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194833347/2500000000 : ℝ)|^4163 ≤ (1878196416679/5000000000000 : ℝ)^3139
        have hw : |(1194833347/2500000000 : ℝ)|=(1194833347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2758651391/5000000000 : ℝ)*x 0 + (4779332041/10000000000 : ℝ)*x 1 + (-2627812681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758651391/5000000000 : ℝ)^4163 ≤ (22721830818957/50000000000000 : ℝ)^3139 := by
    have hnat : (2758651391 : ℕ)^4163*50000000000000^3139 ≤ 22721830818957^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758651391 5000000000 22721830818957 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4779332041/10000000000 : ℝ)^4163 ≤ (18781957146479/50000000000000 : ℝ)^3139 := by
    have hnat : (4779332041 : ℕ)^4163*50000000000000^3139 ≤ 18781957146479^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779332041 10000000000 18781957146479 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627812681/10000000000 : ℝ)^4163 ≤ (8496212024217/50000000000000 : ℝ)^3139 := by
    have hnat : (2627812681 : ℕ)^4163*50000000000000^3139 ≤ 8496212024217^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627812681 10000000000 8496212024217 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758651391/5000000000 : ℝ), (4779332041/10000000000 : ℝ), (-2627812681/10000000000 : ℝ)] ![(22721830818957/50000000000000 : ℝ), (18781957146479/50000000000000 : ℝ), (8496212024217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758651391/5000000000 : ℝ)|^4163 ≤ (22721830818957/50000000000000 : ℝ)^3139
        have hw : |(2758651391/5000000000 : ℝ)|=(2758651391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4779332041/10000000000 : ℝ)|^4163 ≤ (18781957146479/50000000000000 : ℝ)^3139
        have hw : |(4779332041/10000000000 : ℝ)|=(4779332041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2627812681/10000000000 : ℝ)|^4163 ≤ (8496212024217/50000000000000 : ℝ)^3139
        have hw : |(-2627812681/10000000000 : ℝ)|=(2627812681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201720193/10000000000 : ℝ)*x 0 + (1560749281/5000000000 : ℝ)*x 1 + (22630927/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201720193/10000000000 : ℝ)^4163 ≤ (31665188301683/100000000000000 : ℝ)^3139 := by
    have hnat : (4201720193 : ℕ)^4163*100000000000000^3139 ≤ 31665188301683^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201720193 10000000000 31665188301683 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560749281/5000000000 : ℝ)^4163 ≤ (854033706589/4000000000000 : ℝ)^3139 := by
    have hnat : (1560749281 : ℕ)^4163*4000000000000^3139 ≤ 854033706589^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560749281 5000000000 854033706589 4000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22630927/40000000 : ℝ)^4163 ≤ (23491984512589/50000000000000 : ℝ)^3139 := by
    have hnat : (22630927 : ℕ)^4163*50000000000000^3139 ≤ 23491984512589^3139*40000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22630927 40000000 23491984512589 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201720193/10000000000 : ℝ), (1560749281/5000000000 : ℝ), (22630927/40000000 : ℝ)] ![(31665188301683/100000000000000 : ℝ), (854033706589/4000000000000 : ℝ), (23491984512589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201720193/10000000000 : ℝ)|^4163 ≤ (31665188301683/100000000000000 : ℝ)^3139
        have hw : |(4201720193/10000000000 : ℝ)|=(4201720193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560749281/5000000000 : ℝ)|^4163 ≤ (854033706589/4000000000000 : ℝ)^3139
        have hw : |(1560749281/5000000000 : ℝ)|=(1560749281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22630927/40000000 : ℝ)|^4163 ≤ (23491984512589/50000000000000 : ℝ)^3139
        have hw : |(22630927/40000000 : ℝ)|=(22630927/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-94991729/500000000 : ℝ)*x 0 + (4812282387/10000000000 : ℝ)*x 1 + (752788187/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94991729/500000000 : ℝ)^4163 ≤ (11051456156919/100000000000000 : ℝ)^3139 := by
    have hnat : (94991729 : ℕ)^4163*100000000000000^3139 ≤ 11051456156919^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94991729 500000000 11051456156919 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4812282387/10000000000 : ℝ)^4163 ≤ (37907761943799/100000000000000 : ℝ)^3139 := by
    have hnat : (4812282387 : ℕ)^4163*100000000000000^3139 ≤ 37907761943799^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4812282387 10000000000 37907761943799 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752788187/1250000000 : ℝ)^4163 ≤ (3190048867309/6250000000000 : ℝ)^3139 := by
    have hnat : (752788187 : ℕ)^4163*6250000000000^3139 ≤ 3190048867309^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752788187 1250000000 3190048867309 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94991729/500000000 : ℝ), (4812282387/10000000000 : ℝ), (752788187/1250000000 : ℝ)] ![(11051456156919/100000000000000 : ℝ), (37907761943799/100000000000000 : ℝ), (3190048867309/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94991729/500000000 : ℝ)|^4163 ≤ (11051456156919/100000000000000 : ℝ)^3139
        have hw : |(-94991729/500000000 : ℝ)|=(94991729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4812282387/10000000000 : ℝ)|^4163 ≤ (37907761943799/100000000000000 : ℝ)^3139
        have hw : |(4812282387/10000000000 : ℝ)|=(4812282387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752788187/1250000000 : ℝ)|^4163 ≤ (3190048867309/6250000000000 : ℝ)^3139
        have hw : |(752788187/1250000000 : ℝ)|=(752788187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5170334043/10000000000 : ℝ)*x 0 + (-346210457/2500000000 : ℝ)*x 1 + (6022305401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170334043/10000000000 : ℝ)^4163 ≤ (41692991706443/100000000000000 : ℝ)^3139 := by
    have hnat : (5170334043 : ℕ)^4163*100000000000000^3139 ≤ 41692991706443^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170334043 10000000000 41692991706443 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346210457/2500000000 : ℝ)^4163 ≤ (3633113737049/50000000000000 : ℝ)^3139 := by
    have hnat : (346210457 : ℕ)^4163*50000000000000^3139 ≤ 3633113737049^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346210457 2500000000 3633113737049 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6022305401/10000000000 : ℝ)^4163 ≤ (3190048800571/6250000000000 : ℝ)^3139 := by
    have hnat : (6022305401 : ℕ)^4163*6250000000000^3139 ≤ 3190048800571^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022305401 10000000000 3190048800571 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170334043/10000000000 : ℝ), (-346210457/2500000000 : ℝ), (6022305401/10000000000 : ℝ)] ![(41692991706443/100000000000000 : ℝ), (3633113737049/50000000000000 : ℝ), (3190048800571/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170334043/10000000000 : ℝ)|^4163 ≤ (41692991706443/100000000000000 : ℝ)^3139
        have hw : |(5170334043/10000000000 : ℝ)|=(5170334043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346210457/2500000000 : ℝ)|^4163 ≤ (3633113737049/50000000000000 : ℝ)^3139
        have hw : |(-346210457/2500000000 : ℝ)|=(346210457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6022305401/10000000000 : ℝ)|^4163 ≤ (3190048800571/6250000000000 : ℝ)^3139
        have hw : |(6022305401/10000000000 : ℝ)|=(6022305401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585167031/5000000000 : ℝ)*x 0 + (6022305403/10000000000 : ℝ)*x 1 + (-276968359/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585167031/5000000000 : ℝ)^4163 ≤ (20846495954819/50000000000000 : ℝ)^3139 := by
    have hnat : (2585167031 : ℕ)^4163*50000000000000^3139 ≤ 20846495954819^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585167031 5000000000 20846495954819 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6022305403/10000000000 : ℝ)^4163 ≤ (398756100247/781250000000 : ℝ)^3139 := by
    have hnat : (6022305403 : ℕ)^4163*781250000000^3139 ≤ 398756100247^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022305403 10000000000 398756100247 781250000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276968359/2000000000 : ℝ)^4163 ≤ (7266227244463/100000000000000 : ℝ)^3139 := by
    have hnat : (276968359 : ℕ)^4163*100000000000000^3139 ≤ 7266227244463^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276968359 2000000000 7266227244463 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585167031/5000000000 : ℝ), (6022305403/10000000000 : ℝ), (-276968359/2000000000 : ℝ)] ![(20846495954819/50000000000000 : ℝ), (398756100247/781250000000 : ℝ), (7266227244463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585167031/5000000000 : ℝ)|^4163 ≤ (20846495954819/50000000000000 : ℝ)^3139
        have hw : |(2585167031/5000000000 : ℝ)|=(2585167031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6022305403/10000000000 : ℝ)|^4163 ≤ (398756100247/781250000000 : ℝ)^3139
        have hw : |(6022305403/10000000000 : ℝ)|=(6022305403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276968359/2000000000 : ℝ)|^4163 ≤ (7266227244463/100000000000000 : ℝ)^3139
        have hw : |(-276968359/2000000000 : ℝ)|=(276968359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s0_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211991461/10000000000 : ℝ)*x 0 + (1118459067/2000000000 : ℝ)*x 1 + (1594617419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211991461/10000000000 : ℝ)^4163 ≤ (6353577504037/20000000000000 : ℝ)^3139 := by
    have hnat : (4211991461 : ℕ)^4163*20000000000000^3139 ≤ 6353577504037^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211991461 10000000000 6353577504037 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118459067/2000000000 : ℝ)^4163 ≤ (46264653007347/100000000000000 : ℝ)^3139 := by
    have hnat : (1118459067 : ℕ)^4163*100000000000000^3139 ≤ 46264653007347^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118459067 2000000000 46264653007347 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594617419/5000000000 : ℝ)^4163 ≤ (2745932432117/12500000000000 : ℝ)^3139 := by
    have hnat : (1594617419 : ℕ)^4163*12500000000000^3139 ≤ 2745932432117^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594617419 5000000000 2745932432117 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211991461/10000000000 : ℝ), (1118459067/2000000000 : ℝ), (1594617419/5000000000 : ℝ)] ![(6353577504037/20000000000000 : ℝ), (46264653007347/100000000000000 : ℝ), (2745932432117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211991461/10000000000 : ℝ)|^4163 ≤ (6353577504037/20000000000000 : ℝ)^3139
        have hw : |(4211991461/10000000000 : ℝ)|=(4211991461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118459067/2000000000 : ℝ)|^4163 ≤ (46264653007347/100000000000000 : ℝ)^3139
        have hw : |(1118459067/2000000000 : ℝ)|=(1118459067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594617419/5000000000 : ℝ)|^4163 ≤ (2745932432117/12500000000000 : ℝ)^3139
        have hw : |(1594617419/5000000000 : ℝ)|=(1594617419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (47/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (557/2000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8325/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8325 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8325*1^2048 ≤ 0^2048*1^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8325/2048 : ℝ) ≤ (1206055201046820969/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8325 ≤ (1206055201046820969/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8325*50000000000000000000^2048 ≤ 1206055201046820969^2048*5^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1206055201046820969 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1206055201046820969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8325 := by
      have hnat : (1 : ℕ)^2048*1^8325 ≤ 1^8325*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51206055201046820969/50000000000000000000 : ℝ) ≤ (125735090536763/125000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (51206055201046820969/50000000000000000000 : ℝ)^2048 ≤ (125735090536763/125000000000000 : ℝ)^8325 := by
      have hnat : (51206055201046820969 : ℕ)^2048*125000000000000^8325 ≤ 125735090536763^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51206055201046820969 50000000000000000000 125735090536763 125000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125735090536763/125000000000000 : ℝ)) (X := (51206055201046820969/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26206055201046820969/25000000000000000000 : ℝ) ≤ (63235090536763/62500000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (26206055201046820969/25000000000000000000 : ℝ)^2048 ≤ (63235090536763/62500000000000 : ℝ)^8325 := by
      have hnat : (26206055201046820969 : ℕ)^2048*62500000000000^8325 ≤ 63235090536763^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26206055201046820969 25000000000000000000 63235090536763 62500000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (63235090536763/62500000000000 : ℝ)) (X := (26206055201046820969/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(735090536763/50000000000000 : ℝ)*(0 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(735090536763/50000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1206055201046820969/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(735090536763/50000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (1 : ℝ)+(735090536763/50000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(125735090536763/125000000000000 : ℝ) by norm_num, show 1+(1206055201046820969/50000000000000000000 : ℝ)+(0 : ℝ)=(51206055201046820969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1206055201046820969/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(735090536763/50000000000000 : ℝ)*(2/5 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(735090536763/50000000000000 : ℝ)*(2/5 : ℝ)=(63235090536763/62500000000000 : ℝ) by norm_num, show 1+2*(1206055201046820969/50000000000000000000 : ℝ)=(26206055201046820969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(735090536763/50000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (735090536763/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(735090536763/50000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (735090536763/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(735090536763/50000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (735090536763/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-947331427/5000000000 : ℝ)*X 0 0+(757051561/1250000000 : ℝ)*X 0 1+(2389666453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517299447/10000000000 : ℝ)*X 1 0+(-2627815293/10000000000 : ℝ)*X 1 1+(1194833347/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2758651391/5000000000 : ℝ)*X 2 0+(4779332041/10000000000 : ℝ)*X 2 1+(-2627812681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4201720193/10000000000 : ℝ)*X 0 0+(1560749281/5000000000 : ℝ)*X 0 1+(22630927/40000000 : ℝ)*X 0 2+(4201720193/10000000000 : ℝ)*X 1 0+(1560749281/5000000000 : ℝ)*X 1 1+(22630927/40000000 : ℝ)*X 1 2+(4201720193/10000000000 : ℝ)*X 2 0+(1560749281/5000000000 : ℝ)*X 2 1+(22630927/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-94991729/500000000 : ℝ)*X 0 0+(4812282387/10000000000 : ℝ)*X 0 1+(752788187/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170334043/10000000000 : ℝ)*X 1 0+(-346210457/2500000000 : ℝ)*X 1 1+(6022305401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585167031/5000000000 : ℝ)*X 2 0+(6022305403/10000000000 : ℝ)*X 2 1+(-276968359/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211991461/10000000000 : ℝ)*X 0 0+(1118459067/2000000000 : ℝ)*X 0 1+(1594617419/5000000000 : ℝ)*X 0 2+(4211991461/10000000000 : ℝ)*X 1 0+(1118459067/2000000000 : ℝ)*X 1 1+(1594617419/5000000000 : ℝ)*X 1 2+(4211991461/10000000000 : ℝ)*X 2 0+(1118459067/2000000000 : ℝ)*X 2 1+(1594617419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1906657772494665356823/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (50418251/100000000000000 : ℝ)*(base1) + (1636121281/100000000000000 : ℝ)*(base19) + (437074349/25000000000000 : ℝ)*(base23) + (361143919/100000000000000 : ℝ)*(base24) + (5244761/1250000000000 : ℝ)*(upper3) + (588667663110461/100000000000000 : ℝ)*(major0) + (588667663110461/100000000000000 : ℝ)*(major1) + (588667663110461/100000000000000 : ℝ)*(major2) + (783041541207881/100000000000000 : ℝ)*(sp0) + (783043460779309/100000000000000 : ℝ)*(sp1) + (31321719498371/4000000000000 : ℝ)*(sp2) + (394286899154551/100000000000000 : ℝ)*(sp3) + (45076387/1250000000000 : ℝ)*(sp4) + (3076370697/100000000000000 : ℝ)*(sp7) + (394290025943499/100000000000000 : ℝ)*(f.failure) + (78304509690059/10000000000000 : ℝ)*(f.sum) + (3002106662743/2500000000000000000000000000 : ℝ)*base65 + (24659982352743/5000000000000000000000000000 : ℝ)*base67 + (4290126967743/5000000000000000000000000000 : ℝ)*base69 + (9961106462743/5000000000000000000000000000 : ℝ)*base71 + (5535946327743/2500000000000000000000000000 : ℝ)*base73 + (25492124237743/5000000000000000000000000000 : ℝ)*base75 + (3288801827743/5000000000000000000000000000 : ℝ)*base77 + (31049728217743/5000000000000000000000000000 : ℝ)*base79 + (390274774757/2500000000000000000000000000 : ℝ)*base82 + (32038637/10000000000000000000000 : ℝ)*base90 + (32038637/10000000000000000000000 : ℝ)*base92 + (32038637/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4005642395330845659/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (19084223/20000000000000 : ℝ)*(base1) + (247005767/12500000000000 : ℝ)*(base19) + (1978464239/100000000000000 : ℝ)*(base23) + (27329579/12500000000000 : ℝ)*(upper3) + (22945637/10000000000000 : ℝ)*(upper5) + (155320851845897/25000000000000 : ℝ)*(major0) + (155320851845897/25000000000000 : ℝ)*(major1) + (155320851845897/25000000000000 : ℝ)*(major2) + (4039170361/100000000000000 : ℝ)*(sp1) + (201495489/5000000000000 : ℝ)*(sp2) + (82643056812961/10000000000000 : ℝ)*(sp4) + (413212228745999/50000000000000 : ℝ)*(sp5) + (206606116083619/25000000000000 : ℝ)*(sp6) + (26008498724671/6250000000000 : ℝ)*(sp7) + (416136075015851/100000000000000 : ℝ)*(f.failure) + (165286094541699/20000000000000 : ℝ)*(f.sum) + (220307973589/625000000000000000000000000 : ℝ)*base66 + (6999330326089/1250000000000000000000000000 : ℝ)*base68 + (9430152551411/1250000000000000000000000000 : ℝ)*base69 + (10554929740161/1250000000000000000000000000 : ℝ)*base71 + (57904206101/9765625000000000000000000 : ℝ)*base74 + (411919581089/1250000000000000000000000000 : ℝ)*base76 + (6700990751411/1250000000000000000000000000 : ℝ)*base77 + (786850001411/1250000000000000000000000000 : ℝ)*base79 + (1338546606411/625000000000000000000000000 : ℝ)*base81 + (230413/10000000000000000000000 : ℝ)*base90 + (230413/10000000000000000000000 : ℝ)*base92 + (230413/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (557/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1133_s1_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419994723/2000000000 : ℝ)*x 0 + (5703932777/10000000000 : ℝ)*x 1 + (500036921/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419994723/2000000000 : ℝ)^4163 ≤ (3155349234169/25000000000000 : ℝ)^3139 := by
    have hnat : (419994723 : ℕ)^4163*25000000000000^3139 ≤ 3155349234169^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419994723 2000000000 3155349234169 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5703932777/10000000000 : ℝ)^4163 ≤ (4749347712393/10000000000000 : ℝ)^3139 := by
    have hnat : (5703932777 : ℕ)^4163*10000000000000^3139 ≤ 4749347712393^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5703932777 10000000000 4749347712393 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500036921/1000000000 : ℝ)^4163 ≤ (39885125924421/100000000000000 : ℝ)^3139 := by
    have hnat : (500036921 : ℕ)^4163*100000000000000^3139 ≤ 39885125924421^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500036921 1000000000 39885125924421 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419994723/2000000000 : ℝ), (5703932777/10000000000 : ℝ), (500036921/1000000000 : ℝ)] ![(3155349234169/25000000000000 : ℝ), (4749347712393/10000000000000 : ℝ), (39885125924421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419994723/2000000000 : ℝ)|^4163 ≤ (3155349234169/25000000000000 : ℝ)^3139
        have hw : |(-419994723/2000000000 : ℝ)|=(419994723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5703932777/10000000000 : ℝ)|^4163 ≤ (4749347712393/10000000000000 : ℝ)^3139
        have hw : |(5703932777/10000000000 : ℝ)|=(5703932777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500036921/1000000000 : ℝ)|^4163 ≤ (39885125924421/100000000000000 : ℝ)^3139
        have hw : |(500036921/1000000000 : ℝ)|=(500036921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (677452469/1250000000 : ℝ)*x 0 + (-247983071/1000000000 : ℝ)*x 1 + (5000368709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677452469/1250000000 : ℝ)^4163 ≤ (355037722931/800000000000 : ℝ)^3139 := by
    have hnat : (677452469 : ℕ)^4163*800000000000^3139 ≤ 355037722931^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677452469 1250000000 355037722931 800000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247983071/1000000000 : ℝ)^4163 ≤ (15735163990731/100000000000000 : ℝ)^3139 := by
    have hnat : (247983071 : ℕ)^4163*100000000000000^3139 ≤ 15735163990731^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247983071 1000000000 15735163990731 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5000368709/10000000000 : ℝ)^4163 ≤ (19942560312297/50000000000000 : ℝ)^3139 := by
    have hnat : (5000368709 : ℕ)^4163*50000000000000^3139 ≤ 19942560312297^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5000368709 10000000000 19942560312297 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677452469/1250000000 : ℝ), (-247983071/1000000000 : ℝ), (5000368709/10000000000 : ℝ)] ![(355037722931/800000000000 : ℝ), (15735163990731/100000000000000 : ℝ), (19942560312297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677452469/1250000000 : ℝ)|^4163 ≤ (355037722931/800000000000 : ℝ)^3139
        have hw : |(677452469/1250000000 : ℝ)|=(677452469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247983071/1000000000 : ℝ)|^4163 ≤ (15735163990731/100000000000000 : ℝ)^3139
        have hw : |(-247983071/1000000000 : ℝ)|=(247983071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5000368709/10000000000 : ℝ)|^4163 ≤ (19942560312297/50000000000000 : ℝ)^3139
        have hw : |(5000368709/10000000000 : ℝ)|=(5000368709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354905383/2500000000 : ℝ)*x 0 + (1250091779/2500000000 : ℝ)*x 1 + (-2479830417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354905383/2500000000 : ℝ)^4163 ≤ (44379734697219/100000000000000 : ℝ)^3139 := by
    have hnat : (1354905383 : ℕ)^4163*100000000000000^3139 ≤ 44379734697219^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354905383 2500000000 44379734697219 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250091779/2500000000 : ℝ)^4163 ≤ (39885103773049/100000000000000 : ℝ)^3139 := by
    have hnat : (1250091779 : ℕ)^4163*100000000000000^3139 ≤ 39885103773049^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250091779 2500000000 39885103773049 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2479830417/10000000000 : ℝ)^4163 ≤ (7867580762539/50000000000000 : ℝ)^3139 := by
    have hnat : (2479830417 : ℕ)^4163*50000000000000^3139 ≤ 7867580762539^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479830417 10000000000 7867580762539 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354905383/2500000000 : ℝ), (1250091779/2500000000 : ℝ), (-2479830417/10000000000 : ℝ)] ![(44379734697219/100000000000000 : ℝ), (39885103773049/100000000000000 : ℝ), (7867580762539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354905383/2500000000 : ℝ)|^4163 ≤ (44379734697219/100000000000000 : ℝ)^3139
        have hw : |(1354905383/2500000000 : ℝ)|=(1354905383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250091779/2500000000 : ℝ)|^4163 ≤ (39885103773049/100000000000000 : ℝ)^3139
        have hw : |(1250091779/2500000000 : ℝ)|=(1250091779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2479830417/10000000000 : ℝ)|^4163 ≤ (7867580762539/50000000000000 : ℝ)^3139
        have hw : |(-2479830417/10000000000 : ℝ)|=(2479830417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159098291/5000000000 : ℝ)*x 0 + (183766177/500000000 : ℝ)*x 1 + (5072572353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159098291/5000000000 : ℝ)^4163 ≤ (32834566993563/100000000000000 : ℝ)^3139 := by
    have hnat : (2159098291 : ℕ)^4163*100000000000000^3139 ≤ 32834566993563^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159098291 5000000000 32834566993563 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183766177/500000000 : ℝ)^4163 ≤ (26514713166397/100000000000000 : ℝ)^3139 := by
    have hnat : (183766177 : ℕ)^4163*100000000000000^3139 ≤ 26514713166397^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183766177 500000000 26514713166397 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5072572353/10000000000 : ℝ)^4163 ≤ (40650719821591/100000000000000 : ℝ)^3139 := by
    have hnat : (5072572353 : ℕ)^4163*100000000000000^3139 ≤ 40650719821591^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072572353 10000000000 40650719821591 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159098291/5000000000 : ℝ), (183766177/500000000 : ℝ), (5072572353/10000000000 : ℝ)] ![(32834566993563/100000000000000 : ℝ), (26514713166397/100000000000000 : ℝ), (40650719821591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159098291/5000000000 : ℝ)|^4163 ≤ (32834566993563/100000000000000 : ℝ)^3139
        have hw : |(2159098291/5000000000 : ℝ)|=(2159098291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183766177/500000000 : ℝ)|^4163 ≤ (26514713166397/100000000000000 : ℝ)^3139
        have hw : |(183766177/500000000 : ℝ)|=(183766177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5072572353/10000000000 : ℝ)|^4163 ≤ (40650719821591/100000000000000 : ℝ)^3139
        have hw : |(5072572353/10000000000 : ℝ)|=(5072572353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100792711/10000000000 : ℝ)*x 0 + (313125563/625000000 : ℝ)*x 1 + (2847050621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100792711/10000000000 : ℝ)^4163 ≤ (12627926304193/100000000000000 : ℝ)^3139 := by
    have hnat : (2100792711 : ℕ)^4163*100000000000000^3139 ≤ 12627926304193^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100792711 10000000000 12627926304193 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313125563/625000000 : ℝ)^4163 ≤ (7997426511119/20000000000000 : ℝ)^3139 := by
    have hnat : (313125563 : ℕ)^4163*20000000000000^3139 ≤ 7997426511119^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313125563 625000000 7997426511119 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847050621/5000000000 : ℝ)^4163 ≤ (47384941119427/100000000000000 : ℝ)^3139 := by
    have hnat : (2847050621 : ℕ)^4163*100000000000000^3139 ≤ 47384941119427^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847050621 5000000000 47384941119427 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100792711/10000000000 : ℝ), (313125563/625000000 : ℝ), (2847050621/5000000000 : ℝ)] ![(12627926304193/100000000000000 : ℝ), (7997426511119/20000000000000 : ℝ), (47384941119427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100792711/10000000000 : ℝ)|^4163 ≤ (12627926304193/100000000000000 : ℝ)^3139
        have hw : |(-2100792711/10000000000 : ℝ)|=(2100792711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313125563/625000000 : ℝ)|^4163 ≤ (7997426511119/20000000000000 : ℝ)^3139
        have hw : |(313125563/625000000 : ℝ)|=(313125563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847050621/5000000000 : ℝ)|^4163 ≤ (47384941119427/100000000000000 : ℝ)^3139
        have hw : |(2847050621/5000000000 : ℝ)|=(2847050621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1309830061/2500000000 : ℝ)*x 0 + (-893048921/5000000000 : ℝ)*x 1 + (2847050481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309830061/2500000000 : ℝ)^4163 ≤ (21216181943931/50000000000000 : ℝ)^3139 := by
    have hnat : (1309830061 : ℕ)^4163*50000000000000^3139 ≤ 21216181943931^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309830061 2500000000 21216181943931 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893048921/5000000000 : ℝ)^4163 ≤ (2545674517279/25000000000000 : ℝ)^3139 := by
    have hnat : (893048921 : ℕ)^4163*25000000000000^3139 ≤ 2545674517279^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893048921 5000000000 2545674517279 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847050481/5000000000 : ℝ)^4163 ≤ (9476987605843/20000000000000 : ℝ)^3139 := by
    have hnat : (2847050481 : ℕ)^4163*20000000000000^3139 ≤ 9476987605843^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847050481 5000000000 9476987605843 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309830061/2500000000 : ℝ), (-893048921/5000000000 : ℝ), (2847050481/5000000000 : ℝ)] ![(21216181943931/50000000000000 : ℝ), (2545674517279/25000000000000 : ℝ), (9476987605843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309830061/2500000000 : ℝ)|^4163 ≤ (21216181943931/50000000000000 : ℝ)^3139
        have hw : |(1309830061/2500000000 : ℝ)|=(1309830061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893048921/5000000000 : ℝ)|^4163 ≤ (2545674517279/25000000000000 : ℝ)^3139
        have hw : |(-893048921/5000000000 : ℝ)|=(893048921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847050481/5000000000 : ℝ)|^4163 ≤ (9476987605843/20000000000000 : ℝ)^3139
        have hw : |(2847050481/5000000000 : ℝ)|=(2847050481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5239320293/10000000000 : ℝ)*x 0 + (284705057/500000000 : ℝ)*x 1 + (-223262189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239320293/10000000000 : ℝ)^4163 ≤ (21216182207081/50000000000000 : ℝ)^3139 := by
    have hnat : (5239320293 : ℕ)^4163*50000000000000^3139 ≤ 21216182207081^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239320293 10000000000 21216182207081 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284705057/500000000 : ℝ)^4163 ≤ (47384939993707/100000000000000 : ℝ)^3139 := by
    have hnat : (284705057 : ℕ)^4163*100000000000000^3139 ≤ 47384939993707^3139*500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284705057 500000000 47384939993707 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223262189/1250000000 : ℝ)^4163 ≤ (1272836946753/12500000000000 : ℝ)^3139 := by
    have hnat : (223262189 : ℕ)^4163*12500000000000^3139 ≤ 1272836946753^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223262189 1250000000 1272836946753 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239320293/10000000000 : ℝ), (284705057/500000000 : ℝ), (-223262189/1250000000 : ℝ)] ![(21216182207081/50000000000000 : ℝ), (47384939993707/100000000000000 : ℝ), (1272836946753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239320293/10000000000 : ℝ)|^4163 ≤ (21216182207081/50000000000000 : ℝ)^3139
        have hw : |(5239320293/10000000000 : ℝ)|=(5239320293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284705057/500000000 : ℝ)|^4163 ≤ (47384939993707/100000000000000 : ℝ)^3139
        have hw : |(284705057/500000000 : ℝ)|=(284705057/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223262189/1250000000 : ℝ)|^4163 ≤ (1272836946753/12500000000000 : ℝ)^3139
        have hw : |(-223262189/1250000000 : ℝ)|=(223262189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s1_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319819997/10000000000 : ℝ)*x 0 + (1263357249/2500000000 : ℝ)*x 1 + (923711859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319819997/10000000000 : ℝ)^4163 ≤ (1642546946711/5000000000000 : ℝ)^3139 := by
    have hnat : (4319819997 : ℕ)^4163*5000000000000^3139 ≤ 1642546946711^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319819997 10000000000 1642546946711 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263357249/2500000000 : ℝ)^4163 ≤ (4044738791121/10000000000000 : ℝ)^3139 := by
    have hnat : (1263357249 : ℕ)^4163*10000000000000^3139 ≤ 4044738791121^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263357249 2500000000 4044738791121 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923711859/2500000000 : ℝ)^4163 ≤ (26701673135277/100000000000000 : ℝ)^3139 := by
    have hnat : (923711859 : ℕ)^4163*100000000000000^3139 ≤ 26701673135277^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923711859 2500000000 26701673135277 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319819997/10000000000 : ℝ), (1263357249/2500000000 : ℝ), (923711859/2500000000 : ℝ)] ![(1642546946711/5000000000000 : ℝ), (4044738791121/10000000000000 : ℝ), (26701673135277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319819997/10000000000 : ℝ)|^4163 ≤ (1642546946711/5000000000000 : ℝ)^3139
        have hw : |(4319819997/10000000000 : ℝ)|=(4319819997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1263357249/2500000000 : ℝ)|^4163 ≤ (4044738791121/10000000000000 : ℝ)^3139
        have hw : |(1263357249/2500000000 : ℝ)|=(1263357249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923711859/2500000000 : ℝ)|^4163 ≤ (26701673135277/100000000000000 : ℝ)^3139
        have hw : |(923711859/2500000000 : ℝ)|=(923711859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (557/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10239/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (557/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (47/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (557/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (47/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (557/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (47/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (557/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (47/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (557/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (47/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (557/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (47/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (47/12500 : ℝ) ^ (8325/2048 : ℝ) ≤ (6954255983/50000000000000000000 : ℝ) := by
    have hpowers : (47/12500 : ℝ)^8325 ≤ (6954255983/50000000000000000000 : ℝ)^2048 := by
      have hnat : (47 : ℕ)^8325*50000000000000000000^2048 ≤ 6954255983^2048*12500^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47 12500 6954255983 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47/12500 : ℝ)) (X := (6954255983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (557/2000 : ℝ) ^ (8325/2048 : ℝ) ≤ (553664866623047099/100000000000000000000 : ℝ) := by
    have hpowers : (557/2000 : ℝ)^8325 ≤ (553664866623047099/100000000000000000000 : ℝ)^2048 := by
      have hnat : (557 : ℕ)^8325*100000000000000000000^2048 ≤ 553664866623047099^2048*2000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        557 2000 553664866623047099 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (557/2000 : ℝ)) (X := (553664866623047099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000006954255983/25000000000000000000 : ℝ) ≤ (2500000000171079/2500000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25000000006954255983/25000000000000000000 : ℝ)^2048 ≤ (2500000000171079/2500000000000000 : ℝ)^8325 := by
      have hnat : (25000000006954255983 : ℕ)^2048*2500000000000000^8325 ≤ 2500000000171079^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000006954255983 25000000000000000000 2500000000171079 2500000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000171079/2500000000000000 : ℝ)) (X := (25000000006954255983/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20110732976106311813/20000000000000000000 : ℝ) ≤ (5006796075114057/5000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (20110732976106311813/20000000000000000000 : ℝ)^2048 ≤ (5006796075114057/5000000000000000 : ℝ)^8325 := by
      have hnat : (20110732976106311813 : ℕ)^2048*5000000000000000^8325 ≤ 5006796075114057^8325*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20110732976106311813 20000000000000000000 5006796075114057 5000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006796075114057/5000000000000000 : ℝ)) (X := (20110732976106311813/20000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50553664866623047099/50000000000000000000 : ℝ) ≤ (1253398037471489/1250000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50553664866623047099/50000000000000000000 : ℝ)^2048 ≤ (1253398037471489/1250000000000000 : ℝ)^8325 := by
      have hnat : (50553664866623047099 : ℕ)^2048*1250000000000000^8325 ≤ 1253398037471489^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50553664866623047099 50000000000000000000 1253398037471489 1250000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253398037471489/1250000000000000 : ℝ)) (X := (50553664866623047099/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6954255983/50000000000000000000 : ℝ) ≤ ((34341222340292995211/34342500000000000000 : ℝ)+2*(6796074771899/1373700000000000 : ℝ)*(47/12500 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (34341222340292995211/34342500000000000000 : ℝ)+2*(6796074771899/1373700000000000 : ℝ)*(47/12500 : ℝ)=(2500000000171079/2500000000000000 : ℝ) by norm_num, show 1+2*(6954255983/50000000000000000000 : ℝ)=(25000000006954255983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(553664866623047099/100000000000000000000 : ℝ)+(6954255983/50000000000000000000 : ℝ) ≤ ((34341222340292995211/34342500000000000000 : ℝ)+(6796074771899/1373700000000000 : ℝ)*((557/2000 : ℝ)+(47/12500 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (34341222340292995211/34342500000000000000 : ℝ)+(6796074771899/1373700000000000 : ℝ)*((557/2000 : ℝ)+(47/12500 : ℝ))=(5006796075114057/5000000000000000 : ℝ) by norm_num, show 1+(553664866623047099/100000000000000000000 : ℝ)+(6954255983/50000000000000000000 : ℝ)=(20110732976106311813/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(553664866623047099/100000000000000000000 : ℝ) ≤ ((34341222340292995211/34342500000000000000 : ℝ)+2*(6796074771899/1373700000000000 : ℝ)*(557/2000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (34341222340292995211/34342500000000000000 : ℝ)+2*(6796074771899/1373700000000000 : ℝ)*(557/2000 : ℝ)=(1253398037471489/1250000000000000 : ℝ) by norm_num, show 1+2*(553664866623047099/100000000000000000000 : ℝ)=(50553664866623047099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34341222340292995211/34342500000000000000 : ℝ)*(X 1 0+X 2 0)+(6796074771899/1373700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (47/12500 : ℝ)) (hi := (557/2000 : ℝ)) (c := (34341222340292995211/34342500000000000000 : ℝ)) (alpha := (6796074771899/1373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34341222340292995211/34342500000000000000 : ℝ)*(X 0 1+X 2 1)+(6796074771899/1373700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (47/12500 : ℝ)) (hi := (557/2000 : ℝ)) (c := (34341222340292995211/34342500000000000000 : ℝ)) (alpha := (6796074771899/1373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34341222340292995211/34342500000000000000 : ℝ)*(X 0 2+X 1 2)+(6796074771899/1373700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (47/12500 : ℝ)) (hi := (557/2000 : ℝ)) (c := (34341222340292995211/34342500000000000000 : ℝ)) (alpha := (6796074771899/1373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419994723/2000000000 : ℝ)*X 0 0+(5703932777/10000000000 : ℝ)*X 0 1+(500036921/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677452469/1250000000 : ℝ)*X 1 0+(-247983071/1000000000 : ℝ)*X 1 1+(5000368709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354905383/2500000000 : ℝ)*X 2 0+(1250091779/2500000000 : ℝ)*X 2 1+(-2479830417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159098291/5000000000 : ℝ)*X 0 0+(183766177/500000000 : ℝ)*X 0 1+(5072572353/10000000000 : ℝ)*X 0 2+(2159098291/5000000000 : ℝ)*X 1 0+(183766177/500000000 : ℝ)*X 1 1+(5072572353/10000000000 : ℝ)*X 1 2+(2159098291/5000000000 : ℝ)*X 2 0+(183766177/500000000 : ℝ)*X 2 1+(5072572353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100792711/10000000000 : ℝ)*X 0 0+(313125563/625000000 : ℝ)*X 0 1+(2847050621/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309830061/2500000000 : ℝ)*X 1 0+(-893048921/5000000000 : ℝ)*X 1 1+(2847050481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239320293/10000000000 : ℝ)*X 2 0+(284705057/500000000 : ℝ)*X 2 1+(-223262189/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319819997/10000000000 : ℝ)*X 0 0+(1263357249/2500000000 : ℝ)*X 0 1+(923711859/2500000000 : ℝ)*X 0 2+(4319819997/10000000000 : ℝ)*X 1 0+(1263357249/2500000000 : ℝ)*X 1 1+(923711859/2500000000 : ℝ)*X 1 2+(4319819997/10000000000 : ℝ)*X 2 0+(1263357249/2500000000 : ℝ)*X 2 1+(923711859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2100577733509281756115660011/572375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6946207/2000000000000 : ℝ)*(base1) + (420312239/100000000000000 : ℝ)*(base19) + (235249869/25000000000000 : ℝ)*(base23) + (102014507/100000000000000 : ℝ)*(base37) + (3463811/12500000000000 : ℝ)*(upper3) + (1068513699388199/100000000000000 : ℝ)*(major0) + (1068513699388199/100000000000000 : ℝ)*(major1) + (1068513699388199/100000000000000 : ℝ)*(major2) + (355333914256807/25000000000000 : ℝ)*(sp0) + (22208343581997/1562500000000 : ℝ)*(sp1) + (177666885976597/12500000000000 : ℝ)*(sp2) + (22365337447131/3125000000000 : ℝ)*(sp3) + (5752763/800000000000 : ℝ)*(sp4) + (404813051/25000000000000 : ℝ)*(sp5) + (715691247633049/100000000000000 : ℝ)*(f.failure) + (355334007203063/25000000000000 : ℝ)*(f.sum) + (99030916021043/34342500000000000000000000000 : ℝ)*base65 + (9955222582848560011/3434250000000000000000000000000000 : ℝ)*base68 + (7053939232121060011/3434250000000000000000000000000000 : ℝ)*base70 + (21601787120126439989/3434250000000000000000000000000000 : ℝ)*base71 + (29224617235019/68685000000000000000000000000 : ℝ)*base74 + (43909456785596439989/3434250000000000000000000000000000 : ℝ)*base75 + (10694707202306439989/3434250000000000000000000000000000 : ℝ)*base77 + (7410804820946439989/3434250000000000000000000000000000 : ℝ)*base79 + (173334594301861/68685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (24670287/10000000000000000000000 : ℝ)*base90 + (24670287/10000000000000000000000 : ℝ)*base92 + (24670287/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32035195625584526011559397/11447500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41167427/100000000000000 : ℝ)*(base1) + (643434949/100000000000000 : ℝ)*(base19) + (339677919/50000000000000 : ℝ)*(base23) + (6252447/12500000000000 : ℝ)*(upper3) + (7367891/12500000000000 : ℝ)*(upper5) + (21978532766727/2000000000000 : ℝ)*(major0) + (21978532766727/2000000000000 : ℝ)*(major1) + (21978532766727/2000000000000 : ℝ)*(major2) + (73274717/3125000000000 : ℝ)*(sp1) + (747828961/25000000000000 : ℝ)*(sp2) + (1461791368450977/100000000000000 : ℝ)*(sp4) + (1461788339057657/100000000000000 : ℝ)*(sp5) + (365446914152967/25000000000000 : ℝ)*(sp6) + (736061814940229/100000000000000 : ℝ)*(sp7) + (147212371221531/20000000000000 : ℝ)*(f.failure) + (29235826545671/2000000000000 : ℝ)*(f.sum) + (744448279713/572375000000000000000000000 : ℝ)*base66 + (31725914362989799/22895000000000000000000000000000 : ℝ)*base67 + (106418746616320201/22895000000000000000000000000000 : ℝ)*base70 + (90957231820065201/22895000000000000000000000000000 : ℝ)*base72 + (90371907991/28618750000000000000000000 : ℝ)*base73 + (15622503784759799/22895000000000000000000000000000 : ℝ)*base75 + (94981168553785201/22895000000000000000000000000000 : ℝ)*base78 + (65516353587170201/22895000000000000000000000000000 : ℝ)*base80 + (720415505301/457900000000000000000000000 : ℝ)*base82 + (7412253/2000000000000000000000 : ℝ)*base90 + (7412253/2000000000000000000000 : ℝ)*base92 + (7412253/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1133_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (557/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10239/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1133_s2_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430739127/2000000000 : ℝ)*x 0 + (5512528533/10000000000 : ℝ)*x 1 + (5157621731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430739127/2000000000 : ℝ)^4163 ≤ (13051387740323/100000000000000 : ℝ)^3139 := by
    have hnat : (430739127 : ℕ)^4163*100000000000000^3139 ≤ 13051387740323^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430739127 2000000000 13051387740323 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512528533/10000000000 : ℝ)^4163 ≤ (22695758758697/50000000000000 : ℝ)^3139 := by
    have hnat : (5512528533 : ℕ)^4163*50000000000000^3139 ≤ 22695758758697^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512528533 10000000000 22695758758697 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5157621731/10000000000 : ℝ)^4163 ≤ (4155709472959/10000000000000 : ℝ)^3139 := by
    have hnat : (5157621731 : ℕ)^4163*10000000000000^3139 ≤ 4155709472959^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157621731 10000000000 4155709472959 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430739127/2000000000 : ℝ), (5512528533/10000000000 : ℝ), (5157621731/10000000000 : ℝ)] ![(13051387740323/100000000000000 : ℝ), (22695758758697/50000000000000 : ℝ), (4155709472959/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430739127/2000000000 : ℝ)|^4163 ≤ (13051387740323/100000000000000 : ℝ)^3139
        have hw : |(-430739127/2000000000 : ℝ)|=(430739127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512528533/10000000000 : ℝ)|^4163 ≤ (22695758758697/50000000000000 : ℝ)^3139
        have hw : |(5512528533/10000000000 : ℝ)|=(5512528533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5157621731/10000000000 : ℝ)|^4163 ≤ (4155709472959/10000000000000 : ℝ)^3139
        have hw : |(5157621731/10000000000 : ℝ)|=(5157621731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687125703/5000000000 : ℝ)*x 0 + (-1169138501/5000000000 : ℝ)*x 1 + (2578811763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687125703/5000000000 : ℝ)^4163 ≤ (43887688041547/100000000000000 : ℝ)^3139 := by
    have hnat : (2687125703 : ℕ)^4163*100000000000000^3139 ≤ 43887688041547^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687125703 5000000000 43887688041547 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1169138501/5000000000 : ℝ)^4163 ≤ (7277599013647/50000000000000 : ℝ)^3139 := by
    have hnat : (1169138501 : ℕ)^4163*50000000000000^3139 ≤ 7277599013647^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169138501 5000000000 7277599013647 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578811763/5000000000 : ℝ)^4163 ≤ (41557113910767/100000000000000 : ℝ)^3139 := by
    have hnat : (2578811763 : ℕ)^4163*100000000000000^3139 ≤ 41557113910767^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578811763 5000000000 41557113910767 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687125703/5000000000 : ℝ), (-1169138501/5000000000 : ℝ), (2578811763/5000000000 : ℝ)] ![(43887688041547/100000000000000 : ℝ), (7277599013647/50000000000000 : ℝ), (41557113910767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687125703/5000000000 : ℝ)|^4163 ≤ (43887688041547/100000000000000 : ℝ)^3139
        have hw : |(2687125703/5000000000 : ℝ)|=(2687125703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1169138501/5000000000 : ℝ)|^4163 ≤ (7277599013647/50000000000000 : ℝ)^3139
        have hw : |(-1169138501/5000000000 : ℝ)|=(1169138501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578811763/5000000000 : ℝ)|^4163 ≤ (41557113910767/100000000000000 : ℝ)^3139
        have hw : |(2578811763/5000000000 : ℝ)|=(2578811763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687125671/5000000000 : ℝ)*x 0 + (5157623507/10000000000 : ℝ)*x 1 + (-233827711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687125671/5000000000 : ℝ)^4163 ≤ (43887687348409/100000000000000 : ℝ)^3139 := by
    have hnat : (2687125671 : ℕ)^4163*100000000000000^3139 ≤ 43887687348409^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687125671 5000000000 43887687348409 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157623507/10000000000 : ℝ)^4163 ≤ (8311422741547/20000000000000 : ℝ)^3139 := by
    have hnat : (5157623507 : ℕ)^4163*20000000000000^3139 ≤ 8311422741547^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157623507 10000000000 8311422741547 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233827711/1000000000 : ℝ)^4163 ≤ (116441591351/800000000000 : ℝ)^3139 := by
    have hnat : (233827711 : ℕ)^4163*800000000000^3139 ≤ 116441591351^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233827711 1000000000 116441591351 800000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687125671/5000000000 : ℝ), (5157623507/10000000000 : ℝ), (-233827711/1000000000 : ℝ)] ![(43887687348409/100000000000000 : ℝ), (8311422741547/20000000000000 : ℝ), (116441591351/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687125671/5000000000 : ℝ)|^4163 ≤ (43887687348409/100000000000000 : ℝ)^3139
        have hw : |(2687125671/5000000000 : ℝ)|=(2687125671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157623507/10000000000 : ℝ)|^4163 ≤ (8311422741547/20000000000000 : ℝ)^3139
        have hw : |(5157623507/10000000000 : ℝ)|=(5157623507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233827711/1000000000 : ℝ)|^4163 ≤ (116441591351/800000000000 : ℝ)^3139
        have hw : |(-233827711/1000000000 : ℝ)|=(233827711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355029441/10000000000 : ℝ)*x 0 + (4016775727/10000000000 : ℝ)*x 1 + (1180400763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355029441/10000000000 : ℝ)^4163 ≤ (8301628712303/25000000000000 : ℝ)^3139 := by
    have hnat : (4355029441 : ℕ)^4163*25000000000000^3139 ≤ 8301628712303^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355029441 10000000000 8301628712303 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016775727/10000000000 : ℝ)^4163 ≤ (14915063672943/50000000000000 : ℝ)^3139 := by
    have hnat : (4016775727 : ℕ)^4163*50000000000000^3139 ≤ 14915063672943^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016775727 10000000000 14915063672943 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180400763/2500000000 : ℝ)^4163 ≤ (739267156043/2000000000000 : ℝ)^3139 := by
    have hnat : (1180400763 : ℕ)^4163*2000000000000^3139 ≤ 739267156043^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180400763 2500000000 739267156043 2000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355029441/10000000000 : ℝ), (4016775727/10000000000 : ℝ), (1180400763/2500000000 : ℝ)] ![(8301628712303/25000000000000 : ℝ), (14915063672943/50000000000000 : ℝ), (739267156043/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355029441/10000000000 : ℝ)|^4163 ≤ (8301628712303/25000000000000 : ℝ)^3139
        have hw : |(4355029441/10000000000 : ℝ)|=(4355029441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016775727/10000000000 : ℝ)|^4163 ≤ (14915063672943/50000000000000 : ℝ)^3139
        have hw : |(4016775727/10000000000 : ℝ)|=(4016775727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1180400763/2500000000 : ℝ)|^4163 ≤ (739267156043/2000000000000 : ℝ)^3139
        have hw : |(1180400763/2500000000 : ℝ)|=(1180400763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-538450197/2500000000 : ℝ)*x 0 + (5160084647/10000000000 : ℝ)*x 1 + (22040163/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538450197/2500000000 : ℝ)^4163 ≤ (13052232849049/100000000000000 : ℝ)^3139 := by
    have hnat : (538450197 : ℕ)^4163*100000000000000^3139 ≤ 13052232849049^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538450197 2500000000 13052232849049 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5160084647/10000000000 : ℝ)^4163 ≤ (10395853808509/25000000000000 : ℝ)^3139 := by
    have hnat : (5160084647 : ℕ)^4163*25000000000000^3139 ≤ 10395853808509^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160084647 10000000000 10395853808509 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22040163/40000000 : ℝ)^4163 ≤ (22682175953441/50000000000000 : ℝ)^3139 := by
    have hnat : (22040163 : ℕ)^4163*50000000000000^3139 ≤ 22682175953441^3139*40000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22040163 40000000 22682175953441 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538450197/2500000000 : ℝ), (5160084647/10000000000 : ℝ), (22040163/40000000 : ℝ)] ![(13052232849049/100000000000000 : ℝ), (10395853808509/25000000000000 : ℝ), (22682175953441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538450197/2500000000 : ℝ)|^4163 ≤ (13052232849049/100000000000000 : ℝ)^3139
        have hw : |(-538450197/2500000000 : ℝ)|=(538450197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5160084647/10000000000 : ℝ)|^4163 ≤ (10395853808509/25000000000000 : ℝ)^3139
        have hw : |(5160084647/10000000000 : ℝ)|=(5160084647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22040163/40000000 : ℝ)|^4163 ≤ (22682175953441/50000000000000 : ℝ)^3139
        have hw : |(22040163/40000000 : ℝ)|=(22040163/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528425641/1000000000 : ℝ)*x 0 + (-248232241/1250000000 : ℝ)*x 1 + (5510041349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528425641/1000000000 : ℝ)^4163 ≤ (5364461124417/12500000000000 : ℝ)^3139 := by
    have hnat : (528425641 : ℕ)^4163*12500000000000^3139 ≤ 5364461124417^3139*1000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528425641 1000000000 5364461124417 12500000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248232241/1250000000 : ℝ)^4163 ≤ (585997627023/5000000000000 : ℝ)^3139 := by
    have hnat : (248232241 : ℕ)^4163*5000000000000^3139 ≤ 585997627023^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248232241 1250000000 585997627023 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510041349/10000000000 : ℝ)^4163 ≤ (11341089611811/25000000000000 : ℝ)^3139 := by
    have hnat : (5510041349 : ℕ)^4163*25000000000000^3139 ≤ 11341089611811^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510041349 10000000000 11341089611811 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528425641/1000000000 : ℝ), (-248232241/1250000000 : ℝ), (5510041349/10000000000 : ℝ)] ![(5364461124417/12500000000000 : ℝ), (585997627023/5000000000000 : ℝ), (11341089611811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528425641/1000000000 : ℝ)|^4163 ≤ (5364461124417/12500000000000 : ℝ)^3139
        have hw : |(528425641/1000000000 : ℝ)|=(528425641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248232241/1250000000 : ℝ)|^4163 ≤ (585997627023/5000000000000 : ℝ)^3139
        have hw : |(-248232241/1250000000 : ℝ)|=(248232241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510041349/10000000000 : ℝ)|^4163 ≤ (11341089611811/25000000000000 : ℝ)^3139
        have hw : |(5510041349/10000000000 : ℝ)|=(5510041349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642127533/5000000000 : ℝ)*x 0 + (688755149/1250000000 : ℝ)*x 1 + (-496464999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642127533/5000000000 : ℝ)^4163 ≤ (42915674519403/100000000000000 : ℝ)^3139 := by
    have hnat : (2642127533 : ℕ)^4163*100000000000000^3139 ≤ 42915674519403^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642127533 5000000000 42915674519403 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688755149/1250000000 : ℝ)^4163 ≤ (708818073953/1562500000000 : ℝ)^3139 := by
    have hnat : (688755149 : ℕ)^4163*1562500000000^3139 ≤ 708818073953^3139*1250000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688755149 1250000000 708818073953 1562500000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496464999/2500000000 : ℝ)^4163 ≤ (11719968726603/100000000000000 : ℝ)^3139 := by
    have hnat : (496464999 : ℕ)^4163*100000000000000^3139 ≤ 11719968726603^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496464999 2500000000 11719968726603 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642127533/5000000000 : ℝ), (688755149/1250000000 : ℝ), (-496464999/2500000000 : ℝ)] ![(42915674519403/100000000000000 : ℝ), (708818073953/1562500000000 : ℝ), (11719968726603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642127533/5000000000 : ℝ)|^4163 ≤ (42915674519403/100000000000000 : ℝ)^3139
        have hw : |(2642127533/5000000000 : ℝ)|=(2642127533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688755149/1250000000 : ℝ)|^4163 ≤ (708818073953/1562500000000 : ℝ)^3139
        have hw : |(688755149/1250000000 : ℝ)|=(688755149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496464999/2500000000 : ℝ)|^4163 ≤ (11719968726603/100000000000000 : ℝ)^3139
        have hw : |(-496464999/2500000000 : ℝ)|=(496464999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_s2_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177618821/5000000000 : ℝ)*x 0 + (943342657/2000000000 : ℝ)*x 1 + (4021714669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177618821/5000000000 : ℝ)^4163 ≤ (8302155060941/25000000000000 : ℝ)^3139 := by
    have hnat : (2177618821 : ℕ)^4163*25000000000000^3139 ≤ 8302155060941^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177618821 5000000000 8302155060941 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943342657/2000000000 : ℝ)^4163 ≤ (2307037434173/6250000000000 : ℝ)^3139 := by
    have hnat : (943342657 : ℕ)^4163*6250000000000^3139 ≤ 2307037434173^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943342657 2000000000 2307037434173 6250000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021714669/10000000000 : ℝ)^4163 ≤ (29878780792613/100000000000000 : ℝ)^3139 := by
    have hnat : (4021714669 : ℕ)^4163*100000000000000^3139 ≤ 29878780792613^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021714669 10000000000 29878780792613 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177618821/5000000000 : ℝ), (943342657/2000000000 : ℝ), (4021714669/10000000000 : ℝ)] ![(8302155060941/25000000000000 : ℝ), (2307037434173/6250000000000 : ℝ), (29878780792613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177618821/5000000000 : ℝ)|^4163 ≤ (8302155060941/25000000000000 : ℝ)^3139
        have hw : |(2177618821/5000000000 : ℝ)|=(2177618821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(943342657/2000000000 : ℝ)|^4163 ≤ (2307037434173/6250000000000 : ℝ)^3139
        have hw : |(943342657/2000000000 : ℝ)|=(943342657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021714669/10000000000 : ℝ)|^4163 ≤ (29878780792613/100000000000000 : ℝ)^3139
        have hw : |(4021714669/10000000000 : ℝ)|=(4021714669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10239/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9029/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16529/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10239/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10239/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10239/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10239/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10239/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10239/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5599/100000 : ℝ) ^ (8325/2048 : ℝ) ≤ (203742866452319/25000000000000000000 : ℝ) := by
    have hpowers : (5599/100000 : ℝ)^8325 ≤ (203742866452319/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5599 : ℕ)^8325*25000000000000000000^2048 ≤ 203742866452319^2048*100000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5599 100000 203742866452319 25000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5599/100000 : ℝ)) (X := (203742866452319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10239/50000 : ℝ) ^ (8325/2048 : ℝ) ≤ (79322099981750263/50000000000000000000 : ℝ) := by
    have hpowers : (10239/50000 : ℝ)^8325 ≤ (79322099981750263/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10239 : ℕ)^8325*50000000000000000000^2048 ≤ 79322099981750263^2048*50000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10239 50000 79322099981750263 50000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10239/50000 : ℝ)) (X := (79322099981750263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500203742866452319/12500000000000000000 : ℝ) ≤ (312501253041521/312500000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (12500203742866452319/12500000000000000000 : ℝ)^2048 ≤ (312501253041521/312500000000000 : ℝ)^8325 := by
      have hnat : (12500203742866452319 : ℕ)^2048*312500000000000^8325 ≤ 312501253041521^8325*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500203742866452319 12500000000000000000 312501253041521 312500000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501253041521/312500000000000 : ℝ)) (X := (12500203742866452319/12500000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50079729585714654901/50000000000000000000 : ℝ) ≤ (10003920435373879/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50079729585714654901/50000000000000000000 : ℝ)^2048 ≤ (10003920435373879/10000000000000000 : ℝ)^8325 := by
      have hnat : (50079729585714654901 : ℕ)^2048*10000000000000000^8325 ≤ 10003920435373879^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50079729585714654901 50000000000000000000 10003920435373879 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003920435373879/10000000000000000 : ℝ)) (X := (50079729585714654901/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25079322099981750263/25000000000000000000 : ℝ) ≤ (5003900386709543/5000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (25079322099981750263/25000000000000000000 : ℝ)^2048 ≤ (5003900386709543/5000000000000000 : ℝ)^8325 := by
      have hnat : (25079322099981750263 : ℕ)^2048*5000000000000000^8325 ≤ 5003900386709543^8325*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25079322099981750263 25000000000000000000 5003900386709543 5000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003900386709543/5000000000000000 : ℝ)) (X := (25079322099981750263/25000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(203742866452319/25000000000000000000 : ℝ) ≤ ((74373572291361541351/74395000000000000000 : ℝ)+2*(3880338045207/1487900000000000 : ℝ)*(5599/100000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (74373572291361541351/74395000000000000000 : ℝ)+2*(3880338045207/1487900000000000 : ℝ)*(5599/100000 : ℝ)=(312501253041521/312500000000000 : ℝ) by norm_num, show 1+2*(203742866452319/25000000000000000000 : ℝ)=(12500203742866452319/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79322099981750263/50000000000000000000 : ℝ)+(203742866452319/25000000000000000000 : ℝ) ≤ ((74373572291361541351/74395000000000000000 : ℝ)+(3880338045207/1487900000000000 : ℝ)*((10239/50000 : ℝ)+(5599/100000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (74373572291361541351/74395000000000000000 : ℝ)+(3880338045207/1487900000000000 : ℝ)*((10239/50000 : ℝ)+(5599/100000 : ℝ))=(10003920435373879/10000000000000000 : ℝ) by norm_num, show 1+(79322099981750263/50000000000000000000 : ℝ)+(203742866452319/25000000000000000000 : ℝ)=(50079729585714654901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79322099981750263/50000000000000000000 : ℝ) ≤ ((74373572291361541351/74395000000000000000 : ℝ)+2*(3880338045207/1487900000000000 : ℝ)*(10239/50000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (74373572291361541351/74395000000000000000 : ℝ)+2*(3880338045207/1487900000000000 : ℝ)*(10239/50000 : ℝ)=(5003900386709543/5000000000000000 : ℝ) by norm_num, show 1+2*(79322099981750263/50000000000000000000 : ℝ)=(25079322099981750263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74373572291361541351/74395000000000000000 : ℝ)*(X 1 0+X 2 0)+(3880338045207/1487900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5599/100000 : ℝ)) (hi := (10239/50000 : ℝ)) (c := (74373572291361541351/74395000000000000000 : ℝ)) (alpha := (3880338045207/1487900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74373572291361541351/74395000000000000000 : ℝ)*(X 0 1+X 2 1)+(3880338045207/1487900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5599/100000 : ℝ)) (hi := (10239/50000 : ℝ)) (c := (74373572291361541351/74395000000000000000 : ℝ)) (alpha := (3880338045207/1487900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74373572291361541351/74395000000000000000 : ℝ)*(X 0 2+X 1 2)+(3880338045207/1487900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5599/100000 : ℝ)) (hi := (10239/50000 : ℝ)) (c := (74373572291361541351/74395000000000000000 : ℝ)) (alpha := (3880338045207/1487900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430739127/2000000000 : ℝ)*X 0 0+(5512528533/10000000000 : ℝ)*X 0 1+(5157621731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687125703/5000000000 : ℝ)*X 1 0+(-1169138501/5000000000 : ℝ)*X 1 1+(2578811763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687125671/5000000000 : ℝ)*X 2 0+(5157623507/10000000000 : ℝ)*X 2 1+(-233827711/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355029441/10000000000 : ℝ)*X 0 0+(4016775727/10000000000 : ℝ)*X 0 1+(1180400763/2500000000 : ℝ)*X 0 2+(4355029441/10000000000 : ℝ)*X 1 0+(4016775727/10000000000 : ℝ)*X 1 1+(1180400763/2500000000 : ℝ)*X 1 2+(4355029441/10000000000 : ℝ)*X 2 0+(4016775727/10000000000 : ℝ)*X 2 1+(1180400763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-538450197/2500000000 : ℝ)*X 0 0+(5160084647/10000000000 : ℝ)*X 0 1+(22040163/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528425641/1000000000 : ℝ)*X 1 0+(-248232241/1250000000 : ℝ)*X 1 1+(5510041349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642127533/5000000000 : ℝ)*X 2 0+(688755149/1250000000 : ℝ)*X 2 1+(-496464999/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177618821/5000000000 : ℝ)*X 0 0+(943342657/2000000000 : ℝ)*X 0 1+(4021714669/10000000000 : ℝ)*X 0 2+(2177618821/5000000000 : ℝ)*X 1 0+(943342657/2000000000 : ℝ)*X 1 1+(4021714669/10000000000 : ℝ)*X 1 2+(2177618821/5000000000 : ℝ)*X 2 0+(943342657/2000000000 : ℝ)*X 2 1+(4021714669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6216188656392357492099/595160000000000000000000000 : ℝ) := by norm_num
    linear_combination (247445571/20000000000000 : ℝ)*(base19) + (454893673/50000000000000 : ℝ)*(base23) + (166705241/50000000000000 : ℝ)*(upper3) + (157941561/100000000000000 : ℝ)*(upper4) + (4176461/12500000000000 : ℝ)*(upper5) + (105912280543913/5000000000000 : ℝ)*(major0) + (105912280543913/5000000000000 : ℝ)*(major1) + (105912280543913/5000000000000 : ℝ)*(major2) + (352208317817479/12500000000000 : ℝ)*(sp0) + (44026362440789/1562500000000 : ℝ)*(sp1) + (1408843761825503/50000000000000 : ℝ)*(sp2) + (141879339715827/10000000000000 : ℝ)*(sp3) + (21890898519/100000000000000 : ℝ)*(sp4) + (9043007651/100000000000000 : ℝ)*(sp7) + (1418802440165921/100000000000000 : ℝ)*(f.failure) + (2817688433438351/100000000000000 : ℝ)*(f.sum) + (15864968906521/3719750000000000000000000000 : ℝ)*base65 + (2890245862955753537/371975000000000000000000000000000 : ℝ)*base68 + (660512745526578537/371975000000000000000000000000000 : ℝ)*base70 + (1388298628319096463/371975000000000000000000000000000 : ℝ)*base71 + (45458616812243/14879000000000000000000000000 : ℝ)*base74 + (1215435125346771463/371975000000000000000000000000000 : ℝ)*base75 + (2232949667336003537/371975000000000000000000000000000 : ℝ)*base78 + (1612945311893071463/371975000000000000000000000000000 : ℝ)*base79 + (8452417097257/14879000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (23810823/10000000000000000000000 : ℝ)*base90 + (23810823/10000000000000000000000 : ℝ)*base92 + (23810823/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7486417516607174816223/2324843750000000000000000000 : ℝ) := by norm_num
    linear_combination (363563619/100000000000000 : ℝ)*(base19) + (1200193/12500000000000 : ℝ)*(base23) + (30349321/10000000000000 : ℝ)*(upper2) + (58573951/50000000000000 : ℝ)*(upper3) + (2148176875515629/100000000000000 : ℝ)*(major0) + (2148176875515629/100000000000000 : ℝ)*(major1) + (2148176875515629/100000000000000 : ℝ)*(major2) + (2833935523/50000000000000 : ℝ)*(sp0) + (11832592767/100000000000000 : ℝ)*(sp1) + (23090651/10000000000000 : ℝ)*(sp3) + (2857497552981587/100000000000000 : ℝ)*(sp4) + (357186378087031/12500000000000 : ℝ)*(sp5) + (2857503211251089/100000000000000 : ℝ)*(sp6) + (179856273991593/12500000000000 : ℝ)*(sp7) + (719425211419627/50000000000000 : ℝ)*(f.failure) + (1428751610426317/50000000000000 : ℝ)*(f.sum) + (354964093205637/74395000000000000000000000000 : ℝ)*base66 + (12204338588418924779/7439500000000000000000000000000000 : ℝ)*base67 + (7666808878826424779/7439500000000000000000000000000000 : ℝ)*base69 + (21852974670939575221/7439500000000000000000000000000000 : ℝ)*base72 + (105633776460063/74395000000000000000000000000 : ℝ)*base73 + (4063974147034575221/7439500000000000000000000000000000 : ℝ)*base76 + (49930665335023575221/7439500000000000000000000000000000 : ℝ)*base78 + (14786531151669424779/7439500000000000000000000000000000 : ℝ)*base79 + (64190815680463/74395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (13665101/5000000000000000000000 : ℝ)*base90 + (13665101/5000000000000000000000 : ℝ)*base92 + (13665101/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10239/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1133_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1133_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1133_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1133_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1133_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
