-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:04.829992+00:00
-- url     : https://prove2.me/submissions/924fe06a-c9a1-485e-b55a-33e4265c22c2

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
theorem support_rectangle_w1347_s0_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903097043/5000000000 : ℝ)*x 0 + (1198952009/2000000000 : ℝ)*x 1 + (2406050291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903097043/5000000000 : ℝ)^4307 ≤ (5295560441057/50000000000000 : ℝ)^3283 := by
    have hnat : (903097043 : ℕ)^4307*50000000000000^3283 ≤ 5295560441057^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903097043 5000000000 5295560441057 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198952009/2000000000 : ℝ)^4307 ≤ (51104205796589/100000000000000 : ℝ)^3283 := by
    have hnat : (1198952009 : ℕ)^4307*100000000000000^3283 ≤ 51104205796589^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198952009 2000000000 51104205796589 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2406050291/5000000000 : ℝ)^4307 ≤ (9576168328447/25000000000000 : ℝ)^3283 := by
    have hnat : (2406050291 : ℕ)^4307*25000000000000^3283 ≤ 9576168328447^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406050291 5000000000 9576168328447 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903097043/5000000000 : ℝ), (1198952009/2000000000 : ℝ), (2406050291/5000000000 : ℝ)] ![(5295560441057/50000000000000 : ℝ), (51104205796589/100000000000000 : ℝ), (9576168328447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903097043/5000000000 : ℝ)|^4307 ≤ (5295560441057/50000000000000 : ℝ)^3283
        have hw : |(-903097043/5000000000 : ℝ)|=(903097043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198952009/2000000000 : ℝ)|^4307 ≤ (51104205796589/100000000000000 : ℝ)^3283
        have hw : |(1198952009/2000000000 : ℝ)|=(1198952009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2406050291/5000000000 : ℝ)|^4307 ≤ (9576168328447/25000000000000 : ℝ)^3283
        have hw : |(2406050291/5000000000 : ℝ)|=(2406050291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5501252723/10000000000 : ℝ)*x 0 + (-2478168401/10000000000 : ℝ)*x 1 + (1203025253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501252723/10000000000 : ℝ)^4307 ≤ (22828586377191/50000000000000 : ℝ)^3283 := by
    have hnat : (5501252723 : ℕ)^4307*50000000000000^3283 ≤ 22828586377191^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501252723 10000000000 22828586377191 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2478168401/10000000000 : ℝ)^4307 ≤ (16038149421879/100000000000000 : ℝ)^3283 := by
    have hnat : (2478168401 : ℕ)^4307*100000000000000^3283 ≤ 16038149421879^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478168401 10000000000 16038149421879 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203025253/2500000000 : ℝ)^4307 ≤ (7660935560847/20000000000000 : ℝ)^3283 := by
    have hnat : (1203025253 : ℕ)^4307*20000000000000^3283 ≤ 7660935560847^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203025253 2500000000 7660935560847 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501252723/10000000000 : ℝ), (-2478168401/10000000000 : ℝ), (1203025253/2500000000 : ℝ)] ![(22828586377191/50000000000000 : ℝ), (16038149421879/100000000000000 : ℝ), (7660935560847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501252723/10000000000 : ℝ)|^4307 ≤ (22828586377191/50000000000000 : ℝ)^3283
        have hw : |(5501252723/10000000000 : ℝ)|=(5501252723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2478168401/10000000000 : ℝ)|^4307 ≤ (16038149421879/100000000000000 : ℝ)^3283
        have hw : |(-2478168401/10000000000 : ℝ)|=(2478168401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203025253/2500000000 : ℝ)|^4307 ≤ (7660935560847/20000000000000 : ℝ)^3283
        have hw : |(1203025253/2500000000 : ℝ)|=(1203025253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1100250497/2000000000 : ℝ)*x 0 + (1203025181/2500000000 : ℝ)*x 1 + (-1239084531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100250497/2000000000 : ℝ)^4307 ≤ (45657170163019/100000000000000 : ℝ)^3283 := by
    have hnat : (1100250497 : ℕ)^4307*100000000000000^3283 ≤ 45657170163019^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100250497 2000000000 45657170163019 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203025181/2500000000 : ℝ)^4307 ≤ (957616869917/2500000000000 : ℝ)^3283 := by
    have hnat : (1203025181 : ℕ)^4307*2500000000000^3283 ≤ 957616869917^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203025181 2500000000 957616869917 2500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239084531/5000000000 : ℝ)^4307 ≤ (641526201361/4000000000000 : ℝ)^3283 := by
    have hnat : (1239084531 : ℕ)^4307*4000000000000^3283 ≤ 641526201361^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239084531 5000000000 641526201361 4000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100250497/2000000000 : ℝ), (1203025181/2500000000 : ℝ), (-1239084531/5000000000 : ℝ)] ![(45657170163019/100000000000000 : ℝ), (957616869917/2500000000000 : ℝ), (641526201361/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100250497/2000000000 : ℝ)|^4307 ≤ (45657170163019/100000000000000 : ℝ)^3283
        have hw : |(1100250497/2000000000 : ℝ)|=(1100250497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203025181/2500000000 : ℝ)|^4307 ≤ (957616869917/2500000000000 : ℝ)^3283
        have hw : |(1203025181/2500000000 : ℝ)|=(1203025181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1239084531/5000000000 : ℝ)|^4307 ≤ (641526201361/4000000000000 : ℝ)^3283
        have hw : |(-1239084531/5000000000 : ℝ)|=(1239084531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088999577/5000000000 : ℝ)*x 0 + (3106321117/10000000000 : ℝ)*x 1 + (5588146983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088999577/5000000000 : ℝ)^4307 ≤ (994476827293/3125000000000 : ℝ)^3283 := by
    have hnat : (2088999577 : ℕ)^4307*3125000000000^3283 ≤ 994476827293^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088999577 5000000000 994476827293 3125000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3106321117/10000000000 : ℝ)^4307 ≤ (21571134649791/100000000000000 : ℝ)^3283 := by
    have hnat : (3106321117 : ℕ)^4307*100000000000000^3283 ≤ 21571134649791^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106321117 10000000000 21571134649791 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5588146983/10000000000 : ℝ)^4307 ≤ (233028034331/500000000000 : ℝ)^3283 := by
    have hnat : (5588146983 : ℕ)^4307*500000000000^3283 ≤ 233028034331^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588146983 10000000000 233028034331 500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088999577/5000000000 : ℝ), (3106321117/10000000000 : ℝ), (5588146983/10000000000 : ℝ)] ![(994476827293/3125000000000 : ℝ), (21571134649791/100000000000000 : ℝ), (233028034331/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088999577/5000000000 : ℝ)|^4307 ≤ (994476827293/3125000000000 : ℝ)^3283
        have hw : |(2088999577/5000000000 : ℝ)|=(2088999577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3106321117/10000000000 : ℝ)|^4307 ≤ (21571134649791/100000000000000 : ℝ)^3283
        have hw : |(3106321117/10000000000 : ℝ)|=(3106321117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5588146983/10000000000 : ℝ)|^4307 ≤ (233028034331/500000000000 : ℝ)^3283
        have hw : |(5588146983/10000000000 : ℝ)|=(5588146983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1810624529/10000000000 : ℝ)*x 0 + (4842530381/10000000000 : ℝ)*x 1 + (5963243623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1810624529/10000000000 : ℝ)^4307 ≤ (1062521619367/10000000000000 : ℝ)^3283 := by
    have hnat : (1810624529 : ℕ)^4307*10000000000000^3283 ≤ 1062521619367^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810624529 10000000000 1062521619367 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4842530381/10000000000 : ℝ)^4307 ≤ (19311380775317/50000000000000 : ℝ)^3283 := by
    have hnat : (4842530381 : ℕ)^4307*50000000000000^3283 ≤ 19311380775317^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842530381 10000000000 19311380775317 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5963243623/10000000000 : ℝ)^4307 ≤ (50752022237673/100000000000000 : ℝ)^3283 := by
    have hnat : (5963243623 : ℕ)^4307*100000000000000^3283 ≤ 50752022237673^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963243623 10000000000 50752022237673 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1810624529/10000000000 : ℝ), (4842530381/10000000000 : ℝ), (5963243623/10000000000 : ℝ)] ![(1062521619367/10000000000000 : ℝ), (19311380775317/50000000000000 : ℝ), (50752022237673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1810624529/10000000000 : ℝ)|^4307 ≤ (1062521619367/10000000000000 : ℝ)^3283
        have hw : |(-1810624529/10000000000 : ℝ)|=(1810624529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4842530381/10000000000 : ℝ)|^4307 ≤ (19311380775317/50000000000000 : ℝ)^3283
        have hw : |(4842530381/10000000000 : ℝ)|=(4842530381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5963243623/10000000000 : ℝ)|^4307 ≤ (50752022237673/100000000000000 : ℝ)^3283
        have hw : |(5963243623/10000000000 : ℝ)|=(5963243623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589453909/5000000000 : ℝ)*x 0 + (-1327026863/10000000000 : ℝ)*x 1 + (1490810833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589453909/5000000000 : ℝ)^4307 ≤ (21089984585641/50000000000000 : ℝ)^3283 := by
    have hnat : (2589453909 : ℕ)^4307*50000000000000^3283 ≤ 21089984585641^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589453909 5000000000 21089984585641 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1327026863/10000000000 : ℝ)^4307 ≤ (7068011829277/100000000000000 : ℝ)^3283 := by
    have hnat : (1327026863 : ℕ)^4307*100000000000000^3283 ≤ 7068011829277^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327026863 10000000000 7068011829277 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1490810833/2500000000 : ℝ)^4307 ≤ (25376009494269/50000000000000 : ℝ)^3283 := by
    have hnat : (1490810833 : ℕ)^4307*50000000000000^3283 ≤ 25376009494269^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490810833 2500000000 25376009494269 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589453909/5000000000 : ℝ), (-1327026863/10000000000 : ℝ), (1490810833/2500000000 : ℝ)] ![(21089984585641/50000000000000 : ℝ), (7068011829277/100000000000000 : ℝ), (25376009494269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589453909/5000000000 : ℝ)|^4307 ≤ (21089984585641/50000000000000 : ℝ)^3283
        have hw : |(2589453909/5000000000 : ℝ)|=(2589453909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1327026863/10000000000 : ℝ)|^4307 ≤ (7068011829277/100000000000000 : ℝ)^3283
        have hw : |(-1327026863/10000000000 : ℝ)|=(1327026863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1490810833/2500000000 : ℝ)|^4307 ≤ (25376009494269/50000000000000 : ℝ)^3283
        have hw : |(1490810833/2500000000 : ℝ)|=(1490810833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (647363473/1250000000 : ℝ)*x 0 + (2981621823/5000000000 : ℝ)*x 1 + (-331756603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647363473/1250000000 : ℝ)^4307 ≤ (8435993761599/20000000000000 : ℝ)^3283 := by
    have hnat : (647363473 : ℕ)^4307*20000000000000^3283 ≤ 8435993761599^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647363473 1250000000 8435993761599 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981621823/5000000000 : ℝ)^4307 ≤ (50752022494477/100000000000000 : ℝ)^3283 := by
    have hnat : (2981621823 : ℕ)^4307*100000000000000^3283 ≤ 50752022494477^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981621823 5000000000 50752022494477 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (331756603/2500000000 : ℝ)^4307 ≤ (7068008677917/100000000000000 : ℝ)^3283 := by
    have hnat : (331756603 : ℕ)^4307*100000000000000^3283 ≤ 7068008677917^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331756603 2500000000 7068008677917 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647363473/1250000000 : ℝ), (2981621823/5000000000 : ℝ), (-331756603/2500000000 : ℝ)] ![(8435993761599/20000000000000 : ℝ), (50752022494477/100000000000000 : ℝ), (7068008677917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647363473/1250000000 : ℝ)|^4307 ≤ (8435993761599/20000000000000 : ℝ)^3283
        have hw : |(647363473/1250000000 : ℝ)|=(647363473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981621823/5000000000 : ℝ)|^4307 ≤ (50752022494477/100000000000000 : ℝ)^3283
        have hw : |(2981621823/5000000000 : ℝ)|=(2981621823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-331756603/2500000000 : ℝ)|^4307 ≤ (7068008677917/100000000000000 : ℝ)^3283
        have hw : |(-331756603/2500000000 : ℝ)|=(331756603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s0_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046823557/2500000000 : ℝ)*x 0 + (690536331/1250000000 : ℝ)*x 1 + (793114557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046823557/2500000000 : ℝ)^4307 ≤ (15958086510901/50000000000000 : ℝ)^3283 := by
    have hnat : (1046823557 : ℕ)^4307*50000000000000^3283 ≤ 15958086510901^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046823557 2500000000 15958086510901 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690536331/1250000000 : ℝ)^4307 ≤ (22954087625637/50000000000000 : ℝ)^3283 := by
    have hnat : (690536331 : ℕ)^4307*50000000000000^3283 ≤ 22954087625637^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690536331 1250000000 22954087625637 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793114557/2500000000 : ℝ)^4307 ≤ (1385978231809/6250000000000 : ℝ)^3283 := by
    have hnat : (793114557 : ℕ)^4307*6250000000000^3283 ≤ 1385978231809^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793114557 2500000000 1385978231809 6250000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046823557/2500000000 : ℝ), (690536331/1250000000 : ℝ), (793114557/2500000000 : ℝ)] ![(15958086510901/50000000000000 : ℝ), (22954087625637/50000000000000 : ℝ), (1385978231809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046823557/2500000000 : ℝ)|^4307 ≤ (15958086510901/50000000000000 : ℝ)^3283
        have hw : |(1046823557/2500000000 : ℝ)|=(1046823557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690536331/1250000000 : ℝ)|^4307 ≤ (22954087625637/50000000000000 : ℝ)^3283
        have hw : |(690536331/1250000000 : ℝ)|=(690536331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793114557/2500000000 : ℝ)|^4307 ≤ (1385978231809/6250000000000 : ℝ)^3283
        have hw : |(793114557/2500000000 : ℝ)|=(793114557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (363/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5367/20000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2153/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2153 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2153*1^512 ≤ 0^512*1^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2153/512 : ℝ) ≤ (2121442057499884061/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2153 ≤ (2121442057499884061/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2153*100000000000000000000^512 ≤ 2121442057499884061^512*5^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2121442057499884061 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2121442057499884061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2153 := by
      have hnat : (1 : ℕ)^512*1^2153 ≤ 1^2153*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102121442057499884061/100000000000000000000 : ℝ) ≤ (10050046666100451/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (102121442057499884061/100000000000000000000 : ℝ)^512 ≤ (10050046666100451/10000000000000000 : ℝ)^2153 := by
      have hnat : (102121442057499884061 : ℕ)^512*10000000000000000^2153 ≤ 10050046666100451^2153*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102121442057499884061 100000000000000000000 10050046666100451 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050046666100451/10000000000000000 : ℝ)) (X := (102121442057499884061/100000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52121442057499884061/50000000000000000000 : ℝ) ≤ (5050046666100451/5000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (52121442057499884061/50000000000000000000 : ℝ)^512 ≤ (5050046666100451/5000000000000000 : ℝ)^2153 := by
      have hnat : (52121442057499884061 : ℕ)^512*5000000000000000^2153 ≤ 5050046666100451^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52121442057499884061 50000000000000000000 5050046666100451 5000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050046666100451/5000000000000000 : ℝ)) (X := (52121442057499884061/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(50046666100451/4000000000000000 : ℝ)*(0 : ℝ))^(2153/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(50046666100451/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2121442057499884061/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(50046666100451/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (1 : ℝ)+(50046666100451/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10050046666100451/10000000000000000 : ℝ) by norm_num, show 1+(2121442057499884061/100000000000000000000 : ℝ)+(0 : ℝ)=(102121442057499884061/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2121442057499884061/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(50046666100451/4000000000000000 : ℝ)*(2/5 : ℝ))^(2153/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(50046666100451/4000000000000000 : ℝ)*(2/5 : ℝ)=(5050046666100451/5000000000000000 : ℝ) by norm_num, show 1+2*(2121442057499884061/100000000000000000000 : ℝ)=(52121442057499884061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(50046666100451/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50046666100451/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(50046666100451/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50046666100451/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(50046666100451/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50046666100451/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-903097043/5000000000 : ℝ)*X 0 0+(1198952009/2000000000 : ℝ)*X 0 1+(2406050291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5501252723/10000000000 : ℝ)*X 1 0+(-2478168401/10000000000 : ℝ)*X 1 1+(1203025253/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1100250497/2000000000 : ℝ)*X 2 0+(1203025181/2500000000 : ℝ)*X 2 1+(-1239084531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088999577/5000000000 : ℝ)*X 0 0+(3106321117/10000000000 : ℝ)*X 0 1+(5588146983/10000000000 : ℝ)*X 0 2+(2088999577/5000000000 : ℝ)*X 1 0+(3106321117/10000000000 : ℝ)*X 1 1+(5588146983/10000000000 : ℝ)*X 1 2+(2088999577/5000000000 : ℝ)*X 2 0+(3106321117/10000000000 : ℝ)*X 2 1+(5588146983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1810624529/10000000000 : ℝ)*X 0 0+(4842530381/10000000000 : ℝ)*X 0 1+(5963243623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589453909/5000000000 : ℝ)*X 1 0+(-1327026863/10000000000 : ℝ)*X 1 1+(1490810833/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647363473/1250000000 : ℝ)*X 2 0+(2981621823/5000000000 : ℝ)*X 2 1+(-331756603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1046823557/2500000000 : ℝ)*X 0 0+(690536331/1250000000 : ℝ)*X 0 1+(793114557/2500000000 : ℝ)*X 0 2+(1046823557/2500000000 : ℝ)*X 1 0+(690536331/1250000000 : ℝ)*X 1 1+(793114557/2500000000 : ℝ)*X 1 2+(1046823557/2500000000 : ℝ)*X 2 0+(690536331/1250000000 : ℝ)*X 2 1+(793114557/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2722707889582061307/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8968049/10000000000000 : ℝ)*(base1) + (2066489/10000000000000 : ℝ)*(base16) + (15593227/2500000000000 : ℝ)*(base19) + (607812819/100000000000000 : ℝ)*(base23) + (111594623/100000000000000 : ℝ)*(upper3) + (1560608667479/250000000000 : ℝ)*(major0) + (1560608667479/250000000000 : ℝ)*(major1) + (1560608667479/250000000000 : ℝ)*(major2) + (169110859289857/20000000000000 : ℝ)*(sp0) + (845555258509119/100000000000000 : ℝ)*(sp1) + (84555529509027/10000000000000 : ℝ)*(sp2) + (402929840980243/100000000000000 : ℝ)*(sp3) + (848067147/50000000000000 : ℝ)*(sp4) + (1009662443/100000000000000 : ℝ)*(sp7) + (50366367540397/12500000000000 : ℝ)*(f.failure) + (845555902903089/100000000000000 : ℝ)*(f.sum) + (237012761971/500000000000000000000000000 : ℝ)*base66 + (2926042599029/1000000000000000000000000000 : ℝ)*base67 + (4466192028029/1000000000000000000000000000 : ℝ)*base69 + (1870196470029/1000000000000000000000000000 : ℝ)*base71 + (2341866954971/500000000000000000000000000 : ℝ)*base74 + (1355845367971/1000000000000000000000000000 : ℝ)*base76 + (5552456557029/1000000000000000000000000000 : ℝ)*base77 + (948509041971/1000000000000000000000000000 : ℝ)*base80 + (341390366529/500000000000000000000000000 : ℝ)*base81 + (953527/156250000000000000000 : ℝ)*base90 + (953527/156250000000000000000 : ℝ)*base92 + (953527/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1085240348889294321/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (735940819/100000000000000 : ℝ)*(base19) + (893268813/100000000000000 : ℝ)*(base23) + (402841/250000000000 : ℝ)*(base39) + (1529401/2000000000000 : ℝ)*(upper3) + (36709173/25000000000000 : ℝ)*(upper5) + (329372116563769/50000000000000 : ℝ)*(major0) + (329372116563769/50000000000000 : ℝ)*(major1) + (658744071991137/100000000000000 : ℝ)*(major2) + (1690892317/100000000000000 : ℝ)*(sp1) + (893183217/50000000000000 : ℝ)*(sp2) + (223071995602433/25000000000000 : ℝ)*(sp4) + (223071388894149/25000000000000 : ℝ)*(sp5) + (178457092782177/20000000000000 : ℝ)*(sp6) + (17008007120409/4000000000000 : ℝ)*(sp7) + (17008007120409/4000000000000 : ℝ)*(f.failure) + (223072035886533/25000000000000 : ℝ)*(f.sum) + (35353559888897/16000000000000000000000000000 : ℝ)*base65 + (917202653097213/400000000000000000000000000000 : ℝ)*base68 + (1324978966040181/200000000000000000000000000000 : ℝ)*base70 + (934879616102787/400000000000000000000000000000 : ℝ)*base71 + (12754236319103/16000000000000000000000000000 : ℝ)*base74 + (1486747694040181/200000000000000000000000000000 : ℝ)*base76 + (725445375159819/200000000000000000000000000000 : ℝ)*base77 + (3287044040181/200000000000000000000000000000 : ℝ)*base80 + (210722923959819/100000000000000000000000000000 : ℝ)*base81 + (345019/50000000000000000000 : ℝ)*base90 + (345019/50000000000000000000 : ℝ)*base92 + (154981/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1347_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5367/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1347_s1_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-995144619/5000000000 : ℝ)*x 0 + (2819946041/5000000000 : ℝ)*x 1 + (5049067253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995144619/5000000000 : ℝ)^4307 ≤ (12029324989473/100000000000000 : ℝ)^3283 := by
    have hnat : (995144619 : ℕ)^4307*100000000000000^3283 ≤ 12029324989473^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995144619 5000000000 12029324989473 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2819946041/5000000000 : ℝ)^4307 ≤ (23586294223157/50000000000000 : ℝ)^3283 := by
    have hnat : (2819946041 : ℕ)^4307*50000000000000^3283 ≤ 23586294223157^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819946041 5000000000 23586294223157 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5049067253/10000000000 : ℝ)^4307 ≤ (40798086546399/100000000000000 : ℝ)^3283 := by
    have hnat : (5049067253 : ℕ)^4307*100000000000000^3283 ≤ 40798086546399^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049067253 10000000000 40798086546399 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-995144619/5000000000 : ℝ), (2819946041/5000000000 : ℝ), (5049067253/10000000000 : ℝ)] ![(12029324989473/100000000000000 : ℝ), (23586294223157/50000000000000 : ℝ), (40798086546399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-995144619/5000000000 : ℝ)|^4307 ≤ (12029324989473/100000000000000 : ℝ)^3283
        have hw : |(-995144619/5000000000 : ℝ)|=(995144619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2819946041/5000000000 : ℝ)|^4307 ≤ (23586294223157/50000000000000 : ℝ)^3283
        have hw : |(2819946041/5000000000 : ℝ)|=(2819946041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5049067253/10000000000 : ℝ)|^4307 ≤ (40798086546399/100000000000000 : ℝ)^3283
        have hw : |(5049067253/10000000000 : ℝ)|=(5049067253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (27025977/50000000 : ℝ)*x 0 + (-1152716129/5000000000 : ℝ)*x 1 + (5049067527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27025977/50000000 : ℝ)^4307 ≤ (44614152241499/100000000000000 : ℝ)^3283 := by
    have hnat : (27025977 : ℕ)^4307*100000000000000^3283 ≤ 44614152241499^3283*50000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27025977 50000000 44614152241499 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152716129/5000000000 : ℝ)^4307 ≤ (7293879146693/50000000000000 : ℝ)^3283 := by
    have hnat : (1152716129 : ℕ)^4307*50000000000000^3283 ≤ 7293879146693^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152716129 5000000000 7293879146693 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5049067527/10000000000 : ℝ)^4307 ≤ (20399044725489/50000000000000 : ℝ)^3283 := by
    have hnat : (5049067527 : ℕ)^4307*50000000000000^3283 ≤ 20399044725489^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049067527 10000000000 20399044725489 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27025977/50000000 : ℝ), (-1152716129/5000000000 : ℝ), (5049067527/10000000000 : ℝ)] ![(44614152241499/100000000000000 : ℝ), (7293879146693/50000000000000 : ℝ), (20399044725489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27025977/50000000 : ℝ)|^4307 ≤ (44614152241499/100000000000000 : ℝ)^3283
        have hw : |(27025977/50000000 : ℝ)|=(27025977/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1152716129/5000000000 : ℝ)|^4307 ≤ (7293879146693/50000000000000 : ℝ)^3283
        have hw : |(-1152716129/5000000000 : ℝ)|=(1152716129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5049067527/10000000000 : ℝ)|^4307 ≤ (20399044725489/50000000000000 : ℝ)^3283
        have hw : |(5049067527/10000000000 : ℝ)|=(5049067527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405195371/10000000000 : ℝ)*x 0 + (2524533609/5000000000 : ℝ)*x 1 + (-2305432691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405195371/10000000000 : ℝ)^4307 ≤ (1784566077099/4000000000000 : ℝ)^3283 := by
    have hnat : (5405195371 : ℕ)^4307*4000000000000^3283 ≤ 1784566077099^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405195371 10000000000 1784566077099 4000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2524533609/5000000000 : ℝ)^4307 ≤ (40798086175377/100000000000000 : ℝ)^3283 := by
    have hnat : (2524533609 : ℕ)^4307*100000000000000^3283 ≤ 40798086175377^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524533609 5000000000 40798086175377 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2305432691/10000000000 : ℝ)^4307 ≤ (72938809439/500000000000 : ℝ)^3283 := by
    have hnat : (2305432691 : ℕ)^4307*500000000000^3283 ≤ 72938809439^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305432691 10000000000 72938809439 500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405195371/10000000000 : ℝ), (2524533609/5000000000 : ℝ), (-2305432691/10000000000 : ℝ)] ![(1784566077099/4000000000000 : ℝ), (40798086175377/100000000000000 : ℝ), (72938809439/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405195371/10000000000 : ℝ)|^4307 ≤ (1784566077099/4000000000000 : ℝ)^3283
        have hw : |(5405195371/10000000000 : ℝ)|=(5405195371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2524533609/5000000000 : ℝ)|^4307 ≤ (40798086175377/100000000000000 : ℝ)^3283
        have hw : |(2524533609/5000000000 : ℝ)|=(2524533609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2305432691/10000000000 : ℝ)|^4307 ≤ (72938809439/500000000000 : ℝ)^3283
        have hw : |(-2305432691/10000000000 : ℝ)|=(2305432691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291417717/10000000000 : ℝ)*x 0 + (1856448711/5000000000 : ℝ)*x 1 + (495274957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291417717/10000000000 : ℝ)^4307 ≤ (8240344533713/25000000000000 : ℝ)^3283 := by
    have hnat : (4291417717 : ℕ)^4307*25000000000000^3283 ≤ 8240344533713^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291417717 10000000000 8240344533713 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1856448711/5000000000 : ℝ)^4307 ≤ (27258514651003/100000000000000 : ℝ)^3283 := by
    have hnat : (1856448711 : ℕ)^4307*100000000000000^3283 ≤ 27258514651003^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856448711 5000000000 27258514651003 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495274957/1000000000 : ℝ)^4307 ≤ (621564175017/1562500000000 : ℝ)^3283 := by
    have hnat : (495274957 : ℕ)^4307*1562500000000^3283 ≤ 621564175017^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495274957 1000000000 621564175017 1562500000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291417717/10000000000 : ℝ), (1856448711/5000000000 : ℝ), (495274957/1000000000 : ℝ)] ![(8240344533713/25000000000000 : ℝ), (27258514651003/100000000000000 : ℝ), (621564175017/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291417717/10000000000 : ℝ)|^4307 ≤ (8240344533713/25000000000000 : ℝ)^3283
        have hw : |(4291417717/10000000000 : ℝ)|=(4291417717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1856448711/5000000000 : ℝ)|^4307 ≤ (27258514651003/100000000000000 : ℝ)^3283
        have hw : |(1856448711/5000000000 : ℝ)|=(1856448711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(495274957/1000000000 : ℝ)|^4307 ≤ (621564175017/1562500000000 : ℝ)^3283
        have hw : |(495274957/1000000000 : ℝ)|=(495274957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24885209/125000000 : ℝ)*x 0 + (1011290449/2000000000 : ℝ)*x 1 + (5632373273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24885209/125000000 : ℝ)^4307 ≤ (1203350766953/10000000000000 : ℝ)^3283 := by
    have hnat : (24885209 : ℕ)^4307*10000000000000^3283 ≤ 1203350766953^3283*125000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24885209 125000000 1203350766953 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011290449/2000000000 : ℝ)^4307 ≤ (40876390137283/100000000000000 : ℝ)^3283 := by
    have hnat : (1011290449 : ℕ)^4307*100000000000000^3283 ≤ 40876390137283^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011290449 2000000000 40876390137283 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5632373273/10000000000 : ℝ)^4307 ≤ (23545051092133/50000000000000 : ℝ)^3283 := by
    have hnat : (5632373273 : ℕ)^4307*50000000000000^3283 ≤ 23545051092133^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632373273 10000000000 23545051092133 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24885209/125000000 : ℝ), (1011290449/2000000000 : ℝ), (5632373273/10000000000 : ℝ)] ![(1203350766953/10000000000000 : ℝ), (40876390137283/100000000000000 : ℝ), (23545051092133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24885209/125000000 : ℝ)|^4307 ≤ (1203350766953/10000000000000 : ℝ)^3283
        have hw : |(-24885209/125000000 : ℝ)|=(24885209/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011290449/2000000000 : ℝ)|^4307 ≤ (40876390137283/100000000000000 : ℝ)^3283
        have hw : |(1011290449/2000000000 : ℝ)|=(1011290449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5632373273/10000000000 : ℝ)|^4307 ≤ (23545051092133/50000000000000 : ℝ)^3283
        have hw : |(5632373273/10000000000 : ℝ)|=(5632373273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050364139/2000000000 : ℝ)*x 0 + (-172212621/1000000000 : ℝ)*x 1 + (5632373317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050364139/2000000000 : ℝ)^4307 ≤ (42960743929619/100000000000000 : ℝ)^3283 := by
    have hnat : (1050364139 : ℕ)^4307*100000000000000^3283 ≤ 42960743929619^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050364139 2000000000 42960743929619 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172212621/1000000000 : ℝ)^4307 ≤ (4974576696373/50000000000000 : ℝ)^3283 := by
    have hnat : (172212621 : ℕ)^4307*50000000000000^3283 ≤ 4974576696373^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172212621 1000000000 4974576696373 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5632373317/10000000000 : ℝ)^4307 ≤ (23545051333437/50000000000000 : ℝ)^3283 := by
    have hnat : (5632373317 : ℕ)^4307*50000000000000^3283 ≤ 23545051333437^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632373317 10000000000 23545051333437 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050364139/2000000000 : ℝ), (-172212621/1000000000 : ℝ), (5632373317/10000000000 : ℝ)] ![(42960743929619/100000000000000 : ℝ), (4974576696373/50000000000000 : ℝ), (23545051333437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050364139/2000000000 : ℝ)|^4307 ≤ (42960743929619/100000000000000 : ℝ)^3283
        have hw : |(1050364139/2000000000 : ℝ)|=(1050364139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172212621/1000000000 : ℝ)|^4307 ≤ (4974576696373/50000000000000 : ℝ)^3283
        have hw : |(-172212621/1000000000 : ℝ)|=(172212621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5632373317/10000000000 : ℝ)|^4307 ≤ (23545051333437/50000000000000 : ℝ)^3283
        have hw : |(5632373317/10000000000 : ℝ)|=(5632373317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625910297/5000000000 : ℝ)*x 0 + (2816186693/5000000000 : ℝ)*x 1 + (-861063127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625910297/5000000000 : ℝ)^4307 ≤ (10740185711431/25000000000000 : ℝ)^3283 := by
    have hnat : (2625910297 : ℕ)^4307*25000000000000^3283 ≤ 10740185711431^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625910297 5000000000 10740185711431 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816186693/5000000000 : ℝ)^4307 ≤ (11772525855923/25000000000000 : ℝ)^3283 := by
    have hnat : (2816186693 : ℕ)^4307*25000000000000^3283 ≤ 11772525855923^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816186693 5000000000 11772525855923 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861063127/5000000000 : ℝ)^4307 ≤ (1243644215779/12500000000000 : ℝ)^3283 := by
    have hnat : (861063127 : ℕ)^4307*12500000000000^3283 ≤ 1243644215779^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861063127 5000000000 1243644215779 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625910297/5000000000 : ℝ), (2816186693/5000000000 : ℝ), (-861063127/5000000000 : ℝ)] ![(10740185711431/25000000000000 : ℝ), (11772525855923/25000000000000 : ℝ), (1243644215779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625910297/5000000000 : ℝ)|^4307 ≤ (10740185711431/25000000000000 : ℝ)^3283
        have hw : |(2625910297/5000000000 : ℝ)|=(2625910297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816186693/5000000000 : ℝ)|^4307 ≤ (11772525855923/25000000000000 : ℝ)^3283
        have hw : |(2816186693/5000000000 : ℝ)|=(2816186693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-861063127/5000000000 : ℝ)|^4307 ≤ (1243644215779/12500000000000 : ℝ)^3283
        have hw : |(-861063127/5000000000 : ℝ)|=(861063127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s1_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073131233/2500000000 : ℝ)*x 0 + (493725261/1000000000 : ℝ)*x 1 + (3728674463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073131233/2500000000 : ℝ)^4307 ≤ (3297253540619/10000000000000 : ℝ)^3283 := by
    have hnat : (1073131233 : ℕ)^4307*10000000000000^3283 ≤ 3297253540619^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073131233 2500000000 3297253540619 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493725261/1000000000 : ℝ)^4307 ≤ (39616892996993/100000000000000 : ℝ)^3283 := by
    have hnat : (493725261 : ℕ)^4307*100000000000000^3283 ≤ 39616892996993^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493725261 1000000000 39616892996993 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3728674463/10000000000 : ℝ)^4307 ≤ (6852642894337/25000000000000 : ℝ)^3283 := by
    have hnat : (3728674463 : ℕ)^4307*25000000000000^3283 ≤ 6852642894337^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728674463 10000000000 6852642894337 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073131233/2500000000 : ℝ), (493725261/1000000000 : ℝ), (3728674463/10000000000 : ℝ)] ![(3297253540619/10000000000000 : ℝ), (39616892996993/100000000000000 : ℝ), (6852642894337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073131233/2500000000 : ℝ)|^4307 ≤ (3297253540619/10000000000000 : ℝ)^3283
        have hw : |(1073131233/2500000000 : ℝ)|=(1073131233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493725261/1000000000 : ℝ)|^4307 ≤ (39616892996993/100000000000000 : ℝ)^3283
        have hw : |(493725261/1000000000 : ℝ)|=(493725261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3728674463/10000000000 : ℝ)|^4307 ≤ (6852642894337/25000000000000 : ℝ)^3283
        have hw : |(3728674463/10000000000 : ℝ)|=(3728674463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5367/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (867/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (607/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5367/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (363/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5367/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (363/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5367/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (363/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5367/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (363/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5367/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (363/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5367/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (363/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (363/25000 : ℝ) ^ (2153/512 : ℝ) ≤ (466515453109/25000000000000000000 : ℝ) := by
    have hpowers : (363/25000 : ℝ)^2153 ≤ (466515453109/25000000000000000000 : ℝ)^512 := by
      have hnat : (363 : ℕ)^2153*25000000000000000000^512 ≤ 466515453109^512*25000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        363 25000 466515453109 25000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (363/25000 : ℝ)) (X := (466515453109/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (5367/20000 : ℝ) ^ (2153/512 : ℝ) ≤ (197977391620150889/50000000000000000000 : ℝ) := by
    have hpowers : (5367/20000 : ℝ)^2153 ≤ (197977391620150889/50000000000000000000 : ℝ)^512 := by
      have hnat : (5367 : ℕ)^2153*50000000000000000000^512 ≤ 197977391620150889^512*20000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5367 20000 197977391620150889 50000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5367/20000 : ℝ)) (X := (197977391620150889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000466515453109/12500000000000000000 : ℝ) ≤ (10000000088752777/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (12500000466515453109/12500000000000000000 : ℝ)^512 ≤ (10000000088752777/10000000000000000 : ℝ)^2153 := by
      have hnat : (12500000466515453109 : ℕ)^512*10000000000000000^2153 ≤ 10000000088752777^2153*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000466515453109 12500000000000000000 10000000088752777 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000088752777/10000000000000000 : ℝ)) (X := (12500000466515453109/12500000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50197978324651057107/50000000000000000000 : ℝ) ≤ (25023504946551/25000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50197978324651057107/50000000000000000000 : ℝ)^512 ≤ (25023504946551/25000000000000 : ℝ)^2153 := by
      have hnat : (50197978324651057107 : ℕ)^512*25000000000000^2153 ≤ 25023504946551^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50197978324651057107 50000000000000000000 25023504946551 25000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25023504946551/25000000000000 : ℝ)) (X := (50197978324651057107/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25197977391620150889/25000000000000000000 : ℝ) ≤ (10018803868488023/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (25197977391620150889/25000000000000000000 : ℝ)^512 ≤ (10018803868488023/10000000000000000 : ℝ)^2153 := by
      have hnat : (25197977391620150889 : ℕ)^512*10000000000000000^2153 ≤ 10018803868488023^2153*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25197977391620150889 25000000000000000000 10018803868488023 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018803868488023/10000000000000000 : ℝ)) (X := (25197977391620150889/25000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(466515453109/25000000000000000000 : ℝ) ≤ ((84600899721545387133/84610000000000000000 : ℝ)+2*(9401889867623/2538300000000000 : ℝ)*(363/25000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (84600899721545387133/84610000000000000000 : ℝ)+2*(9401889867623/2538300000000000 : ℝ)*(363/25000 : ℝ)=(10000000088752777/10000000000000000 : ℝ) by norm_num, show 1+2*(466515453109/25000000000000000000 : ℝ)=(12500000466515453109/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(197977391620150889/50000000000000000000 : ℝ)+(466515453109/25000000000000000000 : ℝ) ≤ ((84600899721545387133/84610000000000000000 : ℝ)+(9401889867623/2538300000000000 : ℝ)*((5367/20000 : ℝ)+(363/25000 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (84600899721545387133/84610000000000000000 : ℝ)+(9401889867623/2538300000000000 : ℝ)*((5367/20000 : ℝ)+(363/25000 : ℝ))=(25023504946551/25000000000000 : ℝ) by norm_num, show 1+(197977391620150889/50000000000000000000 : ℝ)+(466515453109/25000000000000000000 : ℝ)=(50197978324651057107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(197977391620150889/50000000000000000000 : ℝ) ≤ ((84600899721545387133/84610000000000000000 : ℝ)+2*(9401889867623/2538300000000000 : ℝ)*(5367/20000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (84600899721545387133/84610000000000000000 : ℝ)+2*(9401889867623/2538300000000000 : ℝ)*(5367/20000 : ℝ)=(10018803868488023/10000000000000000 : ℝ) by norm_num, show 1+2*(197977391620150889/50000000000000000000 : ℝ)=(25197977391620150889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84600899721545387133/84610000000000000000 : ℝ)*(X 1 0+X 2 0)+(9401889867623/2538300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (363/25000 : ℝ)) (hi := (5367/20000 : ℝ)) (c := (84600899721545387133/84610000000000000000 : ℝ)) (alpha := (9401889867623/2538300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84600899721545387133/84610000000000000000 : ℝ)*(X 0 1+X 2 1)+(9401889867623/2538300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (363/25000 : ℝ)) (hi := (5367/20000 : ℝ)) (c := (84600899721545387133/84610000000000000000 : ℝ)) (alpha := (9401889867623/2538300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84600899721545387133/84610000000000000000 : ℝ)*(X 0 2+X 1 2)+(9401889867623/2538300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (363/25000 : ℝ)) (hi := (5367/20000 : ℝ)) (c := (84600899721545387133/84610000000000000000 : ℝ)) (alpha := (9401889867623/2538300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-995144619/5000000000 : ℝ)*X 0 0+(2819946041/5000000000 : ℝ)*X 0 1+(5049067253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((27025977/50000000 : ℝ)*X 1 0+(-1152716129/5000000000 : ℝ)*X 1 1+(5049067527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5405195371/10000000000 : ℝ)*X 2 0+(2524533609/5000000000 : ℝ)*X 2 1+(-2305432691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291417717/10000000000 : ℝ)*X 0 0+(1856448711/5000000000 : ℝ)*X 0 1+(495274957/1000000000 : ℝ)*X 0 2+(4291417717/10000000000 : ℝ)*X 1 0+(1856448711/5000000000 : ℝ)*X 1 1+(495274957/1000000000 : ℝ)*X 1 2+(4291417717/10000000000 : ℝ)*X 2 0+(1856448711/5000000000 : ℝ)*X 2 1+(495274957/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-24885209/125000000 : ℝ)*X 0 0+(1011290449/2000000000 : ℝ)*X 0 1+(5632373273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050364139/2000000000 : ℝ)*X 1 0+(-172212621/1000000000 : ℝ)*X 1 1+(5632373317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625910297/5000000000 : ℝ)*X 2 0+(2816186693/5000000000 : ℝ)*X 2 1+(-861063127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073131233/2500000000 : ℝ)*X 0 0+(493725261/1000000000 : ℝ)*X 0 1+(3728674463/10000000000 : ℝ)*X 0 2+(1073131233/2500000000 : ℝ)*X 1 0+(493725261/1000000000 : ℝ)*X 1 1+(3728674463/10000000000 : ℝ)*X 1 2+(1073131233/2500000000 : ℝ)*X 2 0+(493725261/1000000000 : ℝ)*X 2 1+(3728674463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18768392728522228592514456461/2115250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60168581/100000000000000 : ℝ)*(base1) + (1459560429/100000000000000 : ℝ)*(base19) + (72523973/5000000000000 : ℝ)*(base23) + (127605467/50000000000000 : ℝ)*(upper3) + (931921/1250000000000 : ℝ)*(upper5) + (624780832721861/50000000000000 : ℝ)*(major0) + (624780832721861/50000000000000 : ℝ)*(major1) + (624780832721861/50000000000000 : ℝ)*(major2) + (1692559219532451/100000000000000 : ℝ)*(sp0) + (1692565987124143/100000000000000 : ℝ)*(sp1) + (1692565996205113/100000000000000 : ℝ)*(sp2) + (403275587850579/50000000000000 : ℝ)*(sp3) + (4143660351/50000000000000 : ℝ)*(sp4) + (272035621/6250000000000 : ℝ)*(sp7) + (201638897109919/25000000000000 : ℝ)*(f.failure) + (423141861671143/25000000000000 : ℝ)*(f.sum) + (76065109317047/63457500000000000000000000000 : ℝ)*base66 + (55948118128279943539/12691500000000000000000000000000000 : ℝ)*base67 + (10739794905816443539/12691500000000000000000000000000000 : ℝ)*base69 + (28663598530234943539/12691500000000000000000000000000000 : ℝ)*base71 + (26923744422031/31728750000000000000000000000 : ℝ)*base74 + (42472611110118443539/12691500000000000000000000000000000 : ℝ)*base75 + (14253847439219556461/12691500000000000000000000000000000 : ℝ)*base78 + (66556035597493056461/12691500000000000000000000000000000 : ℝ)*base80 + (194613299627869/126915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1117571/312500000000000000000 : ℝ)*base89 + (1117571/312500000000000000000 : ℝ)*base91 + (1117571/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191053113470986908047085607/26440625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39812907/50000000000000 : ℝ)*(base1) + (1478429063/100000000000000 : ℝ)*(base19) + (144207867/10000000000000 : ℝ)*(base23) + (2083443/1250000000000 : ℝ)*(upper3) + (79251281/50000000000000 : ℝ)*(upper5) + (8011774392391/625000000000 : ℝ)*(major0) + (8011774392391/625000000000 : ℝ)*(major1) + (8011774392391/625000000000 : ℝ)*(major2) + (3787369289/50000000000000 : ℝ)*(sp1) + (1868362363/25000000000000 : ℝ)*(sp2) + (43408724874189/2500000000000 : ℝ)*(sp4) + (217042482771763/12500000000000 : ℝ)*(sp5) + (217042499976703/12500000000000 : ℝ)*(sp6) + (165483713947903/20000000000000 : ℝ)*(sp7) + (827418649365329/100000000000000 : ℝ)*(f.failure) + (868174457670873/50000000000000 : ℝ)*(f.sum) + (3038086389941/6345750000000000000000000000 : ℝ)*base66 + (577422503417502509/158643750000000000000000000000000 : ℝ)*base67 + (816020587360153741/158643750000000000000000000000000 : ℝ)*base70 + (1006798934310440009/158643750000000000000000000000000 : ℝ)*base71 + (30012305381369/12691500000000000000000000000 : ℝ)*base73 + (100001799759833759/158643750000000000000000000000000 : ℝ)*base75 + (221601867826415009/158643750000000000000000000000000 : ℝ)*base77 + (293941478882502509/158643750000000000000000000000000 : ℝ)*base79 + (9491516301067/5076600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3896739/1250000000000000000000 : ℝ)*base90 + (3896739/1250000000000000000000 : ℝ)*base92 + (3896739/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1347_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5367/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (867/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (607/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1347_s2_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-507502403/2500000000 : ℝ)*x 0 + (1095677767/2000000000 : ℝ)*x 1 + (518511999/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507502403/2500000000 : ℝ)^4307 ≤ (38578910473/312500000000 : ℝ)^3283 := by
    have hnat : (507502403 : ℕ)^4307*312500000000^3283 ≤ 38578910473^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507502403 2500000000 38578910473 312500000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095677767/2000000000 : ℝ)^4307 ≤ (22704195182237/50000000000000 : ℝ)^3283 := by
    have hnat : (1095677767 : ℕ)^4307*50000000000000^3283 ≤ 22704195182237^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095677767 2000000000 22704195182237 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518511999/1000000000 : ℝ)^4307 ≤ (8449271653349/20000000000000 : ℝ)^3283 := by
    have hnat : (518511999 : ℕ)^4307*20000000000000^3283 ≤ 8449271653349^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518511999 1000000000 8449271653349 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507502403/2500000000 : ℝ), (1095677767/2000000000 : ℝ), (518511999/1000000000 : ℝ)] ![(38578910473/312500000000 : ℝ), (22704195182237/50000000000000 : ℝ), (8449271653349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507502403/2500000000 : ℝ)|^4307 ≤ (38578910473/312500000000 : ℝ)^3283
        have hw : |(-507502403/2500000000 : ℝ)|=(507502403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095677767/2000000000 : ℝ)|^4307 ≤ (22704195182237/50000000000000 : ℝ)^3283
        have hw : |(1095677767/2000000000 : ℝ)|=(1095677767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518511999/1000000000 : ℝ)|^4307 ≤ (8449271653349/20000000000000 : ℝ)^3283
        have hw : |(518511999/1000000000 : ℝ)|=(518511999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365602281/10000000000 : ℝ)*x 0 + (-545375567/2500000000 : ℝ)*x 1 + (5185120383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365602281/10000000000 : ℝ)^4307 ≤ (22092955887073/50000000000000 : ℝ)^3283 := by
    have hnat : (5365602281 : ℕ)^4307*50000000000000^3283 ≤ 22092955887073^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365602281 10000000000 22092955887073 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545375567/2500000000 : ℝ)^4307 ≤ (6783862872273/50000000000000 : ℝ)^3283 := by
    have hnat : (545375567 : ℕ)^4307*50000000000000^3283 ≤ 6783862872273^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545375567 2500000000 6783862872273 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185120383/10000000000 : ℝ)^4307 ≤ (42246362467497/100000000000000 : ℝ)^3283 := by
    have hnat : (5185120383 : ℕ)^4307*100000000000000^3283 ≤ 42246362467497^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185120383 10000000000 42246362467497 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365602281/10000000000 : ℝ), (-545375567/2500000000 : ℝ), (5185120383/10000000000 : ℝ)] ![(22092955887073/50000000000000 : ℝ), (6783862872273/50000000000000 : ℝ), (42246362467497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365602281/10000000000 : ℝ)|^4307 ≤ (22092955887073/50000000000000 : ℝ)^3283
        have hw : |(5365602281/10000000000 : ℝ)|=(5365602281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545375567/2500000000 : ℝ)|^4307 ≤ (6783862872273/50000000000000 : ℝ)^3283
        have hw : |(-545375567/2500000000 : ℝ)|=(545375567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185120383/10000000000 : ℝ)|^4307 ≤ (42246362467497/100000000000000 : ℝ)^3283
        have hw : |(5185120383/10000000000 : ℝ)|=(5185120383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365602361/10000000000 : ℝ)*x 0 + (5185120291/10000000000 : ℝ)*x 1 + (-2181502283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365602361/10000000000 : ℝ)^4307 ≤ (8837182527687/20000000000000 : ℝ)^3283 := by
    have hnat : (5365602361 : ℕ)^4307*20000000000000^3283 ≤ 8837182527687^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365602361 10000000000 8837182527687 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185120291/10000000000 : ℝ)^4307 ≤ (8449272296823/20000000000000 : ℝ)^3283 := by
    have hnat : (5185120291 : ℕ)^4307*20000000000000^3283 ≤ 8449272296823^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185120291 10000000000 8449272296823 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181502283/10000000000 : ℝ)^4307 ≤ (13567725866937/100000000000000 : ℝ)^3283 := by
    have hnat : (2181502283 : ℕ)^4307*100000000000000^3283 ≤ 13567725866937^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181502283 10000000000 13567725866937 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365602361/10000000000 : ℝ), (5185120291/10000000000 : ℝ), (-2181502283/10000000000 : ℝ)] ![(8837182527687/20000000000000 : ℝ), (8449272296823/20000000000000 : ℝ), (13567725866937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365602361/10000000000 : ℝ)|^4307 ≤ (8837182527687/20000000000000 : ℝ)^3283
        have hw : |(5365602361/10000000000 : ℝ)|=(5365602361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185120291/10000000000 : ℝ)|^4307 ≤ (8449272296823/20000000000000 : ℝ)^3283
        have hw : |(5185120291/10000000000 : ℝ)|=(5185120291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181502283/10000000000 : ℝ)|^4307 ≤ (13567725866937/100000000000000 : ℝ)^3283
        have hw : |(-2181502283/10000000000 : ℝ)|=(2181502283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159604099/5000000000 : ℝ)*x 0 + (1005422531/2500000000 : ℝ)*x 1 + (1159279491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159604099/5000000000 : ℝ)^4307 ≤ (3324169056991/10000000000000 : ℝ)^3283 := by
    have hnat : (2159604099 : ℕ)^4307*10000000000000^3283 ≤ 3324169056991^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159604099 5000000000 3324169056991 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005422531/2500000000 : ℝ)^4307 ≤ (3027051127799/10000000000000 : ℝ)^3283 := by
    have hnat : (1005422531 : ℕ)^4307*10000000000000^3283 ≤ 3027051127799^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005422531 2500000000 3027051127799 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159279491/2500000000 : ℝ)^4307 ≤ (9121949534579/25000000000000 : ℝ)^3283 := by
    have hnat : (1159279491 : ℕ)^4307*25000000000000^3283 ≤ 9121949534579^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159279491 2500000000 9121949534579 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159604099/5000000000 : ℝ), (1005422531/2500000000 : ℝ), (1159279491/2500000000 : ℝ)] ![(3324169056991/10000000000000 : ℝ), (3027051127799/10000000000000 : ℝ), (9121949534579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159604099/5000000000 : ℝ)|^4307 ≤ (3324169056991/10000000000000 : ℝ)^3283
        have hw : |(2159604099/5000000000 : ℝ)|=(2159604099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005422531/2500000000 : ℝ)|^4307 ≤ (3027051127799/10000000000000 : ℝ)^3283
        have hw : |(1005422531/2500000000 : ℝ)|=(1005422531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1159279491/2500000000 : ℝ)|^4307 ≤ (9121949534579/25000000000000 : ℝ)^3283
        have hw : |(1159279491/2500000000 : ℝ)|=(1159279491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030074127/10000000000 : ℝ)*x 0 + (5186949627/10000000000 : ℝ)*x 1 + (5476542797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030074127/10000000000 : ℝ)^4307 ≤ (2469153213713/20000000000000 : ℝ)^3283 := by
    have hnat : (2030074127 : ℕ)^4307*20000000000000^3283 ≤ 2469153213713^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030074127 10000000000 2469153213713 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186949627/10000000000 : ℝ)^4307 ≤ (42265916214741/100000000000000 : ℝ)^3283 := by
    have hnat : (5186949627 : ℕ)^4307*100000000000000^3283 ≤ 42265916214741^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186949627 10000000000 42265916214741 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476542797/10000000000 : ℝ)^4307 ≤ (9077663539733/20000000000000 : ℝ)^3283 := by
    have hnat : (5476542797 : ℕ)^4307*20000000000000^3283 ≤ 9077663539733^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476542797 10000000000 9077663539733 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030074127/10000000000 : ℝ), (5186949627/10000000000 : ℝ), (5476542797/10000000000 : ℝ)] ![(2469153213713/20000000000000 : ℝ), (42265916214741/100000000000000 : ℝ), (9077663539733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030074127/10000000000 : ℝ)|^4307 ≤ (2469153213713/20000000000000 : ℝ)^3283
        have hw : |(-2030074127/10000000000 : ℝ)|=(2030074127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186949627/10000000000 : ℝ)|^4307 ≤ (42265916214741/100000000000000 : ℝ)^3283
        have hw : |(5186949627/10000000000 : ℝ)|=(5186949627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476542797/10000000000 : ℝ)|^4307 ≤ (9077663539733/20000000000000 : ℝ)^3283
        have hw : |(5476542797/10000000000 : ℝ)|=(5476542797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644985709/5000000000 : ℝ)*x 0 + (-378015911/2000000000 : ℝ)*x 1 + (5476542783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644985709/5000000000 : ℝ)^4307 ≤ (21685313312099/50000000000000 : ℝ)^3283 := by
    have hnat : (2644985709 : ℕ)^4307*50000000000000^3283 ≤ 21685313312099^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644985709 5000000000 21685313312099 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378015911/2000000000 : ℝ)^4307 ≤ (11241055816949/100000000000000 : ℝ)^3283 := by
    have hnat : (378015911 : ℕ)^4307*100000000000000^3283 ≤ 11241055816949^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378015911 2000000000 11241055816949 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476542783/10000000000 : ℝ)^4307 ≤ (9077663509289/20000000000000 : ℝ)^3283 := by
    have hnat : (5476542783 : ℕ)^4307*20000000000000^3283 ≤ 9077663509289^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476542783 10000000000 9077663509289 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644985709/5000000000 : ℝ), (-378015911/2000000000 : ℝ), (5476542783/10000000000 : ℝ)] ![(21685313312099/50000000000000 : ℝ), (11241055816949/100000000000000 : ℝ), (9077663509289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644985709/5000000000 : ℝ)|^4307 ≤ (21685313312099/50000000000000 : ℝ)^3283
        have hw : |(2644985709/5000000000 : ℝ)|=(2644985709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378015911/2000000000 : ℝ)|^4307 ≤ (11241055816949/100000000000000 : ℝ)^3283
        have hw : |(-378015911/2000000000 : ℝ)|=(378015911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476542783/10000000000 : ℝ)|^4307 ≤ (9077663509289/20000000000000 : ℝ)^3283
        have hw : |(5476542783/10000000000 : ℝ)|=(5476542783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289971419/10000000000 : ℝ)*x 0 + (5476542803/10000000000 : ℝ)*x 1 + (-75603181/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289971419/10000000000 : ℝ)^4307 ≤ (21685313317477/50000000000000 : ℝ)^3283 := by
    have hnat : (5289971419 : ℕ)^4307*50000000000000^3283 ≤ 21685313317477^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289971419 10000000000 21685313317477 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476542803/10000000000 : ℝ)^4307 ≤ (45388317763901/100000000000000 : ℝ)^3283 := by
    have hnat : (5476542803 : ℕ)^4307*100000000000000^3283 ≤ 45388317763901^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476542803 10000000000 45388317763901 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75603181/400000000 : ℝ)^4307 ≤ (2810263895719/25000000000000 : ℝ)^3283 := by
    have hnat : (75603181 : ℕ)^4307*25000000000000^3283 ≤ 2810263895719^3283*400000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75603181 400000000 2810263895719 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289971419/10000000000 : ℝ), (5476542803/10000000000 : ℝ), (-75603181/400000000 : ℝ)] ![(21685313317477/50000000000000 : ℝ), (45388317763901/100000000000000 : ℝ), (2810263895719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289971419/10000000000 : ℝ)|^4307 ≤ (21685313317477/50000000000000 : ℝ)^3283
        have hw : |(5289971419/10000000000 : ℝ)|=(5289971419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476542803/10000000000 : ℝ)|^4307 ≤ (45388317763901/100000000000000 : ℝ)^3283
        have hw : |(5476542803/10000000000 : ℝ)|=(5476542803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75603181/400000000 : ℝ)|^4307 ≤ (2810263895719/25000000000000 : ℝ)^3283
        have hw : |(-75603181/400000000 : ℝ)|=(75603181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s2_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319343929/10000000000 : ℝ)*x 0 + (1158319771/2500000000 : ℝ)*x 1 + (62899429/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319343929/10000000000 : ℝ)^4307 ≤ (1662153051143/5000000000000 : ℝ)^3283 := by
    have hnat : (4319343929 : ℕ)^4307*5000000000000^3283 ≤ 1662153051143^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319343929 10000000000 1662153051143 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158319771/2500000000 : ℝ)^4307 ≤ (36448174718787/100000000000000 : ℝ)^3283 := by
    have hnat : (1158319771 : ℕ)^4307*100000000000000^3283 ≤ 36448174718787^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158319771 2500000000 36448174718787 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62899429/156250000 : ℝ)^4307 ≤ (15154382120351/50000000000000 : ℝ)^3283 := by
    have hnat : (62899429 : ℕ)^4307*50000000000000^3283 ≤ 15154382120351^3283*156250000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62899429 156250000 15154382120351 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319343929/10000000000 : ℝ), (1158319771/2500000000 : ℝ), (62899429/156250000 : ℝ)] ![(1662153051143/5000000000000 : ℝ), (36448174718787/100000000000000 : ℝ), (15154382120351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319343929/10000000000 : ℝ)|^4307 ≤ (1662153051143/5000000000000 : ℝ)^3283
        have hw : |(4319343929/10000000000 : ℝ)|=(4319343929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1158319771/2500000000 : ℝ)|^4307 ≤ (36448174718787/100000000000000 : ℝ)^3283
        have hw : |(1158319771/2500000000 : ℝ)|=(1158319771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62899429/156250000 : ℝ)|^4307 ≤ (15154382120351/50000000000000 : ℝ)^3283
        have hw : |(62899429/156250000 : ℝ)|=(62899429/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (607/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (867/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2471/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4021/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (607/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (867/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (607/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (867/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (607/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (867/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (607/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (867/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (607/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (867/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (607/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (867/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (867/12500 : ℝ) ^ (2153/512 : ℝ) ≤ (669488569004927/50000000000000000000 : ℝ) := by
    have hpowers : (867/12500 : ℝ)^2153 ≤ (669488569004927/50000000000000000000 : ℝ)^512 := by
      have hnat : (867 : ℕ)^2153*50000000000000000000^512 ≤ 669488569004927^512*12500^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        867 12500 669488569004927 50000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (867/12500 : ℝ)) (X := (669488569004927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (607/3125 : ℝ) ^ (2153/512 : ℝ) ≤ (12715063085906141/12500000000000000000 : ℝ) := by
    have hpowers : (607/3125 : ℝ)^2153 ≤ (12715063085906141/12500000000000000000 : ℝ)^512 := by
      have hnat : (607 : ℕ)^2153*12500000000000000000^512 ≤ 12715063085906141^512*3125^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        607 3125 12715063085906141 12500000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (607/3125 : ℝ)) (X := (12715063085906141/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000669488569004927/25000000000000000000 : ℝ) ≤ (10000063683167513/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (25000669488569004927/25000000000000000000 : ℝ)^512 ≤ (10000063683167513/10000000000000000 : ℝ)^2153 := by
      have hnat : (25000669488569004927 : ℕ)^512*10000000000000000^2153 ≤ 10000063683167513^2153*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000669488569004927 25000000000000000000 10000063683167513 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063683167513/10000000000000000 : ℝ)) (X := (25000669488569004927/25000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50051529740912629491/50000000000000000000 : ℝ) ≤ (10002449871941709/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50051529740912629491/50000000000000000000 : ℝ)^512 ≤ (10002449871941709/10000000000000000 : ℝ)^2153 := by
      have hnat : (50051529740912629491 : ℕ)^512*10000000000000000^2153 ≤ 10002449871941709^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50051529740912629491 50000000000000000000 10002449871941709 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002449871941709/10000000000000000 : ℝ)) (X := (50051529740912629491/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6262715063085906141/6250000000000000000 : ℝ) ≤ (2000967212143181/2000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (6262715063085906141/6250000000000000000 : ℝ)^512 ≤ (2000967212143181/2000000000000000 : ℝ)^2153 := by
      have hnat : (6262715063085906141 : ℕ)^512*2000000000000000^2153 ≤ 2000967212143181^2153*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6262715063085906141 6250000000000000000 2000967212143181 2000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000967212143181/2000000000000000 : ℝ)) (X := (6262715063085906141/6250000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(669488569004927/50000000000000000000 : ℝ) ≤ ((15605961758090031929/15610000000000000000 : ℝ)+2*(596547193549/312200000000000 : ℝ)*(867/12500 : ℝ))^(2153/512 : ℝ) := by
    rw [show (15605961758090031929/15610000000000000000 : ℝ)+2*(596547193549/312200000000000 : ℝ)*(867/12500 : ℝ)=(10000063683167513/10000000000000000 : ℝ) by norm_num, show 1+2*(669488569004927/50000000000000000000 : ℝ)=(25000669488569004927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12715063085906141/12500000000000000000 : ℝ)+(669488569004927/50000000000000000000 : ℝ) ≤ ((15605961758090031929/15610000000000000000 : ℝ)+(596547193549/312200000000000 : ℝ)*((607/3125 : ℝ)+(867/12500 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (15605961758090031929/15610000000000000000 : ℝ)+(596547193549/312200000000000 : ℝ)*((607/3125 : ℝ)+(867/12500 : ℝ))=(10002449871941709/10000000000000000 : ℝ) by norm_num, show 1+(12715063085906141/12500000000000000000 : ℝ)+(669488569004927/50000000000000000000 : ℝ)=(50051529740912629491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12715063085906141/12500000000000000000 : ℝ) ≤ ((15605961758090031929/15610000000000000000 : ℝ)+2*(596547193549/312200000000000 : ℝ)*(607/3125 : ℝ))^(2153/512 : ℝ) := by
    rw [show (15605961758090031929/15610000000000000000 : ℝ)+2*(596547193549/312200000000000 : ℝ)*(607/3125 : ℝ)=(2000967212143181/2000000000000000 : ℝ) by norm_num, show 1+2*(12715063085906141/12500000000000000000 : ℝ)=(6262715063085906141/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15605961758090031929/15610000000000000000 : ℝ)*(X 1 0+X 2 0)+(596547193549/312200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (867/12500 : ℝ)) (hi := (607/3125 : ℝ)) (c := (15605961758090031929/15610000000000000000 : ℝ)) (alpha := (596547193549/312200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15605961758090031929/15610000000000000000 : ℝ)*(X 0 1+X 2 1)+(596547193549/312200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (867/12500 : ℝ)) (hi := (607/3125 : ℝ)) (c := (15605961758090031929/15610000000000000000 : ℝ)) (alpha := (596547193549/312200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15605961758090031929/15610000000000000000 : ℝ)*(X 0 2+X 1 2)+(596547193549/312200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (867/12500 : ℝ)) (hi := (607/3125 : ℝ)) (c := (15605961758090031929/15610000000000000000 : ℝ)) (alpha := (596547193549/312200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-507502403/2500000000 : ℝ)*X 0 0+(1095677767/2000000000 : ℝ)*X 0 1+(518511999/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365602281/10000000000 : ℝ)*X 1 0+(-545375567/2500000000 : ℝ)*X 1 1+(5185120383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5365602361/10000000000 : ℝ)*X 2 0+(5185120291/10000000000 : ℝ)*X 2 1+(-2181502283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159604099/5000000000 : ℝ)*X 0 0+(1005422531/2500000000 : ℝ)*X 0 1+(1159279491/2500000000 : ℝ)*X 0 2+(2159604099/5000000000 : ℝ)*X 1 0+(1005422531/2500000000 : ℝ)*X 1 1+(1159279491/2500000000 : ℝ)*X 1 2+(2159604099/5000000000 : ℝ)*X 2 0+(1005422531/2500000000 : ℝ)*X 2 1+(1159279491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2030074127/10000000000 : ℝ)*X 0 0+(5186949627/10000000000 : ℝ)*X 0 1+(5476542797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644985709/5000000000 : ℝ)*X 1 0+(-378015911/2000000000 : ℝ)*X 1 1+(5476542783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289971419/10000000000 : ℝ)*X 2 0+(5476542803/10000000000 : ℝ)*X 2 1+(-75603181/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319343929/10000000000 : ℝ)*X 0 0+(1158319771/2500000000 : ℝ)*X 0 1+(62899429/156250000 : ℝ)*X 0 2+(4319343929/10000000000 : ℝ)*X 1 0+(1158319771/2500000000 : ℝ)*X 1 1+(62899429/156250000 : ℝ)*X 1 2+(4319343929/10000000000 : ℝ)*X 2 0+(1158319771/2500000000 : ℝ)*X 2 1+(62899429/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1769038929519788662994997261/195125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (799367963/50000000000000 : ℝ)*(base19) + (1595128063/100000000000000 : ℝ)*(base23) + (1168597/4000000000000 : ℝ)*(lower2) + (215787299/100000000000000 : ℝ)*(upper3) + (169888231/100000000000000 : ℝ)*(upper5) + (1258698686982703/50000000000000 : ℝ)*(major0) + (1258698686982703/50000000000000 : ℝ)*(major1) + (1258698686982703/50000000000000 : ℝ)*(major2) + (852466074813951/25000000000000 : ℝ)*(sp0) + (53279473571929/1562500000000 : ℝ)*(sp1) + (1704943156105659/50000000000000 : ℝ)*(sp2) + (812447905515983/50000000000000 : ℝ)*(sp3) + (11804041789/50000000000000 : ℝ)*(sp4) + (5363676681/50000000000000 : ℝ)*(sp7) + (1624906538385327/100000000000000 : ℝ)*(f.failure) + (1704943953669691/50000000000000 : ℝ)*(f.sum) + (42848823901213/7805000000000000000000000000 : ℝ)*base66 + (628649459645846559/111500000000000000000000000000000 : ℝ)*base68 + (686978229861846559/111500000000000000000000000000000 : ℝ)*base70 + (19716936331846559/111500000000000000000000000000000 : ℝ)*base72 + (51465730222173/7805000000000000000000000000 : ℝ)*base74 + (291826023314846559/111500000000000000000000000000000 : ℝ)*base76 + (861947647144846559/111500000000000000000000000000000 : ℝ)*base78 + (1433299993546153441/111500000000000000000000000000000 : ℝ)*base79 + (10804188540837/7805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2448157/1250000000000000000000 : ℝ)*base90 + (2448157/1250000000000000000000 : ℝ)*base92 + (2448157/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91721653659402796861034331/27875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19037557/2500000000000 : ℝ)*(base19) + (442982617/50000000000000 : ℝ)*(base23) + (93383177/100000000000000 : ℝ)*(upper3) + (1455287/3125000000000 : ℝ)*(lower4) + (28858053/100000000000000 : ℝ)*(upper5) + (637328152928397/25000000000000 : ℝ)*(major0) + (637328152928397/25000000000000 : ℝ)*(major1) + (637328152928397/25000000000000 : ℝ)*(major2) + (4224876933/50000000000000 : ℝ)*(sp1) + (5476083389/50000000000000 : ℝ)*(sp2) + (3453118220792183/100000000000000 : ℝ)*(sp4) + (3453109009536037/100000000000000 : ℝ)*(sp5) + (3453106382660171/100000000000000 : ℝ)*(sp6) + (411376723238223/25000000000000 : ℝ)*(sp7) + (411376723238223/25000000000000 : ℝ)*(f.failure) + (3453118220792183/100000000000000 : ℝ)*(f.sum) + (2492642953453/1115000000000000000000000000 : ℝ)*base65 + (45261868278401741/55750000000000000000000000000000 : ℝ)*base68 + (19059030098901741/55750000000000000000000000000000 : ℝ)*base70 + (249299888991651741/55750000000000000000000000000000 : ℝ)*base72 + (205295650517/1115000000000000000000000000 : ℝ)*base74 + (470515048337401741/55750000000000000000000000000000 : ℝ)*base76 + (328077799737901741/55750000000000000000000000000000 : ℝ)*base78 + (449579041105901741/55750000000000000000000000000000 : ℝ)*base80 + (3685895464213/1115000000000000000000000000 : ℝ)*base81 + (1795107/312500000000000000000 : ℝ)*base89 + (1795107/312500000000000000000 : ℝ)*base91 + (1795107/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1347_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (607/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (867/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1347_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1347_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1347_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1347_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2471/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4021/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
