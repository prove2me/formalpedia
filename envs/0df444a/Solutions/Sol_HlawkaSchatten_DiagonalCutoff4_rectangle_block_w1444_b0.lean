-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1444_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:30.066264+00:00
-- url     : https://prove2.me/submissions/0a2a5093-3cd7-4df8-a321-bfb4a16b2b33

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
theorem support_rectangle_w1444_s0_0 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-350070387/2000000000 : ℝ)*x 0 + (5954015531/10000000000 : ℝ)*x 1 + (1208664087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (350070387/2000000000 : ℝ)^1101 ≤ (10323422901501/100000000000000 : ℝ)^845 := by
    have hnat : (350070387 : ℕ)^1101*100000000000000^845 ≤ 10323422901501^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350070387 2000000000 10323422901501 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5954015531/10000000000 : ℝ)^1101 ≤ (25442320181417/50000000000000 : ℝ)^845 := by
    have hnat : (5954015531 : ℕ)^1101*50000000000000^845 ≤ 25442320181417^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954015531 10000000000 25442320181417 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208664087/2500000000 : ℝ)^1101 ≤ (969798418151/2500000000000 : ℝ)^845 := by
    have hnat : (1208664087 : ℕ)^1101*2500000000000^845 ≤ 969798418151^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208664087 2500000000 969798418151 2500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-350070387/2000000000 : ℝ), (5954015531/10000000000 : ℝ), (1208664087/2500000000 : ℝ)] ![(10323422901501/100000000000000 : ℝ), (25442320181417/50000000000000 : ℝ), (969798418151/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-350070387/2000000000 : ℝ)|^1101 ≤ (10323422901501/100000000000000 : ℝ)^845
        have hw : |(-350070387/2000000000 : ℝ)|=(350070387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5954015531/10000000000 : ℝ)|^1101 ≤ (25442320181417/50000000000000 : ℝ)^845
        have hw : |(5954015531/10000000000 : ℝ)|=(5954015531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208664087/2500000000 : ℝ)|^1101 ≤ (969798418151/2500000000000 : ℝ)^845
        have hw : |(1208664087/2500000000 : ℝ)|=(1208664087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_1 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (274521637/500000000 : ℝ)*x 0 + (-238202021/1000000000 : ℝ)*x 1 + (1208664051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274521637/500000000 : ℝ)^1101 ≤ (22892233018371/50000000000000 : ℝ)^845 := by
    have hnat : (274521637 : ℕ)^1101*50000000000000^845 ≤ 22892233018371^845*500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274521637 500000000 22892233018371 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238202021/1000000000 : ℝ)^1101 ≤ (7711799364029/50000000000000 : ℝ)^845 := by
    have hnat : (238202021 : ℕ)^1101*50000000000000^845 ≤ 7711799364029^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238202021 1000000000 7711799364029 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208664051/2500000000 : ℝ)^1101 ≤ (38791935220581/100000000000000 : ℝ)^845 := by
    have hnat : (1208664051 : ℕ)^1101*100000000000000^845 ≤ 38791935220581^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208664051 2500000000 38791935220581 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(274521637/500000000 : ℝ), (-238202021/1000000000 : ℝ), (1208664051/2500000000 : ℝ)] ![(22892233018371/50000000000000 : ℝ), (7711799364029/50000000000000 : ℝ), (38791935220581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(274521637/500000000 : ℝ)|^1101 ≤ (22892233018371/50000000000000 : ℝ)^845
        have hw : |(274521637/500000000 : ℝ)|=(274521637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238202021/1000000000 : ℝ)|^1101 ≤ (7711799364029/50000000000000 : ℝ)^845
        have hw : |(-238202021/1000000000 : ℝ)|=(238202021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208664051/2500000000 : ℝ)|^1101 ≤ (38791935220581/100000000000000 : ℝ)^845
        have hw : |(1208664051/2500000000 : ℝ)|=(1208664051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_2 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2745216317/5000000000 : ℝ)*x 0 + (4834656169/10000000000 : ℝ)*x 1 + (-238202039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745216317/5000000000 : ℝ)^1101 ≤ (45784464885019/100000000000000 : ℝ)^845 := by
    have hnat : (2745216317 : ℕ)^1101*100000000000000^845 ≤ 45784464885019^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745216317 5000000000 45784464885019 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4834656169/10000000000 : ℝ)^1101 ≤ (38791934854671/100000000000000 : ℝ)^845 := by
    have hnat : (4834656169 : ℕ)^1101*100000000000000^845 ≤ 38791934854671^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834656169 10000000000 38791934854671 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238202039/1000000000 : ℝ)^1101 ≤ (7711800123329/50000000000000 : ℝ)^845 := by
    have hnat : (238202039 : ℕ)^1101*50000000000000^845 ≤ 7711800123329^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238202039 1000000000 7711800123329 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745216317/5000000000 : ℝ), (4834656169/10000000000 : ℝ), (-238202039/1000000000 : ℝ)] ![(45784464885019/100000000000000 : ℝ), (38791934854671/100000000000000 : ℝ), (7711800123329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745216317/5000000000 : ℝ)|^1101 ≤ (45784464885019/100000000000000 : ℝ)^845
        have hw : |(2745216317/5000000000 : ℝ)|=(2745216317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4834656169/10000000000 : ℝ)|^1101 ≤ (38791934854671/100000000000000 : ℝ)^845
        have hw : |(4834656169/10000000000 : ℝ)|=(4834656169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238202039/1000000000 : ℝ)|^1101 ≤ (7711800123329/50000000000000 : ℝ)^845
        have hw : |(-238202039/1000000000 : ℝ)|=(238202039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_3 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (520482187/1250000000 : ℝ)*x 0 + (387877101/1250000000 : ℝ)*x 1 + (1384470071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520482187/1250000000 : ℝ)^1101 ≤ (31931466397257/100000000000000 : ℝ)^845 := by
    have hnat : (520482187 : ℕ)^1101*100000000000000^845 ≤ 31931466397257^845*1250000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520482187 1250000000 31931466397257 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387877101/1250000000 : ℝ)^1101 ≤ (5441965420443/25000000000000 : ℝ)^845 := by
    have hnat : (387877101 : ℕ)^1101*25000000000000^845 ≤ 5441965420443^845*1250000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387877101 1250000000 5441965420443 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1384470071/2500000000 : ℝ)^1101 ≤ (46300671903637/100000000000000 : ℝ)^845 := by
    have hnat : (1384470071 : ℕ)^1101*100000000000000^845 ≤ 46300671903637^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384470071 2500000000 46300671903637 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520482187/1250000000 : ℝ), (387877101/1250000000 : ℝ), (1384470071/2500000000 : ℝ)] ![(31931466397257/100000000000000 : ℝ), (5441965420443/25000000000000 : ℝ), (46300671903637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520482187/1250000000 : ℝ)|^1101 ≤ (31931466397257/100000000000000 : ℝ)^845
        have hw : |(520482187/1250000000 : ℝ)|=(520482187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(387877101/1250000000 : ℝ)|^1101 ≤ (5441965420443/25000000000000 : ℝ)^845
        have hw : |(387877101/1250000000 : ℝ)|=(387877101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1384470071/2500000000 : ℝ)|^1101 ≤ (46300671903637/100000000000000 : ℝ)^845
        have hw : |(1384470071/2500000000 : ℝ)|=(1384470071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_4 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1754298171/10000000000 : ℝ)*x 0 + (2431631207/5000000000 : ℝ)*x 1 + (2962193931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1754298171/10000000000 : ℝ)^1101 ≤ (10353759034481/100000000000000 : ℝ)^845 := by
    have hnat : (1754298171 : ℕ)^1101*100000000000000^845 ≤ 10353759034481^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754298171 10000000000 10353759034481 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431631207/5000000000 : ℝ)^1101 ≤ (39091268723171/100000000000000 : ℝ)^845 := by
    have hnat : (2431631207 : ℕ)^1101*100000000000000^845 ≤ 39091268723171^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431631207 5000000000 39091268723171 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2962193931/5000000000 : ℝ)^1101 ≤ (10110994444581/20000000000000 : ℝ)^845 := by
    have hnat : (2962193931 : ℕ)^1101*20000000000000^845 ≤ 10110994444581^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2962193931 5000000000 10110994444581 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1754298171/10000000000 : ℝ), (2431631207/5000000000 : ℝ), (2962193931/5000000000 : ℝ)] ![(10353759034481/100000000000000 : ℝ), (39091268723171/100000000000000 : ℝ), (10110994444581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1754298171/10000000000 : ℝ)|^1101 ≤ (10353759034481/100000000000000 : ℝ)^845
        have hw : |(-1754298171/10000000000 : ℝ)|=(1754298171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2431631207/5000000000 : ℝ)|^1101 ≤ (39091268723171/100000000000000 : ℝ)^845
        have hw : |(2431631207/5000000000 : ℝ)|=(2431631207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2962193931/5000000000 : ℝ)|^1101 ≤ (10110994444581/20000000000000 : ℝ)^845
        have hw : |(2962193931/5000000000 : ℝ)|=(2962193931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_5 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (518484927/1000000000 : ℝ)*x 0 + (-129228871/1000000000 : ℝ)*x 1 + (5924387931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518484927/1000000000 : ℝ)^1101 ≤ (42492570157397/100000000000000 : ℝ)^845 := by
    have hnat : (518484927 : ℕ)^1101*100000000000000^845 ≤ 42492570157397^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518484927 1000000000 42492570157397 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129228871/1000000000 : ℝ)^1101 ≤ (139049136783/2000000000000 : ℝ)^845 := by
    have hnat : (129228871 : ℕ)^1101*2000000000000^845 ≤ 139049136783^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129228871 1000000000 139049136783 2000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5924387931/10000000000 : ℝ)^1101 ≤ (5055497299009/10000000000000 : ℝ)^845 := by
    have hnat : (5924387931 : ℕ)^1101*10000000000000^845 ≤ 5055497299009^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5924387931 10000000000 5055497299009 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518484927/1000000000 : ℝ), (-129228871/1000000000 : ℝ), (5924387931/10000000000 : ℝ)] ![(42492570157397/100000000000000 : ℝ), (139049136783/2000000000000 : ℝ), (5055497299009/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518484927/1000000000 : ℝ)|^1101 ≤ (42492570157397/100000000000000 : ℝ)^845
        have hw : |(518484927/1000000000 : ℝ)|=(518484927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129228871/1000000000 : ℝ)|^1101 ≤ (139049136783/2000000000000 : ℝ)^845
        have hw : |(-129228871/1000000000 : ℝ)|=(129228871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5924387931/10000000000 : ℝ)|^1101 ≤ (5055497299009/10000000000000 : ℝ)^845
        have hw : |(5924387931/10000000000 : ℝ)|=(5924387931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_6 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5184849299/10000000000 : ℝ)*x 0 + (5924387777/10000000000 : ℝ)*x 1 + (-1292288911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184849299/10000000000 : ℝ)^1101 ≤ (42492570467071/100000000000000 : ℝ)^845 := by
    have hnat : (5184849299 : ℕ)^1101*100000000000000^845 ≤ 42492570467071^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184849299 10000000000 42492570467071 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5924387777/10000000000 : ℝ)^1101 ≤ (50554971277823/100000000000000 : ℝ)^845 := by
    have hnat : (5924387777 : ℕ)^1101*100000000000000^845 ≤ 50554971277823^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5924387777 10000000000 50554971277823 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292288911/10000000000 : ℝ)^1101 ≤ (1738114562033/25000000000000 : ℝ)^845 := by
    have hnat : (1292288911 : ℕ)^1101*25000000000000^845 ≤ 1738114562033^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292288911 10000000000 1738114562033 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184849299/10000000000 : ℝ), (5924387777/10000000000 : ℝ), (-1292288911/10000000000 : ℝ)] ![(42492570467071/100000000000000 : ℝ), (50554971277823/100000000000000 : ℝ), (1738114562033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184849299/10000000000 : ℝ)|^1101 ≤ (42492570467071/100000000000000 : ℝ)^845
        have hw : |(5184849299/10000000000 : ℝ)|=(5184849299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5924387777/10000000000 : ℝ)|^1101 ≤ (50554971277823/100000000000000 : ℝ)^845
        have hw : |(5924387777/10000000000 : ℝ)|=(5924387777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1292288911/10000000000 : ℝ)|^1101 ≤ (1738114562033/25000000000000 : ℝ)^845
        have hw : |(-1292288911/10000000000 : ℝ)|=(1292288911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s0_7 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4172440651/10000000000 : ℝ)*x 0 + (1368913781/2500000000 : ℝ)*x 1 + (3167464039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172440651/10000000000 : ℝ)^1101 ≤ (3201725628387/10000000000000 : ℝ)^845 := by
    have hnat : (4172440651 : ℕ)^1101*10000000000000^845 ≤ 3201725628387^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172440651 10000000000 3201725628387 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368913781/2500000000 : ℝ)^1101 ≤ (4562396813761/10000000000000 : ℝ)^845 := by
    have hnat : (1368913781 : ℕ)^1101*10000000000000^845 ≤ 4562396813761^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368913781 2500000000 4562396813761 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167464039/10000000000 : ℝ)^1101 ≤ (11179387779923/50000000000000 : ℝ)^845 := by
    have hnat : (3167464039 : ℕ)^1101*50000000000000^845 ≤ 11179387779923^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167464039 10000000000 11179387779923 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172440651/10000000000 : ℝ), (1368913781/2500000000 : ℝ), (3167464039/10000000000 : ℝ)] ![(3201725628387/10000000000000 : ℝ), (4562396813761/10000000000000 : ℝ), (11179387779923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172440651/10000000000 : ℝ)|^1101 ≤ (3201725628387/10000000000000 : ℝ)^845
        have hw : |(4172440651/10000000000 : ℝ)|=(4172440651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368913781/2500000000 : ℝ)|^1101 ≤ (4562396813761/10000000000000 : ℝ)^845
        have hw : |(1368913781/2500000000 : ℝ)|=(1368913781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167464039/10000000000 : ℝ)|^1101 ≤ (11179387779923/50000000000000 : ℝ)^845
        have hw : |(3167464039/10000000000 : ℝ)|=(3167464039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1444_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2153/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5231/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4403/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4403 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4403*1^1024 ≤ 0^1024*1^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4403/1024 : ℝ) ≤ (389014402949769619/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4403 ≤ (389014402949769619/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4403*20000000000000000000^1024 ≤ 389014402949769619^1024*5^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 389014402949769619 20000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (389014402949769619/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4403 := by
      have hnat : (1 : ℕ)^1024*1^4403 ≤ 1^4403*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20389014402949769619/20000000000000000000 : ℝ) ≤ (2511225620525887/2500000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (20389014402949769619/20000000000000000000 : ℝ)^1024 ≤ (2511225620525887/2500000000000000 : ℝ)^4403 := by
      have hnat : (20389014402949769619 : ℕ)^1024*2500000000000000^4403 ≤ 2511225620525887^4403*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20389014402949769619 20000000000000000000 2511225620525887 2500000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511225620525887/2500000000000000 : ℝ)) (X := (20389014402949769619/20000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10389014402949769619/10000000000000000000 : ℝ) ≤ (1261225620525887/1250000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (10389014402949769619/10000000000000000000 : ℝ)^1024 ≤ (1261225620525887/1250000000000000 : ℝ)^4403 := by
      have hnat : (10389014402949769619 : ℕ)^1024*1250000000000000^4403 ≤ 1261225620525887^4403*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10389014402949769619 10000000000000000000 1261225620525887 1250000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261225620525887/1250000000000000 : ℝ)) (X := (10389014402949769619/10000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11225620525887/1000000000000000 : ℝ)*(0 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11225620525887/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(389014402949769619/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11225620525887/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4403/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11225620525887/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511225620525887/2500000000000000 : ℝ) by norm_num, show 1+(389014402949769619/20000000000000000000 : ℝ)+(0 : ℝ)=(20389014402949769619/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(389014402949769619/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11225620525887/1000000000000000 : ℝ)*(2/5 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11225620525887/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261225620525887/1250000000000000 : ℝ) by norm_num, show 1+2*(389014402949769619/20000000000000000000 : ℝ)=(10389014402949769619/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11225620525887/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11225620525887/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11225620525887/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11225620525887/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11225620525887/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11225620525887/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-350070387/2000000000 : ℝ)*X 0 0+(5954015531/10000000000 : ℝ)*X 0 1+(1208664087/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((274521637/500000000 : ℝ)*X 1 0+(-238202021/1000000000 : ℝ)*X 1 1+(1208664051/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2745216317/5000000000 : ℝ)*X 2 0+(4834656169/10000000000 : ℝ)*X 2 1+(-238202039/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((520482187/1250000000 : ℝ)*X 0 0+(387877101/1250000000 : ℝ)*X 0 1+(1384470071/2500000000 : ℝ)*X 0 2+(520482187/1250000000 : ℝ)*X 1 0+(387877101/1250000000 : ℝ)*X 1 1+(1384470071/2500000000 : ℝ)*X 1 2+(520482187/1250000000 : ℝ)*X 2 0+(387877101/1250000000 : ℝ)*X 2 1+(1384470071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1754298171/10000000000 : ℝ)*X 0 0+(2431631207/5000000000 : ℝ)*X 0 1+(2962193931/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518484927/1000000000 : ℝ)*X 1 0+(-129228871/1000000000 : ℝ)*X 1 1+(5924387931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184849299/10000000000 : ℝ)*X 2 0+(5924387777/10000000000 : ℝ)*X 2 1+(-1292288911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4172440651/10000000000 : ℝ)*X 0 0+(1368913781/2500000000 : ℝ)*X 0 1+(3167464039/10000000000 : ℝ)*X 0 2+(4172440651/10000000000 : ℝ)*X 1 0+(1368913781/2500000000 : ℝ)*X 1 1+(3167464039/10000000000 : ℝ)*X 1 2+(4172440651/10000000000 : ℝ)*X 2 0+(1368913781/2500000000 : ℝ)*X 2 1+(3167464039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16221854548047065557929/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144502139/100000000000000 : ℝ)*(base1) + (586093723/50000000000000 : ℝ)*(base19) + (115493969/10000000000000 : ℝ)*(base23) + (759843/500000000000 : ℝ)*(upper3) + (98260183/100000000000000 : ℝ)*(upper5) + (81504954945843/12500000000000 : ℝ)*(major0) + (81504954945843/12500000000000 : ℝ)*(major1) + (81504954945843/12500000000000 : ℝ)*(major2) + (893371888471459/100000000000000 : ℝ)*(sp0) + (446686987136109/50000000000000 : ℝ)*(sp1) + (893373991519973/100000000000000 : ℝ)*(sp2) + (205351058524959/50000000000000 : ℝ)*(sp3) + (425311293/12500000000000 : ℝ)*(sp4) + (1698088643/100000000000000 : ℝ)*(sp7) + (410703959640701/100000000000000 : ℝ)*(f.failure) + (55835946653729/6250000000000 : ℝ)*(f.sum) + (26915339962741/6250000000000000000000000000 : ℝ)*base65 + (66745031775241/12500000000000000000000000000 : ℝ)*base67 + (16466738925241/12500000000000000000000000000 : ℝ)*base69 + (89030149025241/12500000000000000000000000000 : ℝ)*base71 + (21210185187741/6250000000000000000000000000 : ℝ)*base73 + (100197186275241/12500000000000000000000000000 : ℝ)*base75 + (143500379500241/12500000000000000000000000000 : ℝ)*base77 + (186222490625241/12500000000000000000000000000 : ℝ)*base79 + (12751837456009/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2949769/10000000000000000000000 : ℝ)*base89 + (2949769/10000000000000000000000 : ℝ)*base91 + (2949769/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12329304837893517673659/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352145777/25000000000000 : ℝ)*(base19) + (710434183/50000000000000 : ℝ)*(base23) + (8820733/6250000000000 : ℝ)*(base32) + (106682313/50000000000000 : ℝ)*(upper3) + (125366851/100000000000000 : ℝ)*(upper5) + (27512694118119/4000000000000 : ℝ)*(major0) + (27512694118119/4000000000000 : ℝ)*(major1) + (27512694118119/4000000000000 : ℝ)*(major2) + (3369836101/100000000000000 : ℝ)*(sp1) + (3488848639/100000000000000 : ℝ)*(sp2) + (942395026579597/100000000000000 : ℝ)*(sp4) + (942390248160387/100000000000000 : ℝ)*(sp5) + (7362422787989/781250000000 : ℝ)*(sp6) + (216619666353103/50000000000000 : ℝ)*(sp7) + (216619736918967/50000000000000 : ℝ)*(f.failure) + (942395026579597/100000000000000 : ℝ)*(f.sum) + (1522250791447/2000000000000000000000000000 : ℝ)*base66 + (12221008438553/4000000000000000000000000000 : ℝ)*base67 + (422635345447/4000000000000000000000000000 : ℝ)*base70 + (21186097902553/4000000000000000000000000000 : ℝ)*base71 + (1442659881447/2000000000000000000000000000 : ℝ)*base74 + (31520331506553/4000000000000000000000000000 : ℝ)*base75 + (12712522286553/4000000000000000000000000000 : ℝ)*base77 + (4970709170553/4000000000000000000000000000 : ℝ)*base79 + (5985643777447/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (15117477/5000000000000000000000 : ℝ)*base90 + (15117477/5000000000000000000000 : ℝ)*base92 + (15117477/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1444_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5231/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1444_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1444_s1_0 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-960292987/5000000000 : ℝ)*x 0 + (111985517/200000000 : ℝ)*x 1 + (5080236801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (960292987/5000000000 : ℝ)^1101 ≤ (2912620279061/25000000000000 : ℝ)^845 := by
    have hnat : (960292987 : ℕ)^1101*25000000000000^845 ≤ 2912620279061^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960292987 5000000000 2912620279061 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111985517/200000000 : ℝ)^1101 ≤ (9173948331/19531250000 : ℝ)^845 := by
    have hnat : (111985517 : ℕ)^1101*19531250000^845 ≤ 9173948331^845*200000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111985517 200000000 9173948331 19531250000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080236801/10000000000 : ℝ)^1101 ≤ (10344725853807/25000000000000 : ℝ)^845 := by
    have hnat : (5080236801 : ℕ)^1101*25000000000000^845 ≤ 10344725853807^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080236801 10000000000 10344725853807 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-960292987/5000000000 : ℝ), (111985517/200000000 : ℝ), (5080236801/10000000000 : ℝ)] ![(2912620279061/25000000000000 : ℝ), (9173948331/19531250000 : ℝ), (10344725853807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-960292987/5000000000 : ℝ)|^1101 ≤ (2912620279061/25000000000000 : ℝ)^845
        have hw : |(-960292987/5000000000 : ℝ)|=(960292987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111985517/200000000 : ℝ)|^1101 ≤ (9173948331/19531250000 : ℝ)^845
        have hw : |(111985517/200000000 : ℝ)|=(111985517/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080236801/10000000000 : ℝ)|^1101 ≤ (10344725853807/25000000000000 : ℝ)^845
        have hw : |(5080236801/10000000000 : ℝ)|=(5080236801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_1 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5395311039/10000000000 : ℝ)*x 0 + (-1097653501/5000000000 : ℝ)*x 1 + (5080238329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395311039/10000000000 : ℝ)^1101 ≤ (5594207809279/12500000000000 : ℝ)^845 := by
    have hnat : (5395311039 : ℕ)^1101*12500000000000^845 ≤ 5594207809279^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395311039 10000000000 5594207809279 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097653501/5000000000 : ℝ)^1101 ≤ (1386741787209/10000000000000 : ℝ)^845 := by
    have hnat : (1097653501 : ℕ)^1101*10000000000000^845 ≤ 1386741787209^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097653501 5000000000 1386741787209 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080238329/10000000000 : ℝ)^1101 ≤ (1655156785257/4000000000000 : ℝ)^845 := by
    have hnat : (5080238329 : ℕ)^1101*4000000000000^845 ≤ 1655156785257^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080238329 10000000000 1655156785257 4000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395311039/10000000000 : ℝ), (-1097653501/5000000000 : ℝ), (5080238329/10000000000 : ℝ)] ![(5594207809279/12500000000000 : ℝ), (1386741787209/10000000000000 : ℝ), (1655156785257/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395311039/10000000000 : ℝ)|^1101 ≤ (5594207809279/12500000000000 : ℝ)^845
        have hw : |(5395311039/10000000000 : ℝ)|=(5395311039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097653501/5000000000 : ℝ)|^1101 ≤ (1386741787209/10000000000000 : ℝ)^845
        have hw : |(-1097653501/5000000000 : ℝ)|=(1097653501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080238329/10000000000 : ℝ)|^1101 ≤ (1655156785257/4000000000000 : ℝ)^845
        have hw : |(5080238329/10000000000 : ℝ)|=(5080238329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_2 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5395312271/10000000000 : ℝ)*x 0 + (1270059237/2500000000 : ℝ)*x 1 + (-1097653583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395312271/10000000000 : ℝ)^1101 ≤ (5594209473701/12500000000000 : ℝ)^845 := by
    have hnat : (5395312271 : ℕ)^1101*12500000000000^845 ≤ 5594209473701^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395312271 10000000000 5594209473701 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270059237/2500000000 : ℝ)^1101 ≤ (20689452487647/50000000000000 : ℝ)^845 := by
    have hnat : (1270059237 : ℕ)^1101*50000000000000^845 ≤ 20689452487647^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270059237 2500000000 20689452487647 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097653583/5000000000 : ℝ)^1101 ≤ (13867419221907/100000000000000 : ℝ)^845 := by
    have hnat : (1097653583 : ℕ)^1101*100000000000000^845 ≤ 13867419221907^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097653583 5000000000 13867419221907 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395312271/10000000000 : ℝ), (1270059237/2500000000 : ℝ), (-1097653583/5000000000 : ℝ)] ![(5594209473701/12500000000000 : ℝ), (20689452487647/50000000000000 : ℝ), (13867419221907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395312271/10000000000 : ℝ)|^1101 ≤ (5594209473701/12500000000000 : ℝ)^845
        have hw : |(5395312271/10000000000 : ℝ)|=(5395312271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270059237/2500000000 : ℝ)|^1101 ≤ (20689452487647/50000000000000 : ℝ)^845
        have hw : |(1270059237/2500000000 : ℝ)|=(1270059237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097653583/5000000000 : ℝ)|^1101 ≤ (13867419221907/100000000000000 : ℝ)^845
        have hw : |(-1097653583/5000000000 : ℝ)|=(1097653583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_3 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (854781661/2000000000 : ℝ)*x 0 + (3742466197/10000000000 : ℝ)*x 1 + (1217872951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854781661/2000000000 : ℝ)^1101 ≤ (33035472838691/100000000000000 : ℝ)^845 := by
    have hnat : (854781661 : ℕ)^1101*100000000000000^845 ≤ 33035472838691^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854781661 2000000000 33035472838691 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3742466197/10000000000 : ℝ)^1101 ≤ (6946761912033/25000000000000 : ℝ)^845 := by
    have hnat : (3742466197 : ℕ)^1101*25000000000000^845 ≤ 6946761912033^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742466197 10000000000 6946761912033 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217872951/2500000000 : ℝ)^1101 ≤ (9794369876043/25000000000000 : ℝ)^845 := by
    have hnat : (1217872951 : ℕ)^1101*25000000000000^845 ≤ 9794369876043^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217872951 2500000000 9794369876043 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854781661/2000000000 : ℝ), (3742466197/10000000000 : ℝ), (1217872951/2500000000 : ℝ)] ![(33035472838691/100000000000000 : ℝ), (6946761912033/25000000000000 : ℝ), (9794369876043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854781661/2000000000 : ℝ)|^1101 ≤ (33035472838691/100000000000000 : ℝ)^845
        have hw : |(854781661/2000000000 : ℝ)|=(854781661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3742466197/10000000000 : ℝ)|^1101 ≤ (6946761912033/25000000000000 : ℝ)^845
        have hw : |(3742466197/10000000000 : ℝ)|=(3742466197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1217872951/2500000000 : ℝ)|^1101 ≤ (9794369876043/25000000000000 : ℝ)^845
        have hw : |(1217872951/2500000000 : ℝ)|=(1217872951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_4 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920964081/10000000000 : ℝ)*x 0 + (2543125999/5000000000 : ℝ)*x 1 + (349572491/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920964081/10000000000 : ℝ)^1101 ≤ (11653469720329/100000000000000 : ℝ)^845 := by
    have hnat : (1920964081 : ℕ)^1101*100000000000000^845 ≤ 11653469720329^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920964081 10000000000 11653469720329 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543125999/5000000000 : ℝ)^1101 ≤ (2590172019079/6250000000000 : ℝ)^845 := by
    have hnat : (2543125999 : ℕ)^1101*6250000000000^845 ≤ 2590172019079^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543125999 5000000000 2590172019079 6250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349572491/625000000 : ℝ)^1101 ≤ (11725944489877/25000000000000 : ℝ)^845 := by
    have hnat : (349572491 : ℕ)^1101*25000000000000^845 ≤ 11725944489877^845*625000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349572491 625000000 11725944489877 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920964081/10000000000 : ℝ), (2543125999/5000000000 : ℝ), (349572491/625000000 : ℝ)] ![(11653469720329/100000000000000 : ℝ), (2590172019079/6250000000000 : ℝ), (11725944489877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920964081/10000000000 : ℝ)|^1101 ≤ (11653469720329/100000000000000 : ℝ)^845
        have hw : |(-1920964081/10000000000 : ℝ)|=(1920964081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543125999/5000000000 : ℝ)|^1101 ≤ (2590172019079/6250000000000 : ℝ)^845
        have hw : |(2543125999/5000000000 : ℝ)|=(2543125999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(349572491/625000000 : ℝ)|^1101 ≤ (11725944489877/25000000000000 : ℝ)^845
        have hw : |(349572491/625000000 : ℝ)|=(349572491/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_5 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5259551399/10000000000 : ℝ)*x 0 + (-168238493/1000000000 : ℝ)*x 1 + (2796579941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259551399/10000000000 : ℝ)^1101 ≤ (43292006915039/100000000000000 : ℝ)^845 := by
    have hnat : (5259551399 : ℕ)^1101*100000000000000^845 ≤ 43292006915039^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259551399 10000000000 43292006915039 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168238493/1000000000 : ℝ)^1101 ≤ (980421482471/10000000000000 : ℝ)^845 := by
    have hnat : (168238493 : ℕ)^1101*10000000000000^845 ≤ 980421482471^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168238493 1000000000 980421482471 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2796579941/5000000000 : ℝ)^1101 ≤ (46903778243597/100000000000000 : ℝ)^845 := by
    have hnat : (2796579941 : ℕ)^1101*100000000000000^845 ≤ 46903778243597^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796579941 5000000000 46903778243597 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259551399/10000000000 : ℝ), (-168238493/1000000000 : ℝ), (2796579941/5000000000 : ℝ)] ![(43292006915039/100000000000000 : ℝ), (980421482471/10000000000000 : ℝ), (46903778243597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259551399/10000000000 : ℝ)|^1101 ≤ (43292006915039/100000000000000 : ℝ)^845
        have hw : |(5259551399/10000000000 : ℝ)|=(5259551399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168238493/1000000000 : ℝ)|^1101 ≤ (980421482471/10000000000000 : ℝ)^845
        have hw : |(-168238493/1000000000 : ℝ)|=(168238493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2796579941/5000000000 : ℝ)|^1101 ≤ (46903778243597/100000000000000 : ℝ)^845
        have hw : |(2796579941/5000000000 : ℝ)|=(2796579941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_6 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1314887829/2500000000 : ℝ)*x 0 + (2796579921/5000000000 : ℝ)*x 1 + (-105149069/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314887829/2500000000 : ℝ)^1101 ≤ (541150075311/1250000000000 : ℝ)^845 := by
    have hnat : (1314887829 : ℕ)^1101*1250000000000^845 ≤ 541150075311^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314887829 2500000000 541150075311 1250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796579921/5000000000 : ℝ)^1101 ≤ (5862972225817/12500000000000 : ℝ)^845 := by
    have hnat : (2796579921 : ℕ)^1101*12500000000000^845 ≤ 5862972225817^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796579921 5000000000 5862972225817 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105149069/625000000 : ℝ)^1101 ≤ (4902108072953/50000000000000 : ℝ)^845 := by
    have hnat : (105149069 : ℕ)^1101*50000000000000^845 ≤ 4902108072953^845*625000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105149069 625000000 4902108072953 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314887829/2500000000 : ℝ), (2796579921/5000000000 : ℝ), (-105149069/625000000 : ℝ)] ![(541150075311/1250000000000 : ℝ), (5862972225817/12500000000000 : ℝ), (4902108072953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314887829/2500000000 : ℝ)|^1101 ≤ (541150075311/1250000000000 : ℝ)^845
        have hw : |(1314887829/2500000000 : ℝ)|=(1314887829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796579921/5000000000 : ℝ)|^1101 ≤ (5862972225817/12500000000000 : ℝ)^845
        have hw : |(2796579921/5000000000 : ℝ)|=(2796579921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105149069/625000000 : ℝ)|^1101 ≤ (4902108072953/50000000000000 : ℝ)^845
        have hw : |(-105149069/625000000 : ℝ)|=(105149069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s1_7 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (16698169/39062500 : ℝ)*x 0 + (4858408743/10000000000 : ℝ)*x 1 + (375576747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16698169/39062500 : ℝ)^1101 ≤ (8260940338781/25000000000000 : ℝ)^845 := by
    have hnat : (16698169 : ℕ)^1101*25000000000000^845 ≤ 8260940338781^845*39062500^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16698169 39062500 8260940338781 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4858408743/10000000000 : ℝ)^1101 ≤ (305003457497/781250000000 : ℝ)^845 := by
    have hnat : (4858408743 : ℕ)^1101*781250000000^845 ≤ 305003457497^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858408743 10000000000 305003457497 781250000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375576747/1000000000 : ℝ)^1101 ≤ (3489474508079/12500000000000 : ℝ)^845 := by
    have hnat : (375576747 : ℕ)^1101*12500000000000^845 ≤ 3489474508079^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375576747 1000000000 3489474508079 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16698169/39062500 : ℝ), (4858408743/10000000000 : ℝ), (375576747/1000000000 : ℝ)] ![(8260940338781/25000000000000 : ℝ), (305003457497/781250000000 : ℝ), (3489474508079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16698169/39062500 : ℝ)|^1101 ≤ (8260940338781/25000000000000 : ℝ)^845
        have hw : |(16698169/39062500 : ℝ)|=(16698169/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4858408743/10000000000 : ℝ)|^1101 ≤ (305003457497/781250000000 : ℝ)^845
        have hw : |(4858408743/10000000000 : ℝ)|=(4858408743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375576747/1000000000 : ℝ)|^1101 ≤ (3489474508079/12500000000000 : ℝ)^845
        have hw : |(375576747/1000000000 : ℝ)|=(375576747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1444_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5231/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3887/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5231/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5231/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5231/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5231/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5231/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5231/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2153/100000 : ℝ) ^ (4403/1024 : ℝ) ≤ (6798528235307/100000000000000000000 : ℝ) := by
    have hpowers : (2153/100000 : ℝ)^4403 ≤ (6798528235307/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2153 : ℕ)^4403*100000000000000000000^1024 ≤ 6798528235307^1024*100000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2153 100000 6798528235307 100000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2153/100000 : ℝ)) (X := (6798528235307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5231/20000 : ℝ) ^ (4403/1024 : ℝ) ≤ (313039451263962761/100000000000000000000 : ℝ) := by
    have hpowers : (5231/20000 : ℝ)^4403 ≤ (313039451263962761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5231 : ℕ)^4403*100000000000000000000^1024 ≤ 313039451263962761^1024*20000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5231 20000 313039451263962761 100000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5231/20000 : ℝ)) (X := (313039451263962761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000006798528235307/50000000000000000000 : ℝ) ≤ (10000000316224963/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (50000006798528235307/50000000000000000000 : ℝ)^1024 ≤ (10000000316224963/10000000000000000 : ℝ)^4403 := by
      have hnat : (50000006798528235307 : ℕ)^1024*10000000000000000^4403 ≤ 10000000316224963^4403*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000006798528235307 50000000000000000000 10000000316224963 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000316224963/10000000000000000 : ℝ)) (X := (50000006798528235307/50000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25078261562448049517/25000000000000000000 : ℝ) ≤ (2001454349353271/2000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (25078261562448049517/25000000000000000000 : ℝ)^1024 ≤ (2001454349353271/2000000000000000 : ℝ)^4403 := by
      have hnat : (25078261562448049517 : ℕ)^1024*2000000000000000^4403 ≤ 2001454349353271^4403*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25078261562448049517 25000000000000000000 2001454349353271 2000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001454349353271/2000000000000000 : ℝ)) (X := (25078261562448049517/25000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50313039451263962761/50000000000000000000 : ℝ) ≤ (10014543177307747/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (50313039451263962761/50000000000000000000 : ℝ)^1024 ≤ (10014543177307747/10000000000000000 : ℝ)^4403 := by
      have hnat : (50313039451263962761 : ℕ)^1024*10000000000000000^4403 ≤ 10014543177307747^4403*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50313039451263962761 50000000000000000000 10014543177307747 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014543177307747/10000000000000000 : ℝ)) (X := (50313039451263962761/50000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6798528235307/100000000000000000000 : ℝ) ≤ ((119994348405060163987/120010000000000000000 : ℝ)+2*(454464408837/150012500000000 : ℝ)*(2153/100000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (119994348405060163987/120010000000000000000 : ℝ)+2*(454464408837/150012500000000 : ℝ)*(2153/100000 : ℝ)=(10000000316224963/10000000000000000 : ℝ) by norm_num, show 1+2*(6798528235307/100000000000000000000 : ℝ)=(50000006798528235307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(313039451263962761/100000000000000000000 : ℝ)+(6798528235307/100000000000000000000 : ℝ) ≤ ((119994348405060163987/120010000000000000000 : ℝ)+(454464408837/150012500000000 : ℝ)*((5231/20000 : ℝ)+(2153/100000 : ℝ)))^(4403/1024 : ℝ) := by
    rw [show (119994348405060163987/120010000000000000000 : ℝ)+(454464408837/150012500000000 : ℝ)*((5231/20000 : ℝ)+(2153/100000 : ℝ))=(2001454349353271/2000000000000000 : ℝ) by norm_num, show 1+(313039451263962761/100000000000000000000 : ℝ)+(6798528235307/100000000000000000000 : ℝ)=(25078261562448049517/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(313039451263962761/100000000000000000000 : ℝ) ≤ ((119994348405060163987/120010000000000000000 : ℝ)+2*(454464408837/150012500000000 : ℝ)*(5231/20000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (119994348405060163987/120010000000000000000 : ℝ)+2*(454464408837/150012500000000 : ℝ)*(5231/20000 : ℝ)=(10014543177307747/10000000000000000 : ℝ) by norm_num, show 1+2*(313039451263962761/100000000000000000000 : ℝ)=(50313039451263962761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119994348405060163987/120010000000000000000 : ℝ)*(X 1 0+X 2 0)+(454464408837/150012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (2153/100000 : ℝ)) (hi := (5231/20000 : ℝ)) (c := (119994348405060163987/120010000000000000000 : ℝ)) (alpha := (454464408837/150012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119994348405060163987/120010000000000000000 : ℝ)*(X 0 1+X 2 1)+(454464408837/150012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (2153/100000 : ℝ)) (hi := (5231/20000 : ℝ)) (c := (119994348405060163987/120010000000000000000 : ℝ)) (alpha := (454464408837/150012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119994348405060163987/120010000000000000000 : ℝ)*(X 0 2+X 1 2)+(454464408837/150012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (2153/100000 : ℝ)) (hi := (5231/20000 : ℝ)) (c := (119994348405060163987/120010000000000000000 : ℝ)) (alpha := (454464408837/150012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-960292987/5000000000 : ℝ)*X 0 0+(111985517/200000000 : ℝ)*X 0 1+(5080236801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395311039/10000000000 : ℝ)*X 1 0+(-1097653501/5000000000 : ℝ)*X 1 1+(5080238329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395312271/10000000000 : ℝ)*X 2 0+(1270059237/2500000000 : ℝ)*X 2 1+(-1097653583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854781661/2000000000 : ℝ)*X 0 0+(3742466197/10000000000 : ℝ)*X 0 1+(1217872951/2500000000 : ℝ)*X 0 2+(854781661/2000000000 : ℝ)*X 1 0+(3742466197/10000000000 : ℝ)*X 1 1+(1217872951/2500000000 : ℝ)*X 1 2+(854781661/2000000000 : ℝ)*X 2 0+(3742466197/10000000000 : ℝ)*X 2 1+(1217872951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1920964081/10000000000 : ℝ)*X 0 0+(2543125999/5000000000 : ℝ)*X 0 1+(349572491/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259551399/10000000000 : ℝ)*X 1 0+(-168238493/1000000000 : ℝ)*X 1 1+(2796579941/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314887829/2500000000 : ℝ)*X 2 0+(2796579921/5000000000 : ℝ)*X 2 1+(-105149069/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16698169/39062500 : ℝ)*X 0 0+(4858408743/10000000000 : ℝ)*X 0 1+(375576747/1000000000 : ℝ)*X 0 2+(16698169/39062500 : ℝ)*X 1 0+(4858408743/10000000000 : ℝ)*X 1 1+(375576747/1000000000 : ℝ)*X 1 2+(16698169/39062500 : ℝ)*X 2 0+(4858408743/10000000000 : ℝ)*X 2 1+(375576747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1556318421439356823455380097/375031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38981501/6250000000000 : ℝ)*(base19) + (100886759/10000000000000 : ℝ)*(base23) + (10148853/20000000000000 : ℝ)*(upper3) + (7389087/25000000000000 : ℝ)*(upper4) + (29224281/100000000000000 : ℝ)*(upper5) + (87886993320573/6250000000000 : ℝ)*(major0) + (87886993320573/6250000000000 : ℝ)*(major1) + (87886993320573/6250000000000 : ℝ)*(major2) + (963323368187479/50000000000000 : ℝ)*(sp0) + (77066273808271/4000000000000 : ℝ)*(sp1) + (1926656460043201/100000000000000 : ℝ)*(sp2) + (885722468033929/100000000000000 : ℝ)*(sp3) + (1341566979/12500000000000 : ℝ)*(sp4) + (1855492861/50000000000000 : ℝ)*(sp7) + (885726179019651/100000000000000 : ℝ)*(f.failure) + (1926657468910791/100000000000000 : ℝ)*(f.sum) + (301895638896417/60005000000000000000000000000 : ℝ)*base66 + (4757395195790667051/750062500000000000000000000000000 : ℝ)*base67 + (10943499128246229551/750062500000000000000000000000000 : ℝ)*base69 + (892945688964520449/750062500000000000000000000000000 : ℝ)*base72 + (1704252586383/60005000000000000000000000000 : ℝ)*base73 + (1421388616407167051/750062500000000000000000000000000 : ℝ)*base75 + (1994547230895104551/750062500000000000000000000000000 : ℝ)*base77 + (797293090328832949/750062500000000000000000000000000 : ℝ)*base80 + (130901683423239/30002500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (27372681/10000000000000000000000 : ℝ)*base90 + (27372681/10000000000000000000000 : ℝ)*base92 + (27372681/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56017291936136816898469630329/6000500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7555433/10000000000000 : ℝ)*(base1) + (1972726373/100000000000000 : ℝ)*(base19) + (965237097/50000000000000 : ℝ)*(base23) + (113905693/50000000000000 : ℝ)*(upper3) + (764317/390625000000 : ℝ)*(upper5) + (1439829130842111/100000000000000 : ℝ)*(major0) + (1439829130842111/100000000000000 : ℝ)*(major1) + (1439829130842111/100000000000000 : ℝ)*(major2) + (5891816923/50000000000000 : ℝ)*(sp1) + (567634491/5000000000000 : ℝ)*(sp2) + (394548913313829/20000000000000 : ℝ)*(sp4) + (394546146930919/20000000000000 : ℝ)*(sp5) + (1972731207850801/100000000000000 : ℝ)*(sp6) + (453456691966911/50000000000000 : ℝ)*(sp7) + (113364182436019/12500000000000 : ℝ)*(f.failure) + (986372245507407/50000000000000 : ℝ)*(f.sum) + (42728672647941/60005000000000000000000000000 : ℝ)*base65 + (59753032810465143443/12001000000000000000000000000000000 : ℝ)*base68 + (42375405135530856557/12001000000000000000000000000000000 : ℝ)*base69 + (39067306119583856557/12001000000000000000000000000000000 : ℝ)*base71 + (15393886996783/7500625000000000000000000000 : ℝ)*base74 + (93144459489526856557/12001000000000000000000000000000000 : ℝ)*base75 + (4718872744646856557/12001000000000000000000000000000000 : ℝ)*base77 + (62954912715557143443/12001000000000000000000000000000000 : ℝ)*base80 + (80292143714919/15001250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (12548089/1250000000000000000000 : ℝ)*base90 + (12548089/1250000000000000000000 : ℝ)*base92 + (12548089/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1444_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5231/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3887/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1444_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1444_s2_0 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-976306801/5000000000 : ℝ)*x 0 + (545487411/1000000000 : ℝ)*x 1 + (1040801213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976306801/5000000000 : ℝ)^1101 ≤ (11904260860219/100000000000000 : ℝ)^845 := by
    have hnat : (976306801 : ℕ)^1101*100000000000000^845 ≤ 11904260860219^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976306801 5000000000 11904260860219 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545487411/1000000000 : ℝ)^1101 ≤ (5674811255789/12500000000000 : ℝ)^845 := by
    have hnat : (545487411 : ℕ)^1101*12500000000000^845 ≤ 5674811255789^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545487411 1000000000 5674811255789 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040801213/2000000000 : ℝ)^1101 ≤ (42697249077221/100000000000000 : ℝ)^845 := by
    have hnat : (1040801213 : ℕ)^1101*100000000000000^845 ≤ 42697249077221^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040801213 2000000000 42697249077221 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-976306801/5000000000 : ℝ), (545487411/1000000000 : ℝ), (1040801213/2000000000 : ℝ)] ![(11904260860219/100000000000000 : ℝ), (5674811255789/12500000000000 : ℝ), (42697249077221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-976306801/5000000000 : ℝ)|^1101 ≤ (11904260860219/100000000000000 : ℝ)^845
        have hw : |(-976306801/5000000000 : ℝ)|=(976306801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545487411/1000000000 : ℝ)|^1101 ≤ (5674811255789/12500000000000 : ℝ)^845
        have hw : |(545487411/1000000000 : ℝ)|=(545487411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040801213/2000000000 : ℝ)|^1101 ≤ (42697249077221/100000000000000 : ℝ)^845
        have hw : |(1040801213/2000000000 : ℝ)|=(1040801213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_1 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1339800011/2500000000 : ℝ)*x 0 + (-104080029/500000000 : ℝ)*x 1 + (2602002907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339800011/2500000000 : ℝ)^1101 ≤ (44363773514421/100000000000000 : ℝ)^845 := by
    have hnat : (1339800011 : ℕ)^1101*100000000000000^845 ≤ 44363773514421^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339800011 2500000000 44363773514421 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104080029/500000000 : ℝ)^1101 ≤ (3234745022231/25000000000000 : ℝ)^845 := by
    have hnat : (104080029 : ℕ)^1101*25000000000000^845 ≤ 3234745022231^845*500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104080029 500000000 3234745022231 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602002907/5000000000 : ℝ)^1101 ≤ (21348623196969/50000000000000 : ℝ)^845 := by
    have hnat : (2602002907 : ℕ)^1101*50000000000000^845 ≤ 21348623196969^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602002907 5000000000 21348623196969 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339800011/2500000000 : ℝ), (-104080029/500000000 : ℝ), (2602002907/5000000000 : ℝ)] ![(44363773514421/100000000000000 : ℝ), (3234745022231/25000000000000 : ℝ), (21348623196969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339800011/2500000000 : ℝ)|^1101 ≤ (44363773514421/100000000000000 : ℝ)^845
        have hw : |(1339800011/2500000000 : ℝ)|=(1339800011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104080029/500000000 : ℝ)|^1101 ≤ (3234745022231/25000000000000 : ℝ)^845
        have hw : |(-104080029/500000000 : ℝ)|=(104080029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602002907/5000000000 : ℝ)|^1101 ≤ (21348623196969/50000000000000 : ℝ)^845
        have hw : |(2602002907/5000000000 : ℝ)|=(2602002907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_2 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5359199497/10000000000 : ℝ)*x 0 + (1040801271/2000000000 : ℝ)*x 1 + (-2081600593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359199497/10000000000 : ℝ)^1101 ≤ (44363767614497/100000000000000 : ℝ)^845 := by
    have hnat : (5359199497 : ℕ)^1101*100000000000000^845 ≤ 44363767614497^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359199497 10000000000 44363767614497 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040801271/2000000000 : ℝ)^1101 ≤ (10674313044357/25000000000000 : ℝ)^845 := by
    have hnat : (1040801271 : ℕ)^1101*25000000000000^845 ≤ 10674313044357^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040801271 2000000000 10674313044357 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081600593/10000000000 : ℝ)^1101 ≤ (12938980194211/100000000000000 : ℝ)^845 := by
    have hnat : (2081600593 : ℕ)^1101*100000000000000^845 ≤ 12938980194211^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081600593 10000000000 12938980194211 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359199497/10000000000 : ℝ), (1040801271/2000000000 : ℝ), (-2081600593/10000000000 : ℝ)] ![(44363767614497/100000000000000 : ℝ), (10674313044357/25000000000000 : ℝ), (12938980194211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359199497/10000000000 : ℝ)|^1101 ≤ (44363767614497/100000000000000 : ℝ)^845
        have hw : |(5359199497/10000000000 : ℝ)|=(5359199497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040801271/2000000000 : ℝ)|^1101 ≤ (10674313044357/25000000000000 : ℝ)^845
        have hw : |(1040801271/2000000000 : ℝ)|=(1040801271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081600593/10000000000 : ℝ)|^1101 ≤ (12938980194211/100000000000000 : ℝ)^845
        have hw : |(-2081600593/10000000000 : ℝ)|=(2081600593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_3 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2148276539/5000000000 : ℝ)*x 0 + (1007857991/2500000000 : ℝ)*x 1 + (2288564313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148276539/5000000000 : ℝ)^1101 ≤ (6652743634021/20000000000000 : ℝ)^845 := by
    have hnat : (2148276539 : ℕ)^1101*20000000000000^845 ≤ 6652743634021^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148276539 5000000000 6652743634021 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007857991/2500000000 : ℝ)^1101 ≤ (30614689229851/100000000000000 : ℝ)^845 := by
    have hnat : (1007857991 : ℕ)^1101*100000000000000^845 ≤ 30614689229851^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007857991 2500000000 30614689229851 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288564313/5000000000 : ℝ)^1101 ≤ (36121592579763/100000000000000 : ℝ)^845 := by
    have hnat : (2288564313 : ℕ)^1101*100000000000000^845 ≤ 36121592579763^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288564313 5000000000 36121592579763 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148276539/5000000000 : ℝ), (1007857991/2500000000 : ℝ), (2288564313/5000000000 : ℝ)] ![(6652743634021/20000000000000 : ℝ), (30614689229851/100000000000000 : ℝ), (36121592579763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148276539/5000000000 : ℝ)|^1101 ≤ (6652743634021/20000000000000 : ℝ)^845
        have hw : |(2148276539/5000000000 : ℝ)|=(2148276539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007857991/2500000000 : ℝ)|^1101 ≤ (30614689229851/100000000000000 : ℝ)^845
        have hw : |(1007857991/2500000000 : ℝ)|=(1007857991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2288564313/5000000000 : ℝ)|^1101 ≤ (36121592579763/100000000000000 : ℝ)^845
        have hw : |(2288564313/5000000000 : ℝ)|=(2288564313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_4 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-48816403/250000000 : ℝ)*x 0 + (2602710281/5000000000 : ℝ)*x 1 + (2726724193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48816403/250000000 : ℝ)^1101 ≤ (5952299303413/50000000000000 : ℝ)^845 := by
    have hnat : (48816403 : ℕ)^1101*50000000000000^845 ≤ 5952299303413^845*250000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48816403 250000000 5952299303413 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602710281/5000000000 : ℝ)^1101 ≤ (2669523199699/6250000000000 : ℝ)^845 := by
    have hnat : (2602710281 : ℕ)^1101*6250000000000^845 ≤ 2669523199699^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602710281 5000000000 2669523199699 6250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726724193/5000000000 : ℝ)^1101 ≤ (22691515093261/50000000000000 : ℝ)^845 := by
    have hnat : (2726724193 : ℕ)^1101*50000000000000^845 ≤ 22691515093261^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726724193 5000000000 22691515093261 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48816403/250000000 : ℝ), (2602710281/5000000000 : ℝ), (2726724193/5000000000 : ℝ)] ![(5952299303413/50000000000000 : ℝ), (2669523199699/6250000000000 : ℝ), (22691515093261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48816403/250000000 : ℝ)|^1101 ≤ (5952299303413/50000000000000 : ℝ)^845
        have hw : |(-48816403/250000000 : ℝ)|=(48816403/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602710281/5000000000 : ℝ)|^1101 ≤ (2669523199699/6250000000000 : ℝ)^845
        have hw : |(2602710281/5000000000 : ℝ)|=(2602710281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726724193/5000000000 : ℝ)|^1101 ≤ (22691515093261/50000000000000 : ℝ)^845
        have hw : |(2726724193/5000000000 : ℝ)|=(2726724193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_5 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5293874793/10000000000 : ℝ)*x 0 + (-366431381/2000000000 : ℝ)*x 1 + (5453449489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293874793/10000000000 : ℝ)^1101 ≤ (10915120538379/25000000000000 : ℝ)^845 := by
    have hnat : (5293874793 : ℕ)^1101*25000000000000^845 ≤ 10915120538379^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293874793 10000000000 10915120538379 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366431381/2000000000 : ℝ)^1101 ≤ (21399366557/195312500000 : ℝ)^845 := by
    have hnat : (366431381 : ℕ)^1101*195312500000^845 ≤ 21399366557^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366431381 2000000000 21399366557 195312500000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453449489/10000000000 : ℝ)^1101 ≤ (22691521073223/50000000000000 : ℝ)^845 := by
    have hnat : (5453449489 : ℕ)^1101*50000000000000^845 ≤ 22691521073223^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453449489 10000000000 22691521073223 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293874793/10000000000 : ℝ), (-366431381/2000000000 : ℝ), (5453449489/10000000000 : ℝ)] ![(10915120538379/25000000000000 : ℝ), (21399366557/195312500000 : ℝ), (22691521073223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293874793/10000000000 : ℝ)|^1101 ≤ (10915120538379/25000000000000 : ℝ)^845
        have hw : |(5293874793/10000000000 : ℝ)|=(5293874793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366431381/2000000000 : ℝ)|^1101 ≤ (21399366557/195312500000 : ℝ)^845
        have hw : |(-366431381/2000000000 : ℝ)|=(366431381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453449489/10000000000 : ℝ)|^1101 ≤ (22691521073223/50000000000000 : ℝ)^845
        have hw : |(5453449489/10000000000 : ℝ)|=(5453449489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_6 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (330867131/625000000 : ℝ)*x 0 + (5453449301/10000000000 : ℝ)*x 1 + (-1832158129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330867131/625000000 : ℝ)^1101 ≤ (21830237331789/50000000000000 : ℝ)^845 := by
    have hnat : (330867131 : ℕ)^1101*50000000000000^845 ≤ 21830237331789^845*625000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330867131 625000000 21830237331789 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453449301/10000000000 : ℝ)^1101 ≤ (22691520053973/50000000000000 : ℝ)^845 := by
    have hnat : (5453449301 : ℕ)^1101*50000000000000^845 ≤ 22691520053973^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453449301 10000000000 22691520053973 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1832158129/10000000000 : ℝ)^1101 ≤ (10956485214371/100000000000000 : ℝ)^845 := by
    have hnat : (1832158129 : ℕ)^1101*100000000000000^845 ≤ 10956485214371^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832158129 10000000000 10956485214371 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330867131/625000000 : ℝ), (5453449301/10000000000 : ℝ), (-1832158129/10000000000 : ℝ)] ![(21830237331789/50000000000000 : ℝ), (22691520053973/50000000000000 : ℝ), (10956485214371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330867131/625000000 : ℝ)|^1101 ≤ (21830237331789/50000000000000 : ℝ)^845
        have hw : |(330867131/625000000 : ℝ)|=(330867131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453449301/10000000000 : ℝ)|^1101 ≤ (22691520053973/50000000000000 : ℝ)^845
        have hw : |(5453449301/10000000000 : ℝ)|=(5453449301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1832158129/10000000000 : ℝ)|^1101 ≤ (10956485214371/100000000000000 : ℝ)^845
        have hw : |(-1832158129/10000000000 : ℝ)|=(1832158129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s2_7 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (429664609/1000000000 : ℝ)*x 0 + (4574053279/10000000000 : ℝ)*x 1 + (806906477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429664609/1000000000 : ℝ)^1101 ≤ (6652931285341/20000000000000 : ℝ)^845 := by
    have hnat : (429664609 : ℕ)^1101*20000000000000^845 ≤ 6652931285341^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429664609 1000000000 6652931285341 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574053279/10000000000 : ℝ)^1101 ≤ (1443598925231/4000000000000 : ℝ)^845 := by
    have hnat : (4574053279 : ℕ)^1101*4000000000000^845 ≤ 1443598925231^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574053279 10000000000 1443598925231 4000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806906477/2000000000 : ℝ)^1101 ≤ (7661342608179/25000000000000 : ℝ)^845 := by
    have hnat : (806906477 : ℕ)^1101*25000000000000^845 ≤ 7661342608179^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806906477 2000000000 7661342608179 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429664609/1000000000 : ℝ), (4574053279/10000000000 : ℝ), (806906477/2000000000 : ℝ)] ![(6652931285341/20000000000000 : ℝ), (1443598925231/4000000000000 : ℝ), (7661342608179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429664609/1000000000 : ℝ)|^1101 ≤ (6652931285341/20000000000000 : ℝ)^845
        have hw : |(429664609/1000000000 : ℝ)|=(429664609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574053279/10000000000 : ℝ)|^1101 ≤ (1443598925231/4000000000000 : ℝ)^845
        have hw : |(4574053279/10000000000 : ℝ)|=(4574053279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806906477/2000000000 : ℝ)|^1101 ≤ (7661342608179/25000000000000 : ℝ)^845
        have hw : |(806906477/2000000000 : ℝ)|=(806906477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1444_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3887/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5223/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3151/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3887/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3887/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3887/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3887/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3887/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3887/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3887/50000 : ℝ) ^ (4403/1024 : ℝ) ≤ (42454935531147/2500000000000000000 : ℝ) := by
    have hpowers : (3887/50000 : ℝ)^4403 ≤ (42454935531147/2500000000000000000 : ℝ)^1024 := by
      have hnat : (3887 : ℕ)^4403*2500000000000000000^1024 ≤ 42454935531147^1024*50000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3887 50000 42454935531147 2500000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3887/50000 : ℝ)) (X := (42454935531147/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4687/25000 : ℝ) ^ (4403/1024 : ℝ) ≤ (18697703666142091/25000000000000000000 : ℝ) := by
    have hpowers : (4687/25000 : ℝ)^4403 ≤ (18697703666142091/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4687 : ℕ)^4403*25000000000000000000^1024 ≤ 18697703666142091^1024*25000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4687 25000 18697703666142091 25000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4687/25000 : ℝ)) (X := (18697703666142091/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250042454935531147/1250000000000000000 : ℝ) ≤ (10000078988484983/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (1250042454935531147/1250000000000000000 : ℝ)^1024 ≤ (10000078988484983/10000000000000000 : ℝ)^4403 := by
      have hnat : (1250042454935531147 : ℕ)^1024*10000000000000000^4403 ≤ 10000078988484983^4403*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250042454935531147 1250000000000000000 10000078988484983 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078988484983/10000000000000000 : ℝ)) (X := (1250042454935531147/1250000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25019122253021453561/25000000000000000000 : ℝ) ≤ (5000889186581783/5000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (25019122253021453561/25000000000000000000 : ℝ)^1024 ≤ (5000889186581783/5000000000000000 : ℝ)^4403 := by
      have hnat : (25019122253021453561 : ℕ)^1024*5000000000000000^4403 ≤ 5000889186581783^4403*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019122253021453561 25000000000000000000 5000889186581783 5000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000889186581783/5000000000000000 : ℝ)) (X := (25019122253021453561/25000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518697703666142091/12500000000000000000 : ℝ) ≤ (10003477757842149/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (12518697703666142091/12500000000000000000 : ℝ)^1024 ≤ (10003477757842149/10000000000000000 : ℝ)^4403 := by
      have hnat : (12518697703666142091 : ℕ)^1024*10000000000000000^4403 ≤ 10003477757842149^4403*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518697703666142091 12500000000000000000 10003477757842149 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003477757842149/10000000000000000 : ℝ)) (X := (12518697703666142091/12500000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(42454935531147/2500000000000000000 : ℝ) ≤ ((54857222393325797479/54870000000000000000 : ℝ)+2*(1699384678583/1097400000000000 : ℝ)*(3887/50000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (54857222393325797479/54870000000000000000 : ℝ)+2*(1699384678583/1097400000000000 : ℝ)*(3887/50000 : ℝ)=(10000078988484983/10000000000000000 : ℝ) by norm_num, show 1+2*(42454935531147/2500000000000000000 : ℝ)=(1250042454935531147/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18697703666142091/25000000000000000000 : ℝ)+(42454935531147/2500000000000000000 : ℝ) ≤ ((54857222393325797479/54870000000000000000 : ℝ)+(1699384678583/1097400000000000 : ℝ)*((4687/25000 : ℝ)+(3887/50000 : ℝ)))^(4403/1024 : ℝ) := by
    rw [show (54857222393325797479/54870000000000000000 : ℝ)+(1699384678583/1097400000000000 : ℝ)*((4687/25000 : ℝ)+(3887/50000 : ℝ))=(5000889186581783/5000000000000000 : ℝ) by norm_num, show 1+(18697703666142091/25000000000000000000 : ℝ)+(42454935531147/2500000000000000000 : ℝ)=(25019122253021453561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18697703666142091/25000000000000000000 : ℝ) ≤ ((54857222393325797479/54870000000000000000 : ℝ)+2*(1699384678583/1097400000000000 : ℝ)*(4687/25000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (54857222393325797479/54870000000000000000 : ℝ)+2*(1699384678583/1097400000000000 : ℝ)*(4687/25000 : ℝ)=(10003477757842149/10000000000000000 : ℝ) by norm_num, show 1+2*(18697703666142091/25000000000000000000 : ℝ)=(12518697703666142091/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54857222393325797479/54870000000000000000 : ℝ)*(X 1 0+X 2 0)+(1699384678583/1097400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (3887/50000 : ℝ)) (hi := (4687/25000 : ℝ)) (c := (54857222393325797479/54870000000000000000 : ℝ)) (alpha := (1699384678583/1097400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54857222393325797479/54870000000000000000 : ℝ)*(X 0 1+X 2 1)+(1699384678583/1097400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (3887/50000 : ℝ)) (hi := (4687/25000 : ℝ)) (c := (54857222393325797479/54870000000000000000 : ℝ)) (alpha := (1699384678583/1097400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54857222393325797479/54870000000000000000 : ℝ)*(X 0 2+X 1 2)+(1699384678583/1097400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (3887/50000 : ℝ)) (hi := (4687/25000 : ℝ)) (c := (54857222393325797479/54870000000000000000 : ℝ)) (alpha := (1699384678583/1097400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-976306801/5000000000 : ℝ)*X 0 0+(545487411/1000000000 : ℝ)*X 0 1+(1040801213/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339800011/2500000000 : ℝ)*X 1 0+(-104080029/500000000 : ℝ)*X 1 1+(2602002907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359199497/10000000000 : ℝ)*X 2 0+(1040801271/2000000000 : ℝ)*X 2 1+(-2081600593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148276539/5000000000 : ℝ)*X 0 0+(1007857991/2500000000 : ℝ)*X 0 1+(2288564313/5000000000 : ℝ)*X 0 2+(2148276539/5000000000 : ℝ)*X 1 0+(1007857991/2500000000 : ℝ)*X 1 1+(2288564313/5000000000 : ℝ)*X 1 2+(2148276539/5000000000 : ℝ)*X 2 0+(1007857991/2500000000 : ℝ)*X 2 1+(2288564313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-48816403/250000000 : ℝ)*X 0 0+(2602710281/5000000000 : ℝ)*X 0 1+(2726724193/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293874793/10000000000 : ℝ)*X 1 0+(-366431381/2000000000 : ℝ)*X 1 1+(5453449489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330867131/625000000 : ℝ)*X 2 0+(5453449301/10000000000 : ℝ)*X 2 1+(-1832158129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429664609/1000000000 : ℝ)*X 0 0+(4574053279/10000000000 : ℝ)*X 0 1+(806906477/2000000000 : ℝ)*X 0 2+(429664609/1000000000 : ℝ)*X 1 0+(4574053279/10000000000 : ℝ)*X 1 1+(806906477/2000000000 : ℝ)*X 1 2+(429664609/1000000000 : ℝ)*X 2 0+(4574053279/10000000000 : ℝ)*X 2 1+(806906477/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20484378900789151879463/2286250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4981173/400000000000 : ℝ)*(base19) + (586729571/100000000000000 : ℝ)*(base23) + (67446699/50000000000000 : ℝ)*(lower2) + (1608537/500000000000 : ℝ)*(upper3) + (4525613/12500000000000 : ℝ)*(upper5) + (727339331566573/25000000000000 : ℝ)*(major0) + (727339331566573/25000000000000 : ℝ)*(major1) + (727339331566573/25000000000000 : ℝ)*(major2) + (1993086839624673/50000000000000 : ℝ)*(sp0) + (996544867226093/25000000000000 : ℝ)*(sp1) + (996545031867013/25000000000000 : ℝ)*(sp2) + (1832525417810459/100000000000000 : ℝ)*(sp3) + (1758737069/25000000000000 : ℝ)*(sp4) + (2055465993/25000000000000 : ℝ)*(sp7) + (183253363967443/10000000000000 : ℝ)*(f.failure) + (1993090357098811/50000000000000 : ℝ)*(f.sum) + (1830484378417/6858750000000000000000000000 : ℝ)*base65 + (10971145130624019467/1371750000000000000000000000000000 : ℝ)*base67 + (1984756361792019467/1371750000000000000000000000000000 : ℝ)*base69 + (8590484239730480533/1371750000000000000000000000000000 : ℝ)*base72 + (18389708672939/13717500000000000000000000000 : ℝ)*base73 + (101747791916480533/1371750000000000000000000000000000 : ℝ)*base76 + (863922007566519467/1371750000000000000000000000000000 : ℝ)*base77 + (6094504831689980533/1371750000000000000000000000000000 : ℝ)*base80 + (7219079645303/6858750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1146233/1000000000000000000000 : ℝ)*base90 + (1146233/1000000000000000000000 : ℝ)*base92 + (1146233/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36980524775910227385052197/2950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36621777/4000000000000 : ℝ)*(base19) + (771656823/100000000000000 : ℝ)*(base23) + (88386041/25000000000000 : ℝ)*(upper3) + (128200027/50000000000000 : ℝ)*(lower4) + (294264527734911/10000000000000 : ℝ)*(major0) + (294264527734911/10000000000000 : ℝ)*(major1) + (294264527734911/10000000000000 : ℝ)*(major2) + (1017101523/5000000000000 : ℝ)*(sp1) + (12449694821/100000000000000 : ℝ)*(sp2) + (398809553/20000000000000 : ℝ)*(sp3) + (403178922387577/10000000000000 : ℝ)*(sp4) + (1007941991575221/25000000000000 : ℝ)*(sp5) + (2015888001262063/50000000000000 : ℝ)*(sp6) + (1853498918915639/100000000000000 : ℝ)*(sp7) + (463375228240851/25000000000000 : ℝ)*(f.failure) + (403178922387577/10000000000000 : ℝ)*(f.sum) + (366066040879/59000000000000000000000000 : ℝ)*base66 + (6470542590160867/5900000000000000000000000000000 : ℝ)*base68 + (47129942089760867/5900000000000000000000000000000 : ℝ)*base70 + (19456772701060867/5900000000000000000000000000000 : ℝ)*base72 + (126554094599/29500000000000000000000000 : ℝ)*base74 + (87864341516160867/5900000000000000000000000000000 : ℝ)*base76 + (44299241198960867/5900000000000000000000000000000 : ℝ)*base78 + (71213252372060867/5900000000000000000000000000000 : ℝ)*base80 + (369628520941/59000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (40570119/2500000000000000000000 : ℝ)*base89 + (40570119/2500000000000000000000 : ℝ)*base91 + (40570119/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1444_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3887/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5223/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3151/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1444_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1444_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5223/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3151/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1444_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1444_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1444_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5223/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3151/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1444_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
