-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:00:25.294318+00:00
-- url     : https://prove2.me/submissions/8a9dd14b-4dec-47b7-b799-aad93bbfdfdf

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
theorem support_rectangle_w1100_s3_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091420243/5000000000 : ℝ)*x 0 + (543366259/1000000000 : ℝ)*x 1 + (5227967197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091420243/5000000000 : ℝ)^8293 ≤ (3312831353379/25000000000000 : ℝ)^6245 := by
    have hnat : (1091420243 : ℕ)^8293*25000000000000^6245 ≤ 3312831353379^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091420243 5000000000 3312831353379 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543366259/1000000000 : ℝ)^8293 ≤ (44485485274603/100000000000000 : ℝ)^6245 := by
    have hnat : (543366259 : ℕ)^8293*100000000000000^6245 ≤ 44485485274603^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543366259 1000000000 44485485274603 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227967197/10000000000 : ℝ)^8293 ≤ (42263189298689/100000000000000 : ℝ)^6245 := by
    have hnat : (5227967197 : ℕ)^8293*100000000000000^6245 ≤ 42263189298689^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227967197 10000000000 42263189298689 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091420243/5000000000 : ℝ), (543366259/1000000000 : ℝ), (5227967197/10000000000 : ℝ)] ![(3312831353379/25000000000000 : ℝ), (44485485274603/100000000000000 : ℝ), (42263189298689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091420243/5000000000 : ℝ)|^8293 ≤ (3312831353379/25000000000000 : ℝ)^6245
        have hw : |(-1091420243/5000000000 : ℝ)|=(1091420243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543366259/1000000000 : ℝ)|^8293 ≤ (44485485274603/100000000000000 : ℝ)^6245
        have hw : |(543366259/1000000000 : ℝ)|=(543366259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227967197/10000000000 : ℝ)|^8293 ≤ (42263189298689/100000000000000 : ℝ)^6245
        have hw : |(5227967197/10000000000 : ℝ)|=(5227967197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677412327/5000000000 : ℝ)*x 0 + (-457617071/2000000000 : ℝ)*x 1 + (5227967369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677412327/5000000000 : ℝ)^8293 ≤ (43630414048399/100000000000000 : ℝ)^6245 := by
    have hnat : (2677412327 : ℕ)^8293*100000000000000^6245 ≤ 43630414048399^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677412327 5000000000 43630414048399 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457617071/2000000000 : ℝ)^8293 ≤ (1763299348131/12500000000000 : ℝ)^6245 := by
    have hnat : (457617071 : ℕ)^8293*12500000000000^6245 ≤ 1763299348131^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457617071 2000000000 1763299348131 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227967369/10000000000 : ℝ)^8293 ≤ (42263191145137/100000000000000 : ℝ)^6245 := by
    have hnat : (5227967369 : ℕ)^8293*100000000000000^6245 ≤ 42263191145137^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227967369 10000000000 42263191145137 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677412327/5000000000 : ℝ), (-457617071/2000000000 : ℝ), (5227967369/10000000000 : ℝ)] ![(43630414048399/100000000000000 : ℝ), (1763299348131/12500000000000 : ℝ), (42263191145137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677412327/5000000000 : ℝ)|^8293 ≤ (43630414048399/100000000000000 : ℝ)^6245
        have hw : |(2677412327/5000000000 : ℝ)|=(2677412327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-457617071/2000000000 : ℝ)|^8293 ≤ (1763299348131/12500000000000 : ℝ)^6245
        have hw : |(-457617071/2000000000 : ℝ)|=(457617071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227967369/10000000000 : ℝ)|^8293 ≤ (42263191145137/100000000000000 : ℝ)^6245
        have hw : |(5227967369/10000000000 : ℝ)|=(5227967369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677412401/5000000000 : ℝ)*x 0 + (1045593493/2000000000 : ℝ)*x 1 + (-1144042517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677412401/5000000000 : ℝ)^8293 ≤ (2726900978109/6250000000000 : ℝ)^6245 := by
    have hnat : (2677412401 : ℕ)^8293*6250000000000^6245 ≤ 2726900978109^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677412401 5000000000 2726900978109 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045593493/2000000000 : ℝ)^8293 ≤ (42263192175713/100000000000000 : ℝ)^6245 := by
    have hnat : (1045593493 : ℕ)^8293*100000000000000^6245 ≤ 42263192175713^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045593493 2000000000 42263192175713 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144042517/5000000000 : ℝ)^8293 ≤ (14106392157031/100000000000000 : ℝ)^6245 := by
    have hnat : (1144042517 : ℕ)^8293*100000000000000^6245 ≤ 14106392157031^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144042517 5000000000 14106392157031 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677412401/5000000000 : ℝ), (1045593493/2000000000 : ℝ), (-1144042517/5000000000 : ℝ)] ![(2726900978109/6250000000000 : ℝ), (42263192175713/100000000000000 : ℝ), (14106392157031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677412401/5000000000 : ℝ)|^8293 ≤ (2726900978109/6250000000000 : ℝ)^6245
        have hw : |(2677412401/5000000000 : ℝ)|=(2677412401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045593493/2000000000 : ℝ)|^8293 ≤ (42263192175713/100000000000000 : ℝ)^6245
        have hw : |(1045593493/2000000000 : ℝ)|=(1045593493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144042517/5000000000 : ℝ)|^8293 ≤ (14106392157031/100000000000000 : ℝ)^6245
        have hw : |(-1144042517/5000000000 : ℝ)|=(1144042517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368080613/10000000000 : ℝ)*x 0 + (4169882391/10000000000 : ℝ)*x 1 + (1143934613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368080613/10000000000 : ℝ)^8293 ≤ (33290990129181/100000000000000 : ℝ)^6245 := by
    have hnat : (4368080613 : ℕ)^8293*100000000000000^6245 ≤ 33290990129181^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368080613 10000000000 33290990129181 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169882391/10000000000 : ℝ)^8293 ≤ (31300142368309/100000000000000 : ℝ)^6245 := by
    have hnat : (4169882391 : ℕ)^8293*100000000000000^6245 ≤ 31300142368309^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169882391 10000000000 31300142368309 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143934613/2500000000 : ℝ)^8293 ≤ (8852216870927/25000000000000 : ℝ)^6245 := by
    have hnat : (1143934613 : ℕ)^8293*25000000000000^6245 ≤ 8852216870927^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143934613 2500000000 8852216870927 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368080613/10000000000 : ℝ), (4169882391/10000000000 : ℝ), (1143934613/2500000000 : ℝ)] ![(33290990129181/100000000000000 : ℝ), (31300142368309/100000000000000 : ℝ), (8852216870927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368080613/10000000000 : ℝ)|^8293 ≤ (33290990129181/100000000000000 : ℝ)^6245
        have hw : |(4368080613/10000000000 : ℝ)|=(4368080613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169882391/10000000000 : ℝ)|^8293 ≤ (31300142368309/100000000000000 : ℝ)^6245
        have hw : |(4169882391/10000000000 : ℝ)|=(4169882391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143934613/2500000000 : ℝ)|^8293 ≤ (8852216870927/25000000000000 : ℝ)^6245
        have hw : |(1143934613/2500000000 : ℝ)|=(1143934613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091430353/5000000000 : ℝ)*x 0 + (5228789771/10000000000 : ℝ)*x 1 + (2716417663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091430353/5000000000 : ℝ)^8293 ≤ (265029768351/2000000000000 : ℝ)^6245 := by
    have hnat : (1091430353 : ℕ)^8293*2000000000000^6245 ≤ 265029768351^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091430353 5000000000 265029768351 2000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228789771/10000000000 : ℝ)^8293 ≤ (42272019992323/100000000000000 : ℝ)^6245 := by
    have hnat : (5228789771 : ℕ)^8293*100000000000000^6245 ≤ 42272019992323^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228789771 10000000000 42272019992323 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716417663/5000000000 : ℝ)^8293 ≤ (44476491579269/100000000000000 : ℝ)^6245 := by
    have hnat : (2716417663 : ℕ)^8293*100000000000000^6245 ≤ 44476491579269^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716417663 5000000000 44476491579269 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091430353/5000000000 : ℝ), (5228789771/10000000000 : ℝ), (2716417663/5000000000 : ℝ)] ![(265029768351/2000000000000 : ℝ), (42272019992323/100000000000000 : ℝ), (44476491579269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091430353/5000000000 : ℝ)|^8293 ≤ (265029768351/2000000000000 : ℝ)^6245
        have hw : |(-1091430353/5000000000 : ℝ)|=(1091430353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228789771/10000000000 : ℝ)|^8293 ≤ (42272019992323/100000000000000 : ℝ)^6245
        have hw : |(5228789771/10000000000 : ℝ)|=(5228789771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716417663/5000000000 : ℝ)|^8293 ≤ (44476491579269/100000000000000 : ℝ)^6245
        have hw : |(2716417663/5000000000 : ℝ)|=(2716417663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651437597/5000000000 : ℝ)*x 0 + (-520804297/2500000000 : ℝ)*x 1 + (1358208891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651437597/5000000000 : ℝ)^8293 ≤ (4306922210931/10000000000000 : ℝ)^6245 := by
    have hnat : (2651437597 : ℕ)^8293*10000000000000^6245 ≤ 4306922210931^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651437597 5000000000 4306922210931 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520804297/2500000000 : ℝ)^8293 ≤ (6227141856621/50000000000000 : ℝ)^6245 := by
    have hnat : (520804297 : ℕ)^8293*50000000000000^6245 ≤ 6227141856621^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520804297 2500000000 6227141856621 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358208891/2500000000 : ℝ)^8293 ≤ (44476494166649/100000000000000 : ℝ)^6245 := by
    have hnat : (1358208891 : ℕ)^8293*100000000000000^6245 ≤ 44476494166649^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358208891 2500000000 44476494166649 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651437597/5000000000 : ℝ), (-520804297/2500000000 : ℝ), (1358208891/2500000000 : ℝ)] ![(4306922210931/10000000000000 : ℝ), (6227141856621/50000000000000 : ℝ), (44476494166649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651437597/5000000000 : ℝ)|^8293 ≤ (4306922210931/10000000000000 : ℝ)^6245
        have hw : |(2651437597/5000000000 : ℝ)|=(2651437597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520804297/2500000000 : ℝ)|^8293 ≤ (6227141856621/50000000000000 : ℝ)^6245
        have hw : |(-520804297/2500000000 : ℝ)|=(520804297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358208891/2500000000 : ℝ)|^8293 ≤ (44476494166649/100000000000000 : ℝ)^6245
        have hw : |(1358208891/2500000000 : ℝ)|=(1358208891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302875291/10000000000 : ℝ)*x 0 + (2716417673/5000000000 : ℝ)*x 1 + (-1041608677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302875291/10000000000 : ℝ)^8293 ≤ (43069223155491/100000000000000 : ℝ)^6245 := by
    have hnat : (5302875291 : ℕ)^8293*100000000000000^6245 ≤ 43069223155491^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302875291 10000000000 43069223155491 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716417673/5000000000 : ℝ)^8293 ≤ (5559561474587/12500000000000 : ℝ)^6245 := by
    have hnat : (2716417673 : ℕ)^8293*12500000000000^6245 ≤ 5559561474587^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716417673 5000000000 5559561474587 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041608677/5000000000 : ℝ)^8293 ≤ (12454285031109/100000000000000 : ℝ)^6245 := by
    have hnat : (1041608677 : ℕ)^8293*100000000000000^6245 ≤ 12454285031109^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041608677 5000000000 12454285031109 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302875291/10000000000 : ℝ), (2716417673/5000000000 : ℝ), (-1041608677/5000000000 : ℝ)] ![(43069223155491/100000000000000 : ℝ), (5559561474587/12500000000000 : ℝ), (12454285031109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302875291/10000000000 : ℝ)|^8293 ≤ (43069223155491/100000000000000 : ℝ)^6245
        have hw : |(5302875291/10000000000 : ℝ)|=(5302875291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716417673/5000000000 : ℝ)|^8293 ≤ (5559561474587/12500000000000 : ℝ)^6245
        have hw : |(2716417673/5000000000 : ℝ)|=(2716417673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041608677/5000000000 : ℝ)|^8293 ≤ (12454285031109/100000000000000 : ℝ)^6245
        have hw : |(-1041608677/5000000000 : ℝ)|=(1041608677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s3_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092030103/2500000000 : ℝ)*x 0 + (4574116453/10000000000 : ℝ)*x 1 + (521439243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092030103/2500000000 : ℝ)^8293 ≤ (33291392927917/100000000000000 : ℝ)^6245 := by
    have hnat : (1092030103 : ℕ)^8293*100000000000000^6245 ≤ 33291392927917^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092030103 2500000000 33291392927917 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574116453/10000000000 : ℝ)^8293 ≤ (17696100280849/50000000000000 : ℝ)^6245 := by
    have hnat : (4574116453 : ℕ)^8293*50000000000000^6245 ≤ 17696100280849^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574116453 10000000000 17696100280849 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521439243/1250000000 : ℝ)^8293 ≤ (15658203248001/50000000000000 : ℝ)^6245 := by
    have hnat : (521439243 : ℕ)^8293*50000000000000^6245 ≤ 15658203248001^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521439243 1250000000 15658203248001 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092030103/2500000000 : ℝ), (4574116453/10000000000 : ℝ), (521439243/1250000000 : ℝ)] ![(33291392927917/100000000000000 : ℝ), (17696100280849/50000000000000 : ℝ), (15658203248001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092030103/2500000000 : ℝ)|^8293 ≤ (33291392927917/100000000000000 : ℝ)^6245
        have hw : |(1092030103/2500000000 : ℝ)|=(1092030103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574116453/10000000000 : ℝ)|^8293 ≤ (17696100280849/50000000000000 : ℝ)^6245
        have hw : |(4574116453/10000000000 : ℝ)|=(4574116453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521439243/1250000000 : ℝ)|^8293 ≤ (15658203248001/50000000000000 : ℝ)^6245
        have hw : |(521439243/1250000000 : ℝ)|=(521439243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5253/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14859/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16631/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2219/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16631/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2219/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16631/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2219/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16631/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2219/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16631/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2219/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16631/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2219/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2219/25000 : ℝ) ^ (2073/512 : ℝ) ≤ (5514581972780129/100000000000000000000 : ℝ) := by
    have hpowers : (2219/25000 : ℝ)^2073 ≤ (5514581972780129/100000000000000000000 : ℝ)^512 := by
      have hnat : (2219 : ℕ)^2073*100000000000000000000^512 ≤ 5514581972780129^512*25000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2219 25000 5514581972780129 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2219/25000 : ℝ)) (X := (5514581972780129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16631/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (2803446999864673/4000000000000000000 : ℝ) := by
    have hpowers : (16631/100000 : ℝ)^2073 ≤ (2803446999864673/4000000000000000000 : ℝ)^512 := by
      have hnat : (16631 : ℕ)^2073*4000000000000000000^512 ≤ 2803446999864673^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16631 100000 2803446999864673 4000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16631/100000 : ℝ)) (X := (2803446999864673/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005514581972780129/50000000000000000000 : ℝ) ≤ (5000136196272621/5000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50005514581972780129/50000000000000000000 : ℝ)^512 ≤ (5000136196272621/5000000000000000 : ℝ)^2073 := by
      have hnat : (50005514581972780129 : ℕ)^512*5000000000000000^2073 ≤ 5000136196272621^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005514581972780129 50000000000000000000 5000136196272621 5000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136196272621/5000000000000000 : ℝ)) (X := (50005514581972780129/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50037800378484698477/50000000000000000000 : ℝ) ≤ (10001866694385359/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50037800378484698477/50000000000000000000 : ℝ)^512 ≤ (10001866694385359/10000000000000000 : ℝ)^2073 := by
      have hnat : (50037800378484698477 : ℕ)^512*10000000000000000^2073 ≤ 10001866694385359^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037800378484698477 50000000000000000000 10001866694385359 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001866694385359/10000000000000000 : ℝ)) (X := (50037800378484698477/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2002803446999864673/2000000000000000000 : ℝ) ≤ (2500865249056369/2500000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (2002803446999864673/2000000000000000000 : ℝ)^512 ≤ (2500865249056369/2500000000000000 : ℝ)^2073 := by
      have hnat : (2002803446999864673 : ℕ)^512*2500000000000000^2073 ≤ 2500865249056369^2073*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002803446999864673 2000000000000000000 2500865249056369 2500000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500865249056369/2500000000000000 : ℝ)) (X := (2002803446999864673/2000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5514581972780129/100000000000000000000 : ℝ) ≤ ((38761905178961297363/38775000000000000000 : ℝ)+2*(1594301840117/775500000000000 : ℝ)*(2219/25000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (38761905178961297363/38775000000000000000 : ℝ)+2*(1594301840117/775500000000000 : ℝ)*(2219/25000 : ℝ)=(5000136196272621/5000000000000000 : ℝ) by norm_num, show 1+2*(5514581972780129/100000000000000000000 : ℝ)=(50005514581972780129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2803446999864673/4000000000000000000 : ℝ)+(5514581972780129/100000000000000000000 : ℝ) ≤ ((38761905178961297363/38775000000000000000 : ℝ)+(1594301840117/775500000000000 : ℝ)*((16631/100000 : ℝ)+(2219/25000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (38761905178961297363/38775000000000000000 : ℝ)+(1594301840117/775500000000000 : ℝ)*((16631/100000 : ℝ)+(2219/25000 : ℝ))=(10001866694385359/10000000000000000 : ℝ) by norm_num, show 1+(2803446999864673/4000000000000000000 : ℝ)+(5514581972780129/100000000000000000000 : ℝ)=(50037800378484698477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2803446999864673/4000000000000000000 : ℝ) ≤ ((38761905178961297363/38775000000000000000 : ℝ)+2*(1594301840117/775500000000000 : ℝ)*(16631/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (38761905178961297363/38775000000000000000 : ℝ)+2*(1594301840117/775500000000000 : ℝ)*(16631/100000 : ℝ)=(2500865249056369/2500000000000000 : ℝ) by norm_num, show 1+2*(2803446999864673/4000000000000000000 : ℝ)=(2002803446999864673/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38761905178961297363/38775000000000000000 : ℝ)*(X 1 0+X 2 0)+(1594301840117/775500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (2219/25000 : ℝ)) (hi := (16631/100000 : ℝ)) (c := (38761905178961297363/38775000000000000000 : ℝ)) (alpha := (1594301840117/775500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38761905178961297363/38775000000000000000 : ℝ)*(X 0 1+X 2 1)+(1594301840117/775500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (2219/25000 : ℝ)) (hi := (16631/100000 : ℝ)) (c := (38761905178961297363/38775000000000000000 : ℝ)) (alpha := (1594301840117/775500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38761905178961297363/38775000000000000000 : ℝ)*(X 0 2+X 1 2)+(1594301840117/775500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (2219/25000 : ℝ)) (hi := (16631/100000 : ℝ)) (c := (38761905178961297363/38775000000000000000 : ℝ)) (alpha := (1594301840117/775500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091420243/5000000000 : ℝ)*X 0 0+(543366259/1000000000 : ℝ)*X 0 1+(5227967197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677412327/5000000000 : ℝ)*X 1 0+(-457617071/2000000000 : ℝ)*X 1 1+(5227967369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677412401/5000000000 : ℝ)*X 2 0+(1045593493/2000000000 : ℝ)*X 2 1+(-1144042517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368080613/10000000000 : ℝ)*X 0 0+(4169882391/10000000000 : ℝ)*X 0 1+(1143934613/2500000000 : ℝ)*X 0 2+(4368080613/10000000000 : ℝ)*X 1 0+(4169882391/10000000000 : ℝ)*X 1 1+(1143934613/2500000000 : ℝ)*X 1 2+(4368080613/10000000000 : ℝ)*X 2 0+(4169882391/10000000000 : ℝ)*X 2 1+(1143934613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1091430353/5000000000 : ℝ)*X 0 0+(5228789771/10000000000 : ℝ)*X 0 1+(2716417663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651437597/5000000000 : ℝ)*X 1 0+(-520804297/2500000000 : ℝ)*X 1 1+(1358208891/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302875291/10000000000 : ℝ)*X 2 0+(2716417673/5000000000 : ℝ)*X 2 1+(-1041608677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092030103/2500000000 : ℝ)*X 0 0+(4574116453/10000000000 : ℝ)*X 0 1+(521439243/1250000000 : ℝ)*X 0 2+(1092030103/2500000000 : ℝ)*X 1 0+(4574116453/10000000000 : ℝ)*X 1 1+(521439243/1250000000 : ℝ)*X 1 2+(1092030103/2500000000 : ℝ)*X 2 0+(4574116453/10000000000 : ℝ)*X 2 1+(521439243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2497205344546827098928816867/323125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3231243/156250000000 : ℝ)*(base19) + (1932862543/100000000000000 : ℝ)*(base23) + (18039201/12500000000000 : ℝ)*(lower2) + (24909733/20000000000000 : ℝ)*(upper3) + (134324003/50000000000000 : ℝ)*(upper5) + (1831401427288791/50000000000000 : ℝ)*(major0) + (1831401427288791/50000000000000 : ℝ)*(major1) + (1831401427288791/50000000000000 : ℝ)*(major2) + (486159552510077/10000000000000 : ℝ)*(sp0) + (972327925905569/20000000000000 : ℝ)*(sp1) + (4861639764660821/100000000000000 : ℝ)*(sp2) + (307993237528721/12500000000000 : ℝ)*(sp3) + (9234484519/20000000000000 : ℝ)*(sp4) + (17853792187/100000000000000 : ℝ)*(sp7) + (1231981877010977/50000000000000 : ℝ)*(f.failure) + (972328339504673/20000000000000 : ℝ)*(f.sum) + (1199852051843/201953125000000000000000000 : ℝ)*base66 + (5198380090783297289/646250000000000000000000000000000 : ℝ)*base68 + (1039037962016702711/646250000000000000000000000000000 : ℝ)*base69 + (146037279580797289/646250000000000000000000000000000 : ℝ)*base72 + (62166120987251/6462500000000000000000000000 : ℝ)*base74 + (3791509032060452711/646250000000000000000000000000000 : ℝ)*base75 + (2036354261914202711/646250000000000000000000000000000 : ℝ)*base77 + (12900679186416702711/646250000000000000000000000000000 : ℝ)*base79 + (11946252908263/3231250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (151627/50000000000000000000 : ℝ)*base90 + (151627/50000000000000000000 : ℝ)*base92 + (151627/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (313422704419423483323855637/29375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15318679/781250000000 : ℝ)*(base19) + (1180155531/50000000000000 : ℝ)*(base23) + (56008971/20000000000000 : ℝ)*(upper3) + (28469183/20000000000000 : ℝ)*(lower4) + (5998017/4000000000000 : ℝ)*(upper5) + (1846175371813663/50000000000000 : ℝ)*(major0) + (1846175371813663/50000000000000 : ℝ)*(major1) + (1846175371813663/50000000000000 : ℝ)*(major2) + (35736199959/100000000000000 : ℝ)*(sp1) + (319731887/800000000000 : ℝ)*(sp2) + (306303783916981/6250000000000 : ℝ)*(sp4) + (2450411422840413/50000000000000 : ℝ)*(sp5) + (4900818215874759/100000000000000 : ℝ)*(sp6) + (124192029446299/5000000000000 : ℝ)*(sp7) + (124192029446299/5000000000000 : ℝ)*(f.failure) + (306303783916981/6250000000000 : ℝ)*(f.sum) + (1782703577161/1762500000000000000000000000 : ℝ)*base65 + (836953587931732707/58750000000000000000000000000000 : ℝ)*base68 + (303317201206732707/58750000000000000000000000000000 : ℝ)*base70 + (128208430179232707/58750000000000000000000000000000 : ℝ)*base72 + (10372741846753/3525000000000000000000000000 : ℝ)*base74 + (452994625497982707/58750000000000000000000000000000 : ℝ)*base76 + (288039696282982707/58750000000000000000000000000000 : ℝ)*base78 + (298243516720482707/58750000000000000000000000000000 : ℝ)*base80 + (8451516598411/1762500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (32151/5000000000000000000 : ℝ)*base89 + (32151/5000000000000000000 : ℝ)*base91 + (32151/5000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1100_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14859/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_s4_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-437239561/2000000000 : ℝ)*x 0 + (5403993827/10000000000 : ℝ)*x 1 + (1051088289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437239561/2000000000 : ℝ)^8293 ≤ (2655679461313/20000000000000 : ℝ)^6245 := by
    have hnat : (437239561 : ℕ)^8293*20000000000000^6245 ≤ 2655679461313^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437239561 2000000000 2655679461313 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403993827/10000000000 : ℝ)^8293 ≤ (44163219008359/100000000000000 : ℝ)^6245 := by
    have hnat : (5403993827 : ℕ)^8293*100000000000000^6245 ≤ 44163219008359^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403993827 10000000000 44163219008359 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051088289/2000000000 : ℝ)^8293 ≤ (42558383678601/100000000000000 : ℝ)^6245 := by
    have hnat : (1051088289 : ℕ)^8293*100000000000000^6245 ≤ 42558383678601^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051088289 2000000000 42558383678601 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437239561/2000000000 : ℝ), (5403993827/10000000000 : ℝ), (1051088289/2000000000 : ℝ)] ![(2655679461313/20000000000000 : ℝ), (44163219008359/100000000000000 : ℝ), (42558383678601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437239561/2000000000 : ℝ)|^8293 ≤ (2655679461313/20000000000000 : ℝ)^6245
        have hw : |(-437239561/2000000000 : ℝ)|=(437239561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403993827/10000000000 : ℝ)|^8293 ≤ (44163219008359/100000000000000 : ℝ)^6245
        have hw : |(5403993827/10000000000 : ℝ)|=(5403993827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051088289/2000000000 : ℝ)|^8293 ≤ (42558383678601/100000000000000 : ℝ)^6245
        have hw : |(1051088289/2000000000 : ℝ)|=(1051088289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347447759/10000000000 : ℝ)*x 0 + (-282715787/1250000000 : ℝ)*x 1 + (5255441329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347447759/10000000000 : ℝ)^8293 ≤ (21775307403679/50000000000000 : ℝ)^6245 := by
    have hnat : (5347447759 : ℕ)^8293*50000000000000^6245 ≤ 21775307403679^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347447759 10000000000 21775307403679 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282715787/1250000000 : ℝ)^8293 ≤ (13891002739523/100000000000000 : ℝ)^6245 := by
    have hnat : (282715787 : ℕ)^8293*100000000000000^6245 ≤ 13891002739523^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282715787 1250000000 13891002739523 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255441329/10000000000 : ℝ)^8293 ≤ (2127919121559/5000000000000 : ℝ)^6245 := by
    have hnat : (5255441329 : ℕ)^8293*5000000000000^6245 ≤ 2127919121559^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255441329 10000000000 2127919121559 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347447759/10000000000 : ℝ), (-282715787/1250000000 : ℝ), (5255441329/10000000000 : ℝ)] ![(21775307403679/50000000000000 : ℝ), (13891002739523/100000000000000 : ℝ), (2127919121559/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347447759/10000000000 : ℝ)|^8293 ≤ (21775307403679/50000000000000 : ℝ)^6245
        have hw : |(5347447759/10000000000 : ℝ)|=(5347447759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282715787/1250000000 : ℝ)|^8293 ≤ (13891002739523/100000000000000 : ℝ)^6245
        have hw : |(-282715787/1250000000 : ℝ)|=(282715787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255441329/10000000000 : ℝ)|^8293 ≤ (2127919121559/5000000000000 : ℝ)^6245
        have hw : |(5255441329/10000000000 : ℝ)|=(5255441329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336862051/2500000000 : ℝ)*x 0 + (656930149/1250000000 : ℝ)*x 1 + (-35339467/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336862051/2500000000 : ℝ)^8293 ≤ (21775309810019/50000000000000 : ℝ)^6245 := by
    have hnat : (1336862051 : ℕ)^8293*50000000000000^6245 ≤ 21775309810019^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336862051 2500000000 21775309810019 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656930149/1250000000 : ℝ)^8293 ≤ (42558380957933/100000000000000 : ℝ)^6245 := by
    have hnat : (656930149 : ℕ)^8293*100000000000000^6245 ≤ 42558380957933^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656930149 1250000000 42558380957933 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35339467/156250000 : ℝ)^8293 ≤ (13890999411909/100000000000000 : ℝ)^6245 := by
    have hnat : (35339467 : ℕ)^8293*100000000000000^6245 ≤ 13890999411909^6245*156250000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35339467 156250000 13890999411909 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336862051/2500000000 : ℝ), (656930149/1250000000 : ℝ), (-35339467/156250000 : ℝ)] ![(21775309810019/50000000000000 : ℝ), (42558380957933/100000000000000 : ℝ), (13890999411909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336862051/2500000000 : ℝ)|^8293 ≤ (21775309810019/50000000000000 : ℝ)^6245
        have hw : |(1336862051/2500000000 : ℝ)|=(1336862051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656930149/1250000000 : ℝ)|^8293 ≤ (42558380957933/100000000000000 : ℝ)^6245
        have hw : |(656930149/1250000000 : ℝ)|=(656930149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35339467/156250000 : ℝ)|^8293 ≤ (13890999411909/100000000000000 : ℝ)^6245
        have hw : |(-35339467/156250000 : ℝ)|=(35339467/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370080999/10000000000 : ℝ)*x 0 + (1056498781/2500000000 : ℝ)*x 1 + (2259551907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370080999/10000000000 : ℝ)^8293 ≤ (3331123717677/10000000000000 : ℝ)^6245 := by
    have hnat : (4370080999 : ℕ)^8293*10000000000000^6245 ≤ 3331123717677^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370080999 10000000000 3331123717677 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056498781/2500000000 : ℝ)^8293 ≤ (159303482143/500000000000 : ℝ)^6245 := by
    have hnat : (1056498781 : ℕ)^8293*500000000000^6245 ≤ 159303482143^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056498781 2500000000 159303482143 500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259551907/5000000000 : ℝ)^8293 ≤ (34828066371799/100000000000000 : ℝ)^6245 := by
    have hnat : (2259551907 : ℕ)^8293*100000000000000^6245 ≤ 34828066371799^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259551907 5000000000 34828066371799 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370080999/10000000000 : ℝ), (1056498781/2500000000 : ℝ), (2259551907/5000000000 : ℝ)] ![(3331123717677/10000000000000 : ℝ), (159303482143/500000000000 : ℝ), (34828066371799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370080999/10000000000 : ℝ)|^8293 ≤ (3331123717677/10000000000000 : ℝ)^6245
        have hw : |(4370080999/10000000000 : ℝ)|=(4370080999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056498781/2500000000 : ℝ)|^8293 ≤ (159303482143/500000000000 : ℝ)^6245
        have hw : |(1056498781/2500000000 : ℝ)|=(1056498781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259551907/5000000000 : ℝ)|^8293 ≤ (34828066371799/100000000000000 : ℝ)^6245
        have hw : |(2259551907/5000000000 : ℝ)|=(2259551907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109310319/500000000 : ℝ)*x 0 + (328491933/625000000 : ℝ)*x 1 + (5403561867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109310319/500000000 : ℝ)^8293 ≤ (1327846646893/10000000000000 : ℝ)^6245 := by
    have hnat : (109310319 : ℕ)^8293*10000000000000^6245 ≤ 1327846646893^6245*500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109310319 500000000 1327846646893 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328491933/625000000 : ℝ)^8293 ≤ (42563002242367/100000000000000 : ℝ)^6245 := by
    have hnat : (328491933 : ℕ)^8293*100000000000000^6245 ≤ 42563002242367^6245*625000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328491933 625000000 42563002242367 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403561867/10000000000 : ℝ)^8293 ≤ (2207926563729/5000000000000 : ℝ)^6245 := by
    have hnat : (5403561867 : ℕ)^8293*5000000000000^6245 ≤ 2207926563729^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403561867 10000000000 2207926563729 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109310319/500000000 : ℝ), (328491933/625000000 : ℝ), (5403561867/10000000000 : ℝ)] ![(1327846646893/10000000000000 : ℝ), (42563002242367/100000000000000 : ℝ), (2207926563729/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109310319/500000000 : ℝ)|^8293 ≤ (1327846646893/10000000000000 : ℝ)^6245
        have hw : |(-109310319/500000000 : ℝ)|=(109310319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328491933/625000000 : ℝ)|^8293 ≤ (42563002242367/100000000000000 : ℝ)^6245
        have hw : |(328491933/625000000 : ℝ)|=(328491933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403561867/10000000000 : ℝ)|^8293 ≤ (2207926563729/5000000000000 : ℝ)^6245
        have hw : |(5403561867/10000000000 : ℝ)|=(5403561867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (13274833/25000000 : ℝ)*x 0 + (-2113604959/10000000000 : ℝ)*x 1 + (5403561937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13274833/25000000 : ℝ)^8293 ≤ (43145361888069/100000000000000 : ℝ)^6245 := by
    have hnat : (13274833 : ℕ)^8293*100000000000000^6245 ≤ 43145361888069^6245*25000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13274833 25000000 43145361888069 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113604959/10000000000 : ℝ)^8293 ≤ (6348053029143/50000000000000 : ℝ)^6245 := by
    have hnat : (2113604959 : ℕ)^8293*50000000000000^6245 ≤ 6348053029143^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113604959 10000000000 6348053029143 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403561937/10000000000 : ℝ)^8293 ≤ (44158532034227/100000000000000 : ℝ)^6245 := by
    have hnat : (5403561937 : ℕ)^8293*100000000000000^6245 ≤ 44158532034227^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403561937 10000000000 44158532034227 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13274833/25000000 : ℝ), (-2113604959/10000000000 : ℝ), (5403561937/10000000000 : ℝ)] ![(43145361888069/100000000000000 : ℝ), (6348053029143/50000000000000 : ℝ), (44158532034227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13274833/25000000 : ℝ)|^8293 ≤ (43145361888069/100000000000000 : ℝ)^6245
        have hw : |(13274833/25000000 : ℝ)|=(13274833/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2113604959/10000000000 : ℝ)|^8293 ≤ (6348053029143/50000000000000 : ℝ)^6245
        have hw : |(-2113604959/10000000000 : ℝ)|=(2113604959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403561937/10000000000 : ℝ)|^8293 ≤ (44158532034227/100000000000000 : ℝ)^6245
        have hw : |(5403561937/10000000000 : ℝ)|=(5403561937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265496633/500000000 : ℝ)*x 0 + (5403562479/10000000000 : ℝ)*x 1 + (-2113604953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265496633/500000000 : ℝ)^8293 ≤ (43145356061431/100000000000000 : ℝ)^6245 := by
    have hnat : (265496633 : ℕ)^8293*100000000000000^6245 ≤ 43145356061431^6245*500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265496633 500000000 43145356061431 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403562479/10000000000 : ℝ)^8293 ≤ (8831707583213/20000000000000 : ℝ)^6245 := by
    have hnat : (5403562479 : ℕ)^8293*20000000000000^6245 ≤ 8831707583213^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403562479 10000000000 8831707583213 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113604953/10000000000 : ℝ)^8293 ≤ (6348053005213/50000000000000 : ℝ)^6245 := by
    have hnat : (2113604953 : ℕ)^8293*50000000000000^6245 ≤ 6348053005213^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113604953 10000000000 6348053005213 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265496633/500000000 : ℝ), (5403562479/10000000000 : ℝ), (-2113604953/10000000000 : ℝ)] ![(43145356061431/100000000000000 : ℝ), (8831707583213/20000000000000 : ℝ), (6348053005213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265496633/500000000 : ℝ)|^8293 ≤ (43145356061431/100000000000000 : ℝ)^6245
        have hw : |(265496633/500000000 : ℝ)|=(265496633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403562479/10000000000 : ℝ)|^8293 ≤ (8831707583213/20000000000000 : ℝ)^6245
        have hw : |(5403562479/10000000000 : ℝ)|=(5403562479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113604953/10000000000 : ℝ)|^8293 ≤ (6348053005213/50000000000000 : ℝ)^6245
        have hw : |(-2113604953/10000000000 : ℝ)|=(2113604953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s4_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370095693/10000000000 : ℝ)*x 0 + (4518256617/10000000000 : ℝ)*x 1 + (528355781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370095693/10000000000 : ℝ)^8293 ≤ (33311385914371/100000000000000 : ℝ)^6245 := by
    have hnat : (4370095693 : ℕ)^8293*100000000000000^6245 ≤ 33311385914371^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370095693 10000000000 33311385914371 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518256617/10000000000 : ℝ)^8293 ≤ (17409698103761/50000000000000 : ℝ)^6245 := by
    have hnat : (4518256617 : ℕ)^8293*50000000000000^6245 ≤ 17409698103761^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518256617 10000000000 17409698103761 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528355781/1250000000 : ℝ)^8293 ≤ (31869217862389/100000000000000 : ℝ)^6245 := by
    have hnat : (528355781 : ℕ)^8293*100000000000000^6245 ≤ 31869217862389^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528355781 1250000000 31869217862389 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370095693/10000000000 : ℝ), (4518256617/10000000000 : ℝ), (528355781/1250000000 : ℝ)] ![(33311385914371/100000000000000 : ℝ), (17409698103761/50000000000000 : ℝ), (31869217862389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370095693/10000000000 : ℝ)|^8293 ≤ (33311385914371/100000000000000 : ℝ)^6245
        have hw : |(4370095693/10000000000 : ℝ)|=(4370095693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518256617/10000000000 : ℝ)|^8293 ≤ (17409698103761/50000000000000 : ℝ)^6245
        have hw : |(4518256617/10000000000 : ℝ)|=(4518256617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528355781/1250000000 : ℝ)|^8293 ≤ (31869217862389/100000000000000 : ℝ)^6245
        have hw : |(528355781/1250000000 : ℝ)|=(528355781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11093/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5253/50000 : ℝ) ^ (2073/512 : ℝ) ≤ (10913604436754961/100000000000000000000 : ℝ) := by
    have hpowers : (5253/50000 : ℝ)^2073 ≤ (10913604436754961/100000000000000000000 : ℝ)^512 := by
      have hnat : (5253 : ℕ)^2073*100000000000000000000^512 ≤ 10913604436754961^512*50000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5253 50000 10913604436754961 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5253/50000 : ℝ)) (X := (10913604436754961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14859/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (2220742167239407/5000000000000000000 : ℝ) := by
    have hpowers : (14859/100000 : ℝ)^2073 ≤ (2220742167239407/5000000000000000000 : ℝ)^512 := by
      have hnat : (14859 : ℕ)^2073*5000000000000000000^512 ≤ 2220742167239407^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14859 100000 2220742167239407 5000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14859/100000 : ℝ)) (X := (2220742167239407/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010913604436754961/50000000000000000000 : ℝ) ≤ (625033690945017/625000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50010913604436754961/50000000000000000000 : ℝ)^512 ≤ (625033690945017/625000000000000 : ℝ)^2073 := by
      have hnat : (50010913604436754961 : ℕ)^512*625000000000000^2073 ≤ 625033690945017^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010913604436754961 50000000000000000000 625033690945017 625000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033690945017/625000000000000 : ℝ)) (X := (50010913604436754961/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055328447781543101/100000000000000000000 : ℝ) ≤ (10001366245343393/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (100055328447781543101/100000000000000000000 : ℝ)^512 ≤ (10001366245343393/10000000000000000 : ℝ)^2073 := by
      have hnat : (100055328447781543101 : ℕ)^512*10000000000000000^2073 ≤ 10001366245343393^2073*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055328447781543101 100000000000000000000 10001366245343393 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001366245343393/10000000000000000 : ℝ)) (X := (100055328447781543101/100000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502220742167239407/2500000000000000000 : ℝ) ≤ (5001096717783257/5000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (2502220742167239407/2500000000000000000 : ℝ)^512 ≤ (5001096717783257/5000000000000000 : ℝ)^2073 := by
      have hnat : (2502220742167239407 : ℕ)^512*5000000000000000^2073 ≤ 5001096717783257^2073*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502220742167239407 2500000000000000000 5001096717783257 5000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001096717783257/5000000000000000 : ℝ)) (X := (2502220742167239407/2500000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10913604436754961/100000000000000000000 : ℝ) ≤ ((3626247132164193797/3627500000000000000 : ℝ)+2*(827190223121/435300000000000 : ℝ)*(5253/50000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (3626247132164193797/3627500000000000000 : ℝ)+2*(827190223121/435300000000000 : ℝ)*(5253/50000 : ℝ)=(625033690945017/625000000000000 : ℝ) by norm_num, show 1+2*(10913604436754961/100000000000000000000 : ℝ)=(50010913604436754961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2220742167239407/5000000000000000000 : ℝ)+(10913604436754961/100000000000000000000 : ℝ) ≤ ((3626247132164193797/3627500000000000000 : ℝ)+(827190223121/435300000000000 : ℝ)*((14859/100000 : ℝ)+(5253/50000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (3626247132164193797/3627500000000000000 : ℝ)+(827190223121/435300000000000 : ℝ)*((14859/100000 : ℝ)+(5253/50000 : ℝ))=(10001366245343393/10000000000000000 : ℝ) by norm_num, show 1+(2220742167239407/5000000000000000000 : ℝ)+(10913604436754961/100000000000000000000 : ℝ)=(100055328447781543101/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2220742167239407/5000000000000000000 : ℝ) ≤ ((3626247132164193797/3627500000000000000 : ℝ)+2*(827190223121/435300000000000 : ℝ)*(14859/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (3626247132164193797/3627500000000000000 : ℝ)+2*(827190223121/435300000000000 : ℝ)*(14859/100000 : ℝ)=(5001096717783257/5000000000000000 : ℝ) by norm_num, show 1+2*(2220742167239407/5000000000000000000 : ℝ)=(2502220742167239407/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3626247132164193797/3627500000000000000 : ℝ)*(X 1 0+X 2 0)+(827190223121/435300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (14859/100000 : ℝ)) (c := (3626247132164193797/3627500000000000000 : ℝ)) (alpha := (827190223121/435300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3626247132164193797/3627500000000000000 : ℝ)*(X 0 1+X 2 1)+(827190223121/435300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (14859/100000 : ℝ)) (c := (3626247132164193797/3627500000000000000 : ℝ)) (alpha := (827190223121/435300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3626247132164193797/3627500000000000000 : ℝ)*(X 0 2+X 1 2)+(827190223121/435300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (14859/100000 : ℝ)) (c := (3626247132164193797/3627500000000000000 : ℝ)) (alpha := (827190223121/435300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437239561/2000000000 : ℝ)*X 0 0+(5403993827/10000000000 : ℝ)*X 0 1+(1051088289/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347447759/10000000000 : ℝ)*X 1 0+(-282715787/1250000000 : ℝ)*X 1 1+(5255441329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336862051/2500000000 : ℝ)*X 2 0+(656930149/1250000000 : ℝ)*X 2 1+(-35339467/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370080999/10000000000 : ℝ)*X 0 0+(1056498781/2500000000 : ℝ)*X 0 1+(2259551907/5000000000 : ℝ)*X 0 2+(4370080999/10000000000 : ℝ)*X 1 0+(1056498781/2500000000 : ℝ)*X 1 1+(2259551907/5000000000 : ℝ)*X 1 2+(4370080999/10000000000 : ℝ)*X 2 0+(1056498781/2500000000 : ℝ)*X 2 1+(2259551907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109310319/500000000 : ℝ)*X 0 0+(328491933/625000000 : ℝ)*X 0 1+(5403561867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13274833/25000000 : ℝ)*X 1 0+(-2113604959/10000000000 : ℝ)*X 1 1+(5403561937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265496633/500000000 : ℝ)*X 2 0+(5403562479/10000000000 : ℝ)*X 2 1+(-2113604953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370095693/10000000000 : ℝ)*X 0 0+(4518256617/10000000000 : ℝ)*X 0 1+(528355781/1250000000 : ℝ)*X 0 2+(4370095693/10000000000 : ℝ)*X 1 0+(4518256617/10000000000 : ℝ)*X 1 1+(528355781/1250000000 : ℝ)*X 1 2+(4370095693/10000000000 : ℝ)*X 2 0+(4518256617/10000000000 : ℝ)*X 2 1+(528355781/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (688369581937825534587999663/90687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5830427/12500000000000 : ℝ)*(base8) + (159395489/100000000000000 : ℝ)*(base21) + (447830901/100000000000000 : ℝ)*(lower2) + (51786413/100000000000000 : ℝ)*(lower4) + (5071659932056607/100000000000000 : ℝ)*(major0) + (5071659932056607/100000000000000 : ℝ)*(major1) + (5071659932056607/100000000000000 : ℝ)*(major2) + (6731616752773893/100000000000000 : ℝ)*(sp0) + (3365806591264659/50000000000000 : ℝ)*(sp1) + (134632379498379/2000000000000 : ℝ)*(sp2) + (3411698282079017/100000000000000 : ℝ)*(sp3) + (2334897131/100000000000000 : ℝ)*(sp4) + (5951785121/100000000000000 : ℝ)*(sp5) + (2194700831/100000000000000 : ℝ)*(sp7) + (426462559597481/12500000000000 : ℝ)*(f.failure) + (168290478357861/2500000000000 : ℝ)*(f.sum) + (150853372065191/10882500000000000000000000000 : ℝ)*base65 + (2849884933817475337/1088250000000000000000000000000000 : ℝ)*base67 + (7329694381611975337/1088250000000000000000000000000000 : ℝ)*base69 + (9889767094956975337/1088250000000000000000000000000000 : ℝ)*base71 + (25969301828573/21765000000000000000000000000 : ℝ)*base74 + (8217244923346725337/1088250000000000000000000000000000 : ℝ)*base75 + (12644943773453475337/1088250000000000000000000000000000 : ℝ)*base77 + (9228734932010774663/1088250000000000000000000000000000 : ℝ)*base80 + (122341224490057/21765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (91931/12500000000000000000 : ℝ)*base90 + (91931/12500000000000000000 : ℝ)*base92 + (91931/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236180968574169356023450599/90687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513513261/100000000000000 : ℝ)*(base19) + (53519609/12500000000000 : ℝ)*(base23) + (261115619/100000000000000 : ℝ)*(upper2) + (45196861/20000000000000 : ℝ)*(upper3) + (2550617534794963/50000000000000 : ℝ)*(major0) + (2550617534794963/50000000000000 : ℝ)*(major1) + (2550617534794963/50000000000000 : ℝ)*(major2) + (3878258863/100000000000000 : ℝ)*(sp1) + (2456882279/12500000000000 : ℝ)*(sp2) + (4737268831/100000000000000 : ℝ)*(sp3) + (6770874410657497/100000000000000 : ℝ)*(sp4) + (6770870018885373/100000000000000 : ℝ)*(sp5) + (6770854327442393/100000000000000 : ℝ)*(sp6) + (214474431527639/6250000000000 : ℝ)*(sp7) + (1715797820855527/50000000000000 : ℝ)*(f.failure) + (6770874410657497/100000000000000 : ℝ)*(f.sum) + (94252477175819/21765000000000000000000000000 : ℝ)*base66 + (1320987066763091467/544125000000000000000000000000000 : ℝ)*base68 + (8616691471163216467/544125000000000000000000000000000 : ℝ)*base70 + (6269685077656841467/544125000000000000000000000000000 : ℝ)*base72 + (88948293482159/21765000000000000000000000000 : ℝ)*base74 + (6817122926130341467/544125000000000000000000000000000 : ℝ)*base76 + (3127226676797216467/544125000000000000000000000000000 : ℝ)*base78 + (4919132017259966467/544125000000000000000000000000000 : ℝ)*base80 + (111493880929319/21765000000000000000000000000 : ℝ)*base82 + (193677/50000000000000000000 : ℝ)*base90 + (193677/50000000000000000000 : ℝ)*base92 + (193677/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1100_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_s5_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-437387473/2000000000 : ℝ)*x 0 + (1079207809/2000000000 : ℝ)*x 1 + (657863859/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437387473/2000000000 : ℝ)^8293 ≤ (13284362615349/100000000000000 : ℝ)^6245 := by
    have hnat : (437387473 : ℕ)^8293*100000000000000^6245 ≤ 13284362615349^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437387473 2000000000 13284362615349 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079207809/2000000000 : ℝ)^8293 ≤ (22038455756901/50000000000000 : ℝ)^6245 := by
    have hnat : (1079207809 : ℕ)^8293*50000000000000^6245 ≤ 22038455756901^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079207809 2000000000 22038455756901 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657863859/1250000000 : ℝ)^8293 ≤ (10659681464171/25000000000000 : ℝ)^6245 := by
    have hnat : (657863859 : ℕ)^8293*25000000000000^6245 ≤ 10659681464171^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657863859 1250000000 10659681464171 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437387473/2000000000 : ℝ), (1079207809/2000000000 : ℝ), (657863859/1250000000 : ℝ)] ![(13284362615349/100000000000000 : ℝ), (22038455756901/50000000000000 : ℝ), (10659681464171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437387473/2000000000 : ℝ)|^8293 ≤ (13284362615349/100000000000000 : ℝ)^6245
        have hw : |(-437387473/2000000000 : ℝ)|=(437387473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079207809/2000000000 : ℝ)|^8293 ≤ (22038455756901/50000000000000 : ℝ)^6245
        have hw : |(1079207809/2000000000 : ℝ)|=(1079207809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657863859/1250000000 : ℝ)|^8293 ≤ (10659681464171/25000000000000 : ℝ)^6245
        have hw : |(657863859/1250000000 : ℝ)|=(657863859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345460607/10000000000 : ℝ)*x 0 + (-70453327/312500000 : ℝ)*x 1 + (2631455429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345460607/10000000000 : ℝ)^8293 ≤ (43529125046389/100000000000000 : ℝ)^6245 := by
    have hnat : (5345460607 : ℕ)^8293*100000000000000^6245 ≤ 43529125046389^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345460607 10000000000 43529125046389 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70453327/312500000 : ℝ)^8293 ≤ (3458037309003/25000000000000 : ℝ)^6245 := by
    have hnat : (70453327 : ℕ)^8293*25000000000000^6245 ≤ 3458037309003^6245*312500000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70453327 312500000 3458037309003 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631455429/5000000000 : ℝ)^8293 ≤ (42638725706063/100000000000000 : ℝ)^6245 := by
    have hnat : (2631455429 : ℕ)^8293*100000000000000^6245 ≤ 42638725706063^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631455429 5000000000 42638725706063 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345460607/10000000000 : ℝ), (-70453327/312500000 : ℝ), (2631455429/5000000000 : ℝ)] ![(43529125046389/100000000000000 : ℝ), (3458037309003/25000000000000 : ℝ), (42638725706063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345460607/10000000000 : ℝ)|^8293 ≤ (43529125046389/100000000000000 : ℝ)^6245
        have hw : |(5345460607/10000000000 : ℝ)|=(5345460607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70453327/312500000 : ℝ)|^8293 ≤ (3458037309003/25000000000000 : ℝ)^6245
        have hw : |(-70453327/312500000 : ℝ)|=(70453327/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631455429/5000000000 : ℝ)|^8293 ≤ (42638725706063/100000000000000 : ℝ)^6245
        have hw : |(2631455429/5000000000 : ℝ)|=(2631455429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83522821/156250000 : ℝ)*x 0 + (2631455407/5000000000 : ℝ)*x 1 + (-450901321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83522821/156250000 : ℝ)^8293 ≤ (21764562182563/50000000000000 : ℝ)^6245 := by
    have hnat : (83522821 : ℕ)^8293*50000000000000^6245 ≤ 21764562182563^6245*156250000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83522821 156250000 21764562182563 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631455407/5000000000 : ℝ)^8293 ≤ (21319362616341/50000000000000 : ℝ)^6245 := by
    have hnat : (2631455407 : ℕ)^8293*50000000000000^6245 ≤ 21319362616341^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631455407 5000000000 21319362616341 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450901321/2000000000 : ℝ)^8293 ≤ (1729018798099/12500000000000 : ℝ)^6245 := by
    have hnat : (450901321 : ℕ)^8293*12500000000000^6245 ≤ 1729018798099^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450901321 2000000000 1729018798099 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83522821/156250000 : ℝ), (2631455407/5000000000 : ℝ), (-450901321/2000000000 : ℝ)] ![(21764562182563/50000000000000 : ℝ), (21319362616341/50000000000000 : ℝ), (1729018798099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83522821/156250000 : ℝ)|^8293 ≤ (21764562182563/50000000000000 : ℝ)^6245
        have hw : |(83522821/156250000 : ℝ)|=(83522821/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631455407/5000000000 : ℝ)|^8293 ≤ (21319362616341/50000000000000 : ℝ)^6245
        have hw : |(2631455407/5000000000 : ℝ)|=(2631455407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450901321/2000000000 : ℝ)|^8293 ≤ (1729018798099/12500000000000 : ℝ)^6245
        have hw : |(-450901321/2000000000 : ℝ)|=(450901321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370510073/10000000000 : ℝ)*x 0 + (4241156221/10000000000 : ℝ)*x 1 + (4503830917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370510073/10000000000 : ℝ)^8293 ≤ (4164447559423/12500000000000 : ℝ)^6245 := by
    have hnat : (4370510073 : ℕ)^8293*12500000000000^6245 ≤ 4164447559423^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370510073 10000000000 4164447559423 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241156221/10000000000 : ℝ)^8293 ≤ (32012573187289/100000000000000 : ℝ)^6245 := by
    have hnat : (4241156221 : ℕ)^8293*100000000000000^6245 ≤ 32012573187289^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241156221 10000000000 32012573187289 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503830917/10000000000 : ℝ)^8293 ≤ (4333980790241/12500000000000 : ℝ)^6245 := by
    have hnat : (4503830917 : ℕ)^8293*12500000000000^6245 ≤ 4333980790241^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503830917 10000000000 4333980790241 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370510073/10000000000 : ℝ), (4241156221/10000000000 : ℝ), (4503830917/10000000000 : ℝ)] ![(4164447559423/12500000000000 : ℝ), (32012573187289/100000000000000 : ℝ), (4333980790241/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370510073/10000000000 : ℝ)|^8293 ≤ (4164447559423/12500000000000 : ℝ)^6245
        have hw : |(4370510073/10000000000 : ℝ)|=(4370510073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241156221/10000000000 : ℝ)|^8293 ≤ (32012573187289/100000000000000 : ℝ)^6245
        have hw : |(4241156221/10000000000 : ℝ)|=(4241156221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503830917/10000000000 : ℝ)|^8293 ≤ (4333980790241/12500000000000 : ℝ)^6245
        have hw : |(4503830917/10000000000 : ℝ)|=(4503830917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093471449/5000000000 : ℝ)*x 0 + (842121/1600000 : ℝ)*x 1 + (2697846181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093471449/5000000000 : ℝ)^8293 ≤ (6642203623577/50000000000000 : ℝ)^6245 := by
    have hnat : (1093471449 : ℕ)^8293*50000000000000^6245 ≤ 6642203623577^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093471449 5000000000 6642203623577 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842121/1600000 : ℝ)^8293 ≤ (42642441694663/100000000000000 : ℝ)^6245 := by
    have hnat : (842121 : ℕ)^8293*100000000000000^6245 ≤ 42642441694663^6245*1600000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842121 1600000 42642441694663 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697846181/5000000000 : ℝ)^8293 ≤ (8814630206791/20000000000000 : ℝ)^6245 := by
    have hnat : (2697846181 : ℕ)^8293*20000000000000^6245 ≤ 8814630206791^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697846181 5000000000 8814630206791 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093471449/5000000000 : ℝ), (842121/1600000 : ℝ), (2697846181/5000000000 : ℝ)] ![(6642203623577/50000000000000 : ℝ), (42642441694663/100000000000000 : ℝ), (8814630206791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093471449/5000000000 : ℝ)|^8293 ≤ (6642203623577/50000000000000 : ℝ)^6245
        have hw : |(-1093471449/5000000000 : ℝ)|=(1093471449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842121/1600000 : ℝ)|^8293 ≤ (42642441694663/100000000000000 : ℝ)^6245
        have hw : |(842121/1600000 : ℝ)|=(842121/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697846181/5000000000 : ℝ)|^8293 ≤ (8814630206791/20000000000000 : ℝ)^6245
        have hw : |(2697846181/5000000000 : ℝ)|=(2697846181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655919663/5000000000 : ℝ)*x 0 + (-212172501/1000000000 : ℝ)*x 1 + (5395692379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655919663/5000000000 : ℝ)^8293 ≤ (43165930332453/100000000000000 : ℝ)^6245 := by
    have hnat : (2655919663 : ℕ)^8293*100000000000000^6245 ≤ 43165930332453^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655919663 5000000000 43165930332453 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212172501/1000000000 : ℝ)^8293 ≤ (6380459218613/50000000000000 : ℝ)^6245 := by
    have hnat : (212172501 : ℕ)^8293*50000000000000^6245 ≤ 6380459218613^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212172501 1000000000 6380459218613 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395692379/10000000000 : ℝ)^8293 ≤ (2754571951147/6250000000000 : ℝ)^6245 := by
    have hnat : (5395692379 : ℕ)^8293*6250000000000^6245 ≤ 2754571951147^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395692379 10000000000 2754571951147 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655919663/5000000000 : ℝ), (-212172501/1000000000 : ℝ), (5395692379/10000000000 : ℝ)] ![(43165930332453/100000000000000 : ℝ), (6380459218613/50000000000000 : ℝ), (2754571951147/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655919663/5000000000 : ℝ)|^8293 ≤ (43165930332453/100000000000000 : ℝ)^6245
        have hw : |(2655919663/5000000000 : ℝ)|=(2655919663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212172501/1000000000 : ℝ)|^8293 ≤ (6380459218613/50000000000000 : ℝ)^6245
        have hw : |(-212172501/1000000000 : ℝ)|=(212172501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395692379/10000000000 : ℝ)|^8293 ≤ (2754571951147/6250000000000 : ℝ)^6245
        have hw : |(5395692379/10000000000 : ℝ)|=(5395692379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327959807/2500000000 : ℝ)*x 0 + (5395692461/10000000000 : ℝ)*x 1 + (-212172503/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327959807/2500000000 : ℝ)^8293 ≤ (21582964637451/50000000000000 : ℝ)^6245 := by
    have hnat : (1327959807 : ℕ)^8293*50000000000000^6245 ≤ 21582964637451^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327959807 2500000000 21582964637451 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395692461/10000000000 : ℝ)^8293 ≤ (44073152107799/100000000000000 : ℝ)^6245 := by
    have hnat : (5395692461 : ℕ)^8293*100000000000000^6245 ≤ 44073152107799^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395692461 10000000000 44073152107799 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212172503/1000000000 : ℝ)^8293 ≤ (6380459298481/50000000000000 : ℝ)^6245 := by
    have hnat : (212172503 : ℕ)^8293*50000000000000^6245 ≤ 6380459298481^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212172503 1000000000 6380459298481 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327959807/2500000000 : ℝ), (5395692461/10000000000 : ℝ), (-212172503/1000000000 : ℝ)] ![(21582964637451/50000000000000 : ℝ), (44073152107799/100000000000000 : ℝ), (6380459298481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327959807/2500000000 : ℝ)|^8293 ≤ (21582964637451/50000000000000 : ℝ)^6245
        have hw : |(1327959807/2500000000 : ℝ)|=(1327959807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395692461/10000000000 : ℝ)|^8293 ≤ (44073152107799/100000000000000 : ℝ)^6245
        have hw : |(5395692461/10000000000 : ℝ)|=(5395692461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212172503/1000000000 : ℝ)|^8293 ≤ (6380459298481/50000000000000 : ℝ)^6245
        have hw : |(-212172503/1000000000 : ℝ)|=(212172503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s5_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874104211/2000000000 : ℝ)*x 0 + (4503149633/10000000000 : ℝ)*x 1 + (4241839939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874104211/2000000000 : ℝ)^8293 ≤ (33315691642439/100000000000000 : ℝ)^6245 := by
    have hnat : (874104211 : ℕ)^8293*100000000000000^6245 ≤ 33315691642439^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874104211 2000000000 33315691642439 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503149633/10000000000 : ℝ)^8293 ≤ (34664881796459/100000000000000 : ℝ)^6245 := by
    have hnat : (4503149633 : ℕ)^8293*100000000000000^6245 ≤ 34664881796459^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503149633 10000000000 34664881796459 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241839939/10000000000 : ℝ)^8293 ≤ (1600971327747/5000000000000 : ℝ)^6245 := by
    have hnat : (4241839939 : ℕ)^8293*5000000000000^6245 ≤ 1600971327747^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241839939 10000000000 1600971327747 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874104211/2000000000 : ℝ), (4503149633/10000000000 : ℝ), (4241839939/10000000000 : ℝ)] ![(33315691642439/100000000000000 : ℝ), (34664881796459/100000000000000 : ℝ), (1600971327747/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874104211/2000000000 : ℝ)|^8293 ≤ (33315691642439/100000000000000 : ℝ)^6245
        have hw : |(874104211/2000000000 : ℝ)|=(874104211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503149633/10000000000 : ℝ)|^8293 ≤ (34664881796459/100000000000000 : ℝ)^6245
        have hw : |(4503149633/10000000000 : ℝ)|=(4503149633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241839939/10000000000 : ℝ)|^8293 ≤ (1600971327747/5000000000000 : ℝ)^6245
        have hw : |(4241839939/10000000000 : ℝ)|=(4241839939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2813/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1759/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11093/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (13600898067660883/100000000000000000000 : ℝ) := by
    have hpowers : (11093/100000 : ℝ)^2073 ≤ (13600898067660883/100000000000000000000 : ℝ)^512 := by
      have hnat : (11093 : ℕ)^2073*100000000000000000000^512 ≤ 13600898067660883^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11093 100000 13600898067660883 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11093/100000 : ℝ)) (X := (13600898067660883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (2073/512 : ℝ) ≤ (37364610190419679/100000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^2073 ≤ (37364610190419679/100000000000000000000 : ℝ)^512 := by
      have hnat : (7119 : ℕ)^2073*100000000000000000000^512 ≤ 37364610190419679^512*50000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 37364610190419679 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (37364610190419679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013600898067660883/50000000000000000000 : ℝ) ≤ (2500167943722341/2500000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50013600898067660883/50000000000000000000 : ℝ)^512 ≤ (2500167943722341/2500000000000000 : ℝ)^2073 := by
      have hnat : (50013600898067660883 : ℕ)^512*2500000000000000^2073 ≤ 2500167943722341^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013600898067660883 50000000000000000000 2500167943722341 2500000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500167943722341/2500000000000000 : ℝ)) (X := (50013600898067660883/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025482754129040281/50000000000000000000 : ℝ) ≤ (5000629265183389/5000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50025482754129040281/50000000000000000000 : ℝ)^512 ≤ (5000629265183389/5000000000000000 : ℝ)^2073 := by
      have hnat : (50025482754129040281 : ℕ)^512*5000000000000000^2073 ≤ 5000629265183389^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025482754129040281 50000000000000000000 5000629265183389 5000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000629265183389/5000000000000000 : ℝ)) (X := (50025482754129040281/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037364610190419679/50000000000000000000 : ℝ) ≤ (312557665182631/312500000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50037364610190419679/50000000000000000000 : ℝ)^512 ≤ (312557665182631/312500000000000 : ℝ)^2073 := by
      have hnat : (50037364610190419679 : ℕ)^512*312500000000000^2073 ≤ 312557665182631^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037364610190419679 50000000000000000000 312557665182631 312500000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312557665182631/312500000000000 : ℝ)) (X := (50037364610190419679/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13600898067660883/100000000000000000000 : ℝ) ≤ ((3929886871875642847/3931250000000000000 : ℝ)+2*(293377738707/157250000000000 : ℝ)*(11093/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (3929886871875642847/3931250000000000000 : ℝ)+2*(293377738707/157250000000000 : ℝ)*(11093/100000 : ℝ)=(2500167943722341/2500000000000000 : ℝ) by norm_num, show 1+2*(13600898067660883/100000000000000000000 : ℝ)=(50013600898067660883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37364610190419679/100000000000000000000 : ℝ)+(13600898067660883/100000000000000000000 : ℝ) ≤ ((3929886871875642847/3931250000000000000 : ℝ)+(293377738707/157250000000000 : ℝ)*((7119/50000 : ℝ)+(11093/100000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (3929886871875642847/3931250000000000000 : ℝ)+(293377738707/157250000000000 : ℝ)*((7119/50000 : ℝ)+(11093/100000 : ℝ))=(5000629265183389/5000000000000000 : ℝ) by norm_num, show 1+(37364610190419679/100000000000000000000 : ℝ)+(13600898067660883/100000000000000000000 : ℝ)=(50025482754129040281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37364610190419679/100000000000000000000 : ℝ) ≤ ((3929886871875642847/3931250000000000000 : ℝ)+2*(293377738707/157250000000000 : ℝ)*(7119/50000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (3929886871875642847/3931250000000000000 : ℝ)+2*(293377738707/157250000000000 : ℝ)*(7119/50000 : ℝ)=(312557665182631/312500000000000 : ℝ) by norm_num, show 1+2*(37364610190419679/100000000000000000000 : ℝ)=(50037364610190419679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3929886871875642847/3931250000000000000 : ℝ)*(X 1 0+X 2 0)+(293377738707/157250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (3929886871875642847/3931250000000000000 : ℝ)) (alpha := (293377738707/157250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3929886871875642847/3931250000000000000 : ℝ)*(X 0 1+X 2 1)+(293377738707/157250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (3929886871875642847/3931250000000000000 : ℝ)) (alpha := (293377738707/157250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3929886871875642847/3931250000000000000 : ℝ)*(X 0 2+X 1 2)+(293377738707/157250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (3929886871875642847/3931250000000000000 : ℝ)) (alpha := (293377738707/157250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437387473/2000000000 : ℝ)*X 0 0+(1079207809/2000000000 : ℝ)*X 0 1+(657863859/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345460607/10000000000 : ℝ)*X 1 0+(-70453327/312500000 : ℝ)*X 1 1+(2631455429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83522821/156250000 : ℝ)*X 2 0+(2631455407/5000000000 : ℝ)*X 2 1+(-450901321/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370510073/10000000000 : ℝ)*X 0 0+(4241156221/10000000000 : ℝ)*X 0 1+(4503830917/10000000000 : ℝ)*X 0 2+(4370510073/10000000000 : ℝ)*X 1 0+(4241156221/10000000000 : ℝ)*X 1 1+(4503830917/10000000000 : ℝ)*X 1 2+(4370510073/10000000000 : ℝ)*X 2 0+(4241156221/10000000000 : ℝ)*X 2 1+(4503830917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093471449/5000000000 : ℝ)*X 0 0+(842121/1600000 : ℝ)*X 0 1+(2697846181/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655919663/5000000000 : ℝ)*X 1 0+(-212172501/1000000000 : ℝ)*X 1 1+(5395692379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327959807/2500000000 : ℝ)*X 2 0+(5395692461/10000000000 : ℝ)*X 2 1+(-212172503/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874104211/2000000000 : ℝ)*X 0 0+(4503149633/10000000000 : ℝ)*X 0 1+(4241839939/10000000000 : ℝ)*X 0 2+(874104211/2000000000 : ℝ)*X 1 0+(4503149633/10000000000 : ℝ)*X 1 1+(4241839939/10000000000 : ℝ)*X 1 2+(874104211/2000000000 : ℝ)*X 2 0+(4503149633/10000000000 : ℝ)*X 2 1+(4241839939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90836453195089190155054413/12285156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (240988523/20000000000000 : ℝ)*(base19) + (567993429/50000000000000 : ℝ)*(base23) + (9943333/10000000000000 : ℝ)*(upper3) + (23697023/100000000000000 : ℝ)*(lower4) + (707416205271761/12500000000000 : ℝ)*(major0) + (707416205271761/12500000000000 : ℝ)*(major1) + (707416205271761/12500000000000 : ℝ)*(major2) + (7511599038126703/100000000000000 : ℝ)*(sp0) + (1502326508002541/20000000000000 : ℝ)*(sp1) + (938953584105541/12500000000000 : ℝ)*(sp2) + (237937946010201/6250000000000 : ℝ)*(sp3) + (34706828617/100000000000000 : ℝ)*(sp4) + (1968062067/50000000000000 : ℝ)*(sp6) + (18156762943/100000000000000 : ℝ)*(sp7) + (1903512646463079/50000000000000 : ℝ)*(f.failure) + (187790843623883/2500000000000 : ℝ)*(f.sum) + (2483758815317/3931250000000000000000000000 : ℝ)*base66 + (387626905890143933/49140625000000000000000000000000 : ℝ)*base68 + (12483202029148851/6142578125000000000000000000000 : ℝ)*base70 + (6242093984831433/49140625000000000000000000000000 : ℝ)*base72 + (11578636839443/15725000000000000000000000000 : ℝ)*base74 + (13955086760583881/1535644531250000000000000000000 : ℝ)*base75 + (365927232311451471/24570312500000000000000000000000 : ℝ)*base77 + (395400382364954779/24570312500000000000000000000000 : ℝ)*base80 + (6343498623907/15725000000000000000000000000 : ℝ)*base81 + (375629/50000000000000000000 : ℝ)*base90 + (375629/50000000000000000000 : ℝ)*base92 + (375629/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1908731765250962796940547187/196562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76448569/5000000000000 : ℝ)*(base19) + (770831573/50000000000000 : ℝ)*(base23) + (21153593/12500000000000 : ℝ)*(upper3) + (65243017/100000000000000 : ℝ)*(lower4) + (41304193/50000000000000 : ℝ)*(upper5) + (5688840588567969/100000000000000 : ℝ)*(major0) + (5688840588567969/100000000000000 : ℝ)*(major1) + (5688840588567969/100000000000000 : ℝ)*(major2) + (20620078551/50000000000000 : ℝ)*(sp1) + (11462311241/25000000000000 : ℝ)*(sp2) + (7550803576907457/100000000000000 : ℝ)*(sp4) + (3775380403889487/50000000000000 : ℝ)*(sp5) + (7550756185999347/100000000000000 : ℝ)*(sp6) + (59794957445987/1562500000000 : ℝ)*(sp7) + (59794957445987/1562500000000 : ℝ)*(f.failure) + (7550803576907457/100000000000000 : ℝ)*(f.sum) + (2761279878249/982812500000000000000000000 : ℝ)*base66 + (7299288678711007257/393125000000000000000000000000000 : ℝ)*base68 + (4334936138941007257/393125000000000000000000000000000 : ℝ)*base70 + (3326485792358507257/393125000000000000000000000000000 : ℝ)*base72 + (88877446618967/7862500000000000000000000000 : ℝ)*base74 + (6832895329198507257/393125000000000000000000000000000 : ℝ)*base76 + (2142500259312257257/393125000000000000000000000000000 : ℝ)*base78 + (5885063717946632257/393125000000000000000000000000000 : ℝ)*base80 + (5991231366571/3931250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6619/781250000000000000 : ℝ)*base89 + (6619/781250000000000000 : ℝ)*base91 + (6619/781250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1100_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1100_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1100_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1100_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1100_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16631/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2219/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
