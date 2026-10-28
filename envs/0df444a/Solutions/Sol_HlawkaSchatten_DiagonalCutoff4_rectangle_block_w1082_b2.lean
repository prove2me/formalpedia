-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:50:48.082987+00:00
-- url     : https://prove2.me/submissions/1d1a8c8a-1ee4-426c-bec4-71a1e5b8f8f0

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
theorem support_rectangle_w1082_s6_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195867477/10000000000 : ℝ)*x 0 + (2697296907/5000000000 : ℝ)*x 1 + (5264256881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195867477/10000000000 : ℝ)^8275 ≤ (6668632142741/50000000000000 : ℝ)^6227 := by
    have hnat : (2195867477 : ℕ)^8275*50000000000000^6227 ≤ 6668632142741^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195867477 10000000000 6668632142741 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697296907/5000000000 : ℝ)^8275 ≤ (11008866043023/25000000000000 : ℝ)^6227 := by
    have hnat : (2697296907 : ℕ)^8275*25000000000000^6227 ≤ 11008866043023^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697296907 5000000000 11008866043023 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264256881/10000000000 : ℝ)^8275 ≤ (42627271533203/100000000000000 : ℝ)^6227 := by
    have hnat : (5264256881 : ℕ)^8275*100000000000000^6227 ≤ 42627271533203^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264256881 10000000000 42627271533203 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195867477/10000000000 : ℝ), (2697296907/5000000000 : ℝ), (5264256881/10000000000 : ℝ)] ![(6668632142741/50000000000000 : ℝ), (11008866043023/25000000000000 : ℝ), (42627271533203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195867477/10000000000 : ℝ)|^8275 ≤ (6668632142741/50000000000000 : ℝ)^6227
        have hw : |(-2195867477/10000000000 : ℝ)|=(2195867477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697296907/5000000000 : ℝ)|^8275 ≤ (11008866043023/25000000000000 : ℝ)^6227
        have hw : |(2697296907/5000000000 : ℝ)|=(2697296907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264256881/10000000000 : ℝ)|^8275 ≤ (42627271533203/100000000000000 : ℝ)^6227
        have hw : |(5264256881/10000000000 : ℝ)|=(5264256881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668133711/1250000000 : ℝ)*x 0 + (-2261999423/10000000000 : ℝ)*x 1 + (658032109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668133711/1250000000 : ℝ)^8275 ≤ (43499059812397/100000000000000 : ℝ)^6227 := by
    have hnat : (668133711 : ℕ)^8275*100000000000000^6227 ≤ 43499059812397^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668133711 1250000000 43499059812397 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261999423/10000000000 : ℝ)^8275 ≤ (1387366873609/10000000000000 : ℝ)^6227 := by
    have hnat : (2261999423 : ℕ)^8275*10000000000000^6227 ≤ 1387366873609^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261999423 10000000000 1387366873609 10000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658032109/1250000000 : ℝ)^8275 ≤ (42627271436357/100000000000000 : ℝ)^6227 := by
    have hnat : (658032109 : ℕ)^8275*100000000000000^6227 ≤ 42627271436357^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658032109 1250000000 42627271436357 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668133711/1250000000 : ℝ), (-2261999423/10000000000 : ℝ), (658032109/1250000000 : ℝ)] ![(43499059812397/100000000000000 : ℝ), (1387366873609/10000000000000 : ℝ), (42627271436357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668133711/1250000000 : ℝ)|^8275 ≤ (43499059812397/100000000000000 : ℝ)^6227
        have hw : |(668133711/1250000000 : ℝ)|=(668133711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2261999423/10000000000 : ℝ)|^8275 ≤ (1387366873609/10000000000000 : ℝ)^6227
        have hw : |(-2261999423/10000000000 : ℝ)|=(2261999423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658032109/1250000000 : ℝ)|^8275 ≤ (42627271436357/100000000000000 : ℝ)^6227
        have hw : |(658032109/1250000000 : ℝ)|=(658032109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672534839/5000000000 : ℝ)*x 0 + (2632128443/5000000000 : ℝ)*x 1 + (-1130999709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672534839/5000000000 : ℝ)^8275 ≤ (173996238817/400000000000 : ℝ)^6227 := by
    have hnat : (2672534839 : ℕ)^8275*400000000000^6227 ≤ 173996238817^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672534839 5000000000 173996238817 400000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632128443/5000000000 : ℝ)^8275 ≤ (21313635793503/50000000000000 : ℝ)^6227 := by
    have hnat : (2632128443 : ℕ)^8275*50000000000000^6227 ≤ 21313635793503^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632128443 5000000000 21313635793503 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130999709/5000000000 : ℝ)^8275 ≤ (13873668695337/100000000000000 : ℝ)^6227 := by
    have hnat : (1130999709 : ℕ)^8275*100000000000000^6227 ≤ 13873668695337^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130999709 5000000000 13873668695337 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672534839/5000000000 : ℝ), (2632128443/5000000000 : ℝ), (-1130999709/5000000000 : ℝ)] ![(173996238817/400000000000 : ℝ), (21313635793503/50000000000000 : ℝ), (13873668695337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672534839/5000000000 : ℝ)|^8275 ≤ (173996238817/400000000000 : ℝ)^6227
        have hw : |(2672534839/5000000000 : ℝ)|=(2672534839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632128443/5000000000 : ℝ)|^8275 ≤ (21313635793503/50000000000000 : ℝ)^6227
        have hw : |(2632128443/5000000000 : ℝ)|=(2632128443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130999709/5000000000 : ℝ)|^8275 ≤ (13873668695337/100000000000000 : ℝ)^6227
        have hw : |(-1130999709/5000000000 : ℝ)|=(1130999709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093292627/2500000000 : ℝ)*x 0 + (4246937877/10000000000 : ℝ)*x 1 + (562898967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093292627/2500000000 : ℝ)^8275 ≤ (33316381653997/100000000000000 : ℝ)^6227 := by
    have hnat : (1093292627 : ℕ)^8275*100000000000000^6227 ≤ 33316381653997^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093292627 2500000000 33316381653997 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246937877/10000000000 : ℝ)^8275 ≤ (4005564128563/12500000000000 : ℝ)^6227 := by
    have hnat : (4246937877 : ℕ)^8275*12500000000000^6227 ≤ 4005564128563^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246937877 10000000000 4005564128563 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562898967/1250000000 : ℝ)^8275 ≤ (34639105308127/100000000000000 : ℝ)^6227 := by
    have hnat : (562898967 : ℕ)^8275*100000000000000^6227 ≤ 34639105308127^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562898967 1250000000 34639105308127 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093292627/2500000000 : ℝ), (4246937877/10000000000 : ℝ), (562898967/1250000000 : ℝ)] ![(33316381653997/100000000000000 : ℝ), (4005564128563/12500000000000 : ℝ), (34639105308127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093292627/2500000000 : ℝ)|^8275 ≤ (33316381653997/100000000000000 : ℝ)^6227
        have hw : |(1093292627/2500000000 : ℝ)|=(1093292627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246937877/10000000000 : ℝ)|^8275 ≤ (4005564128563/12500000000000 : ℝ)^6227
        have hw : |(4246937877/10000000000 : ℝ)|=(4246937877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562898967/1250000000 : ℝ)|^8275 ≤ (34639105308127/100000000000000 : ℝ)^6227
        have hw : |(562898967/1250000000 : ℝ)|=(562898967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097936093/5000000000 : ℝ)*x 0 + (1316146559/2500000000 : ℝ)*x 1 + (2697131793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097936093/5000000000 : ℝ)^8275 ≤ (3334325573449/25000000000000 : ℝ)^6227 := by
    have hnat : (1097936093 : ℕ)^8275*25000000000000^6227 ≤ 3334325573449^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097936093 5000000000 3334325573449 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316146559/2500000000 : ℝ)^8275 ≤ (2664425978279/6250000000000 : ℝ)^6227 := by
    have hnat : (1316146559 : ℕ)^8275*6250000000000^6227 ≤ 2664425978279^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316146559 2500000000 2664425978279 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697131793/5000000000 : ℝ)^8275 ≤ (880637640653/2000000000000 : ℝ)^6227 := by
    have hnat : (2697131793 : ℕ)^8275*2000000000000^6227 ≤ 880637640653^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697131793 5000000000 880637640653 2000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097936093/5000000000 : ℝ), (1316146559/2500000000 : ℝ), (2697131793/5000000000 : ℝ)] ![(3334325573449/25000000000000 : ℝ), (2664425978279/6250000000000 : ℝ), (880637640653/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097936093/5000000000 : ℝ)|^8275 ≤ (3334325573449/25000000000000 : ℝ)^6227
        have hw : |(-1097936093/5000000000 : ℝ)|=(1097936093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316146559/2500000000 : ℝ)|^8275 ≤ (2664425978279/6250000000000 : ℝ)^6227
        have hw : |(1316146559/2500000000 : ℝ)|=(1316146559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697131793/5000000000 : ℝ)|^8275 ≤ (880637640653/2000000000000 : ℝ)^6227
        have hw : |(2697131793/5000000000 : ℝ)|=(2697131793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656099291/5000000000 : ℝ)*x 0 + (-2131993111/10000000000 : ℝ)*x 1 + (5394263603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656099291/5000000000 : ℝ)^8275 ≤ (21571963860369/50000000000000 : ℝ)^6227 := by
    have hnat : (2656099291 : ℕ)^8275*50000000000000^6227 ≤ 21571963860369^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656099291 5000000000 21571963860369 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131993111/10000000000 : ℝ)^8275 ≤ (12824190049971/100000000000000 : ℝ)^6227 := by
    have hnat : (2131993111 : ℕ)^8275*100000000000000^6227 ≤ 12824190049971^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131993111 10000000000 12824190049971 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394263603/10000000000 : ℝ)^8275 ≤ (8806376443411/20000000000000 : ℝ)^6227 := by
    have hnat : (5394263603 : ℕ)^8275*20000000000000^6227 ≤ 8806376443411^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394263603 10000000000 8806376443411 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656099291/5000000000 : ℝ), (-2131993111/10000000000 : ℝ), (5394263603/10000000000 : ℝ)] ![(21571963860369/50000000000000 : ℝ), (12824190049971/100000000000000 : ℝ), (8806376443411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656099291/5000000000 : ℝ)|^8275 ≤ (21571963860369/50000000000000 : ℝ)^6227
        have hw : |(2656099291/5000000000 : ℝ)|=(2656099291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131993111/10000000000 : ℝ)|^8275 ≤ (12824190049971/100000000000000 : ℝ)^6227
        have hw : |(-2131993111/10000000000 : ℝ)|=(2131993111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394263603/10000000000 : ℝ)|^8275 ≤ (8806376443411/20000000000000 : ℝ)^6227
        have hw : |(5394263603/10000000000 : ℝ)|=(5394263603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312198787/10000000000 : ℝ)*x 0 + (539426351/1000000000 : ℝ)*x 1 + (-3331239/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312198787/10000000000 : ℝ)^8275 ≤ (2696495620829/6250000000000 : ℝ)^6227 := by
    have hnat : (5312198787 : ℕ)^8275*6250000000000^6227 ≤ 2696495620829^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312198787 10000000000 2696495620829 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539426351/1000000000 : ℝ)^8275 ≤ (176127524833/400000000000 : ℝ)^6227 := by
    have hnat : (539426351 : ℕ)^8275*400000000000^6227 ≤ 176127524833^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539426351 1000000000 176127524833 400000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3331239/15625000 : ℝ)^8275 ≤ (12824188842963/100000000000000 : ℝ)^6227 := by
    have hnat : (3331239 : ℕ)^8275*100000000000000^6227 ≤ 12824188842963^6227*15625000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331239 15625000 12824188842963 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312198787/10000000000 : ℝ), (539426351/1000000000 : ℝ), (-3331239/15625000 : ℝ)] ![(2696495620829/6250000000000 : ℝ), (176127524833/400000000000 : ℝ), (12824188842963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312198787/10000000000 : ℝ)|^8275 ≤ (2696495620829/6250000000000 : ℝ)^6227
        have hw : |(5312198787/10000000000 : ℝ)|=(5312198787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539426351/1000000000 : ℝ)|^8275 ≤ (176127524833/400000000000 : ℝ)^6227
        have hw : |(539426351/1000000000 : ℝ)|=(539426351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3331239/15625000 : ℝ)|^8275 ≤ (12824188842963/100000000000000 : ℝ)^6227
        have hw : |(-3331239/15625000 : ℝ)|=(3331239/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s6_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373180367/10000000000 : ℝ)*x 0 + (4502544821/10000000000 : ℝ)*x 1 + (4247587391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373180367/10000000000 : ℝ)^8275 ≤ (33316481466187/100000000000000 : ℝ)^6227 := by
    have hnat : (4373180367 : ℕ)^8275*100000000000000^6227 ≤ 33316481466187^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373180367 10000000000 33316481466187 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502544821/10000000000 : ℝ)^8275 ≤ (34632492707023/100000000000000 : ℝ)^6227 := by
    have hnat : (4502544821 : ℕ)^8275*100000000000000^6227 ≤ 34632492707023^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502544821 10000000000 34632492707023 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247587391/10000000000 : ℝ)^8275 ≤ (4006378225941/12500000000000 : ℝ)^6227 := by
    have hnat : (4247587391 : ℕ)^8275*12500000000000^6227 ≤ 4006378225941^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247587391 10000000000 4006378225941 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373180367/10000000000 : ℝ), (4502544821/10000000000 : ℝ), (4247587391/10000000000 : ℝ)] ![(33316481466187/100000000000000 : ℝ), (34632492707023/100000000000000 : ℝ), (4006378225941/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373180367/10000000000 : ℝ)|^8275 ≤ (33316481466187/100000000000000 : ℝ)^6227
        have hw : |(4373180367/10000000000 : ℝ)|=(4373180367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502544821/10000000000 : ℝ)|^8275 ≤ (34632492707023/100000000000000 : ℝ)^6227
        have hw : |(4502544821/10000000000 : ℝ)|=(4502544821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247587391/10000000000 : ℝ)|^8275 ≤ (4006378225941/12500000000000 : ℝ)^6227
        have hw : |(4247587391/10000000000 : ℝ)|=(4247587391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1403/12500 : ℝ) ^ (4137/1024 : ℝ) ≤ (14539833549547983/100000000000000000000 : ℝ) := by
    have hpowers : (1403/12500 : ℝ)^4137 ≤ (14539833549547983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1403 : ℕ)^4137*100000000000000000000^1024 ≤ 14539833549547983^1024*12500^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 12500 14539833549547983 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/12500 : ℝ)) (X := (14539833549547983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (4137/1024 : ℝ) ≤ (18089279285503933/50000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^4137 ≤ (18089279285503933/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2813 : ℕ)^4137*50000000000000000000^1024 ≤ 18089279285503933^1024*20000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 18089279285503933 50000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (18089279285503933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014539833549547983/50000000000000000000 : ℝ) ≤ (10000719708042731/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50014539833549547983/50000000000000000000 : ℝ)^1024 ≤ (10000719708042731/10000000000000000 : ℝ)^4137 := by
      have hnat : (50014539833549547983 : ℕ)^1024*10000000000000000^4137 ≤ 10000719708042731^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014539833549547983 50000000000000000000 10000719708042731 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000719708042731/10000000000000000 : ℝ)) (X := (50014539833549547983/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050718392120555849/100000000000000000000 : ℝ) ≤ (5000627577060559/5000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (100050718392120555849/100000000000000000000 : ℝ)^1024 ≤ (5000627577060559/5000000000000000 : ℝ)^4137 := by
      have hnat : (100050718392120555849 : ℕ)^1024*5000000000000000^4137 ≤ 5000627577060559^4137*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050718392120555849 100000000000000000000 5000627577060559 5000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000627577060559/5000000000000000 : ℝ)) (X := (100050718392120555849/100000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018089279285503933/25000000000000000000 : ℝ) ≤ (2000358120039901/2000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (25018089279285503933/25000000000000000000 : ℝ)^1024 ≤ (2000358120039901/2000000000000000 : ℝ)^4137 := by
      have hnat : (25018089279285503933 : ℕ)^1024*2000000000000000^4137 ≤ 2000358120039901^4137*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018089279285503933 25000000000000000000 2000358120039901 2000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000358120039901/2000000000000000 : ℝ)) (X := (25018089279285503933/25000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14539833549547983/100000000000000000000 : ℝ) ≤ ((1893334999798784493/1894000000000000000 : ℝ)+2*(178482026129/94700000000000 : ℝ)*(1403/12500 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (1893334999798784493/1894000000000000000 : ℝ)+2*(178482026129/94700000000000 : ℝ)*(1403/12500 : ℝ)=(10000719708042731/10000000000000000 : ℝ) by norm_num, show 1+2*(14539833549547983/100000000000000000000 : ℝ)=(50014539833549547983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18089279285503933/50000000000000000000 : ℝ)+(14539833549547983/100000000000000000000 : ℝ) ≤ ((1893334999798784493/1894000000000000000 : ℝ)+(178482026129/94700000000000 : ℝ)*((2813/20000 : ℝ)+(1403/12500 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (1893334999798784493/1894000000000000000 : ℝ)+(178482026129/94700000000000 : ℝ)*((2813/20000 : ℝ)+(1403/12500 : ℝ))=(5000627577060559/5000000000000000 : ℝ) by norm_num, show 1+(18089279285503933/50000000000000000000 : ℝ)+(14539833549547983/100000000000000000000 : ℝ)=(100050718392120555849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18089279285503933/50000000000000000000 : ℝ) ≤ ((1893334999798784493/1894000000000000000 : ℝ)+2*(178482026129/94700000000000 : ℝ)*(2813/20000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (1893334999798784493/1894000000000000000 : ℝ)+2*(178482026129/94700000000000 : ℝ)*(2813/20000 : ℝ)=(2000358120039901/2000000000000000 : ℝ) by norm_num, show 1+2*(18089279285503933/50000000000000000000 : ℝ)=(25018089279285503933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1893334999798784493/1894000000000000000 : ℝ)*(X 1 0+X 2 0)+(178482026129/94700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (1893334999798784493/1894000000000000000 : ℝ)) (alpha := (178482026129/94700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1893334999798784493/1894000000000000000 : ℝ)*(X 0 1+X 2 1)+(178482026129/94700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (1893334999798784493/1894000000000000000 : ℝ)) (alpha := (178482026129/94700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1893334999798784493/1894000000000000000 : ℝ)*(X 0 2+X 1 2)+(178482026129/94700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (1893334999798784493/1894000000000000000 : ℝ)) (alpha := (178482026129/94700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2195867477/10000000000 : ℝ)*X 0 0+(2697296907/5000000000 : ℝ)*X 0 1+(5264256881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668133711/1250000000 : ℝ)*X 1 0+(-2261999423/10000000000 : ℝ)*X 1 1+(658032109/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672534839/5000000000 : ℝ)*X 2 0+(2632128443/5000000000 : ℝ)*X 2 1+(-1130999709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093292627/2500000000 : ℝ)*X 0 0+(4246937877/10000000000 : ℝ)*X 0 1+(562898967/1250000000 : ℝ)*X 0 2+(1093292627/2500000000 : ℝ)*X 1 0+(4246937877/10000000000 : ℝ)*X 1 1+(562898967/1250000000 : ℝ)*X 1 2+(1093292627/2500000000 : ℝ)*X 2 0+(4246937877/10000000000 : ℝ)*X 2 1+(562898967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1097936093/5000000000 : ℝ)*X 0 0+(1316146559/2500000000 : ℝ)*X 0 1+(2697131793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656099291/5000000000 : ℝ)*X 1 0+(-2131993111/10000000000 : ℝ)*X 1 1+(5394263603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312198787/10000000000 : ℝ)*X 2 0+(539426351/1000000000 : ℝ)*X 2 1+(-3331239/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373180367/10000000000 : ℝ)*X 0 0+(4502544821/10000000000 : ℝ)*X 0 1+(4247587391/10000000000 : ℝ)*X 0 2+(4373180367/10000000000 : ℝ)*X 1 0+(4502544821/10000000000 : ℝ)*X 1 1+(4247587391/10000000000 : ℝ)*X 1 2+(4373180367/10000000000 : ℝ)*X 2 0+(4502544821/10000000000 : ℝ)*X 2 1+(4247587391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (648001519420884320915508963/94700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (715462493/50000000000000 : ℝ)*(base19) + (262747919/20000000000000 : ℝ)*(base23) + (5496391/10000000000000 : ℝ)*(lower2) + (86796339/50000000000000 : ℝ)*(upper3) + (51155201/50000000000000 : ℝ)*(upper5) + (5787460562981403/100000000000000 : ℝ)*(major0) + (5787460562981403/100000000000000 : ℝ)*(major1) + (5787460562981403/100000000000000 : ℝ)*(major2) + (7672462449281619/100000000000000 : ℝ)*(sp0) + (959062407349871/12500000000000 : ℝ)*(sp1) + (3836249687992179/50000000000000 : ℝ)*(sp2) + (975599807684371/25000000000000 : ℝ)*(sp3) + (19120221167/50000000000000 : ℝ)*(sp4) + (20977412119/100000000000000 : ℝ)*(sp7) + (3902420208149603/100000000000000 : ℝ)*(f.failure) + (3836250344861977/50000000000000 : ℝ)*(f.sum) + (9626597239143/4735000000000000000000000000 : ℝ)*base66 + (3903911902427723679/189400000000000000000000000000000 : ℝ)*base67 + (2233961314393123679/189400000000000000000000000000000 : ℝ)*base69 + (4241099614449076321/189400000000000000000000000000000 : ℝ)*base72 + (9660863532641/2367500000000000000000000000 : ℝ)*base73 + (5528784920942923679/189400000000000000000000000000000 : ℝ)*base75 + (870843046205076321/189400000000000000000000000000000 : ℝ)*base78 + (2218181919506523679/189400000000000000000000000000000 : ℝ)*base79 + (1174794795359/591875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2244547/1250000000000000000000 : ℝ)*base89 + (2244547/1250000000000000000000 : ℝ)*base91 + (2244547/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12024125011773386069436111/947000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8906807/6250000000000 : ℝ)*(base19) + (465539567/50000000000000 : ℝ)*(base23) + (37854519/50000000000000 : ℝ)*(lower2) + (787453/1000000000000 : ℝ)*(upper3) + (100677/39062500000 : ℝ)*(lower4) + (58168349094791/1000000000000 : ℝ)*(major0) + (58168349094791/1000000000000 : ℝ)*(major1) + (58168349094791/1000000000000 : ℝ)*(major2) + (1198560919/5000000000000 : ℝ)*(sp2) + (156427223/20000000000000 : ℝ)*(sp3) + (7711442392843823/100000000000000 : ℝ)*(sp4) + (771144225033491/10000000000000 : ℝ)*(sp5) + (7711417490546309/100000000000000 : ℝ)*(sp6) + (19611131103713/500000000000 : ℝ)*(sp7) + (784445400575743/20000000000000 : ℝ)*(f.failure) + (7711442392843823/100000000000000 : ℝ)*(f.sum) + (290310693253/473500000000000000000000000 : ℝ)*base65 + (13514137642946037/1894000000000000000000000000000 : ℝ)*base68 + (2088996423563963/1894000000000000000000000000000 : ℝ)*base69 + (1002414832095963/1894000000000000000000000000000 : ℝ)*base71 + (98233699927/189400000000000000000000000 : ℝ)*base74 + (5537304773475963/1894000000000000000000000000000 : ℝ)*base75 + (29991590586386037/1894000000000000000000000000000 : ℝ)*base78 + (1893118551505963/1894000000000000000000000000000 : ℝ)*base79 + (181204915153/47350000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1945407/250000000000000000000 : ℝ)*base89 + (1945407/250000000000000000000 : ℝ)*base91 + (1945407/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1082_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_s7_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195905739/10000000000 : ℝ)*x 0 + (674270621/1250000000 : ℝ)*x 1 + (1028254/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195905739/10000000000 : ℝ)^8275 ≤ (13337573114911/100000000000000 : ℝ)^6227 := by
    have hnat : (2195905739 : ℕ)^8275*100000000000000^6227 ≤ 13337573114911^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195905739 10000000000 13337573114911 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674270621/1250000000 : ℝ)^8275 ≤ (8806162458101/20000000000000 : ℝ)^6227 := by
    have hnat : (674270621 : ℕ)^8275*20000000000000^6227 ≤ 8806162458101^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674270621 1250000000 8806162458101 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028254/1953125 : ℝ)^8275 ≤ (8526322917293/20000000000000 : ℝ)^6227 := by
    have hnat : (1028254 : ℕ)^8275*20000000000000^6227 ≤ 8526322917293^6227*1953125^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028254 1953125 8526322917293 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195905739/10000000000 : ℝ), (674270621/1250000000 : ℝ), (1028254/1953125 : ℝ)] ![(13337573114911/100000000000000 : ℝ), (8806162458101/20000000000000 : ℝ), (8526322917293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195905739/10000000000 : ℝ)|^8275 ≤ (13337573114911/100000000000000 : ℝ)^6227
        have hw : |(-2195905739/10000000000 : ℝ)|=(2195905739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674270621/1250000000 : ℝ)|^8275 ≤ (8806162458101/20000000000000 : ℝ)^6227
        have hw : |(674270621/1250000000 : ℝ)|=(674270621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028254/1953125 : ℝ)|^8275 ≤ (8526322917293/20000000000000 : ℝ)^6227
        have hw : |(1028254/1953125 : ℝ)|=(1028254/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213798493/400000000 : ℝ)*x 0 + (-8834407/39062500 : ℝ)*x 1 + (1052932219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213798493/400000000 : ℝ)^8275 ≤ (43497898714499/100000000000000 : ℝ)^6227 := by
    have hnat : (213798493 : ℕ)^8275*100000000000000^6227 ≤ 43497898714499^6227*400000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213798493 400000000 43497898714499 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8834407/39062500 : ℝ)^8275 ≤ (13870480071241/100000000000000 : ℝ)^6227 := by
    have hnat : (8834407 : ℕ)^8275*100000000000000^6227 ≤ 13870480071241^6227*39062500^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8834407 39062500 13870480071241 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052932219/2000000000 : ℝ)^8275 ≤ (1332238162639/3125000000000 : ℝ)^6227 := by
    have hnat : (1052932219 : ℕ)^8275*3125000000000^6227 ≤ 1332238162639^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052932219 2000000000 1332238162639 3125000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213798493/400000000 : ℝ), (-8834407/39062500 : ℝ), (1052932219/2000000000 : ℝ)] ![(43497898714499/100000000000000 : ℝ), (13870480071241/100000000000000 : ℝ), (1332238162639/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213798493/400000000 : ℝ)|^8275 ≤ (43497898714499/100000000000000 : ℝ)^6227
        have hw : |(213798493/400000000 : ℝ)|=(213798493/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8834407/39062500 : ℝ)|^8275 ≤ (13870480071241/100000000000000 : ℝ)^6227
        have hw : |(-8834407/39062500 : ℝ)|=(8834407/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052932219/2000000000 : ℝ)|^8275 ≤ (1332238162639/3125000000000 : ℝ)^6227
        have hw : |(1052932219/2000000000 : ℝ)|=(1052932219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213798501/400000000 : ℝ)*x 0 + (1316165141/2500000000 : ℝ)*x 1 + (-565402157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213798501/400000000 : ℝ)^8275 ≤ (4349790087743/10000000000000 : ℝ)^6227 := by
    have hnat : (213798501 : ℕ)^8275*10000000000000^6227 ≤ 4349790087743^6227*400000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213798501 400000000 4349790087743 10000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316165141/2500000000 : ℝ)^8275 ≤ (8526323098077/20000000000000 : ℝ)^6227 := by
    have hnat : (1316165141 : ℕ)^8275*20000000000000^6227 ≤ 8526323098077^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316165141 2500000000 8526323098077 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565402157/2500000000 : ℝ)^8275 ≤ (13870483624687/100000000000000 : ℝ)^6227 := by
    have hnat : (565402157 : ℕ)^8275*100000000000000^6227 ≤ 13870483624687^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565402157 2500000000 13870483624687 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213798501/400000000 : ℝ), (1316165141/2500000000 : ℝ), (-565402157/2500000000 : ℝ)] ![(4349790087743/10000000000000 : ℝ), (8526323098077/20000000000000 : ℝ), (13870483624687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213798501/400000000 : ℝ)|^8275 ≤ (4349790087743/10000000000000 : ℝ)^6227
        have hw : |(213798501/400000000 : ℝ)|=(213798501/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316165141/2500000000 : ℝ)|^8275 ≤ (8526323098077/20000000000000 : ℝ)^6227
        have hw : |(1316165141/2500000000 : ℝ)|=(1316165141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565402157/2500000000 : ℝ)|^8275 ≤ (13870483624687/100000000000000 : ℝ)^6227
        have hw : |(-565402157/2500000000 : ℝ)|=(565402157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34165559/78125000 : ℝ)*x 0 + (1061938653/2500000000 : ℝ)*x 1 + (900473939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34165559/78125000 : ℝ)^8275 ≤ (16658297351423/50000000000000 : ℝ)^6227 := by
    have hnat : (34165559 : ℕ)^8275*50000000000000^6227 ≤ 16658297351423^6227*78125000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34165559 78125000 16658297351423 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061938653/2500000000 : ℝ)^8275 ≤ (16026351305907/50000000000000 : ℝ)^6227 := by
    have hnat : (1061938653 : ℕ)^8275*50000000000000^6227 ≤ 16026351305907^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061938653 2500000000 16026351305907 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900473939/2000000000 : ℝ)^8275 ≤ (8657675666799/25000000000000 : ℝ)^6227 := by
    have hnat : (900473939 : ℕ)^8275*25000000000000^6227 ≤ 8657675666799^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900473939 2000000000 8657675666799 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34165559/78125000 : ℝ), (1061938653/2500000000 : ℝ), (900473939/2000000000 : ℝ)] ![(16658297351423/50000000000000 : ℝ), (16026351305907/50000000000000 : ℝ), (8657675666799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34165559/78125000 : ℝ)|^8275 ≤ (16658297351423/50000000000000 : ℝ)^6227
        have hw : |(34165559/78125000 : ℝ)|=(34165559/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061938653/2500000000 : ℝ)|^8275 ≤ (16026351305907/50000000000000 : ℝ)^6227
        have hw : |(1061938653/2500000000 : ℝ)|=(1061938653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900473939/2000000000 : ℝ)|^8275 ≤ (8657675666799/25000000000000 : ℝ)^6227
        have hw : |(900473939/2000000000 : ℝ)|=(900473939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097955249/5000000000 : ℝ)*x 0 + (1316246491/2500000000 : ℝ)*x 1 + (5393838527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097955249/5000000000 : ℝ)^8275 ≤ (13337611527017/100000000000000 : ℝ)^6227 := by
    have hnat : (1097955249 : ℕ)^8275*100000000000000^6227 ≤ 13337611527017^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097955249 5000000000 13337611527017 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316246491/2500000000 : ℝ)^8275 ≤ (10658779284651/25000000000000 : ℝ)^6227 := by
    have hnat : (1316246491 : ℕ)^8275*25000000000000^6227 ≤ 10658779284651^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316246491 2500000000 10658779284651 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393838527/10000000000 : ℝ)^8275 ≤ (44027271322623/100000000000000 : ℝ)^6227 := by
    have hnat : (5393838527 : ℕ)^8275*100000000000000^6227 ≤ 44027271322623^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393838527 10000000000 44027271322623 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097955249/5000000000 : ℝ), (1316246491/2500000000 : ℝ), (5393838527/10000000000 : ℝ)] ![(13337611527017/100000000000000 : ℝ), (10658779284651/25000000000000 : ℝ), (44027271322623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097955249/5000000000 : ℝ)|^8275 ≤ (13337611527017/100000000000000 : ℝ)^6227
        have hw : |(-1097955249/5000000000 : ℝ)|=(1097955249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316246491/2500000000 : ℝ)|^8275 ≤ (10658779284651/25000000000000 : ℝ)^6227
        have hw : |(1316246491/2500000000 : ℝ)|=(1316246491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393838527/10000000000 : ℝ)|^8275 ≤ (44027271322623/100000000000000 : ℝ)^6227
        have hw : |(5393838527/10000000000 : ℝ)|=(5393838527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328075373/2500000000 : ℝ)*x 0 + (-2132430981/10000000000 : ℝ)*x 1 + (5393838527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328075373/2500000000 : ℝ)^8275 ≤ (4314503841231/10000000000000 : ℝ)^6227 := by
    have hnat : (1328075373 : ℕ)^8275*10000000000000^6227 ≤ 4314503841231^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328075373 2500000000 4314503841231 10000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132430981/10000000000 : ℝ)^8275 ≤ (51310761009/400000000000 : ℝ)^6227 := by
    have hnat : (2132430981 : ℕ)^8275*400000000000^6227 ≤ 51310761009^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132430981 10000000000 51310761009 400000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393838527/10000000000 : ℝ)^8275 ≤ (44027271322623/100000000000000 : ℝ)^6227 := by
    have hnat : (5393838527 : ℕ)^8275*100000000000000^6227 ≤ 44027271322623^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393838527 10000000000 44027271322623 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328075373/2500000000 : ℝ), (-2132430981/10000000000 : ℝ), (5393838527/10000000000 : ℝ)] ![(4314503841231/10000000000000 : ℝ), (51310761009/400000000000 : ℝ), (44027271322623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328075373/2500000000 : ℝ)|^8275 ≤ (4314503841231/10000000000000 : ℝ)^6227
        have hw : |(1328075373/2500000000 : ℝ)|=(1328075373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132430981/10000000000 : ℝ)|^8275 ≤ (51310761009/400000000000 : ℝ)^6227
        have hw : |(-2132430981/10000000000 : ℝ)|=(2132430981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393838527/10000000000 : ℝ)|^8275 ≤ (44027271322623/100000000000000 : ℝ)^6227
        have hw : |(5393838527/10000000000 : ℝ)|=(5393838527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312301493/10000000000 : ℝ)*x 0 + (5393838527/10000000000 : ℝ)*x 1 + (-106621549/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312301493/10000000000 : ℝ)^8275 ≤ (43145038423103/100000000000000 : ℝ)^6227 := by
    have hnat : (5312301493 : ℕ)^8275*100000000000000^6227 ≤ 43145038423103^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312301493 10000000000 43145038423103 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393838527/10000000000 : ℝ)^8275 ≤ (44027271322623/100000000000000 : ℝ)^6227 := by
    have hnat : (5393838527 : ℕ)^8275*100000000000000^6227 ≤ 44027271322623^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393838527 10000000000 44027271322623 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106621549/500000000 : ℝ)^8275 ≤ (400865320133/3125000000000 : ℝ)^6227 := by
    have hnat : (106621549 : ℕ)^8275*3125000000000^6227 ≤ 400865320133^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106621549 500000000 400865320133 3125000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312301493/10000000000 : ℝ), (5393838527/10000000000 : ℝ), (-106621549/500000000 : ℝ)] ![(43145038423103/100000000000000 : ℝ), (44027271322623/100000000000000 : ℝ), (400865320133/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312301493/10000000000 : ℝ)|^8275 ≤ (43145038423103/100000000000000 : ℝ)^6227
        have hw : |(5312301493/10000000000 : ℝ)|=(5312301493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393838527/10000000000 : ℝ)|^8275 ≤ (44027271322623/100000000000000 : ℝ)^6227
        have hw : |(5393838527/10000000000 : ℝ)|=(5393838527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106621549/500000000 : ℝ)|^8275 ≤ (400865320133/3125000000000 : ℝ)^6227
        have hw : |(-106621549/500000000 : ℝ)|=(106621549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s7_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186600873/5000000000 : ℝ)*x 0 + (900346179/2000000000 : ℝ)*x 1 + (4248395437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186600873/5000000000 : ℝ)^8275 ≤ (33316697906729/100000000000000 : ℝ)^6227 := by
    have hnat : (2186600873 : ℕ)^8275*100000000000000^6227 ≤ 33316697906729^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186600873 5000000000 33316697906729 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900346179/2000000000 : ℝ)^8275 ≤ (17312086702853/50000000000000 : ℝ)^6227 := by
    have hnat : (900346179 : ℕ)^8275*50000000000000^6227 ≤ 17312086702853^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900346179 2000000000 17312086702853 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248395437/10000000000 : ℝ)^8275 ≤ (8014782167267/25000000000000 : ℝ)^6227 := by
    have hnat : (4248395437 : ℕ)^8275*25000000000000^6227 ≤ 8014782167267^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248395437 10000000000 8014782167267 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186600873/5000000000 : ℝ), (900346179/2000000000 : ℝ), (4248395437/10000000000 : ℝ)] ![(33316697906729/100000000000000 : ℝ), (17312086702853/50000000000000 : ℝ), (8014782167267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186600873/5000000000 : ℝ)|^8275 ≤ (33316697906729/100000000000000 : ℝ)^6227
        have hw : |(2186600873/5000000000 : ℝ)|=(2186600873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900346179/2000000000 : ℝ)|^8275 ≤ (17312086702853/50000000000000 : ℝ)^6227
        have hw : |(900346179/2000000000 : ℝ)|=(900346179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248395437/10000000000 : ℝ)|^8275 ≤ (8014782167267/25000000000000 : ℝ)^6227
        have hw : |(4248395437/10000000000 : ℝ)|=(4248395437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1409/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2803/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (7372511512451019/50000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^4137 ≤ (7372511512451019/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11263 : ℕ)^4137*50000000000000000000^1024 ≤ 7372511512451019^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 7372511512451019 50000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (7372511512451019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (4137/1024 : ℝ) ≤ (17877186361356689/50000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^4137 ≤ (17877186361356689/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1753 : ℕ)^4137*50000000000000000000^1024 ≤ 17877186361356689^1024*12500^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 17877186361356689 50000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (17877186361356689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007372511512451019/25000000000000000000 : ℝ) ≤ (10000729863601517/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (25007372511512451019/25000000000000000000 : ℝ)^1024 ≤ (10000729863601517/10000000000000000 : ℝ)^4137 := by
      have hnat : (25007372511512451019 : ℕ)^1024*10000000000000000^4137 ≤ 10000729863601517^4137*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007372511512451019 25000000000000000000 10000729863601517 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729863601517/10000000000000000 : ℝ)) (X := (25007372511512451019/25000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506312424468451927/12500000000000000000 : ℝ) ≤ (1000124973553461/1000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (12506312424468451927/12500000000000000000 : ℝ)^1024 ≤ (1000124973553461/1000000000000000 : ℝ)^4137 := by
      have hnat : (12506312424468451927 : ℕ)^1024*1000000000000000^4137 ≤ 1000124973553461^4137*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506312424468451927 12500000000000000000 1000124973553461 1000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000124973553461/1000000000000000 : ℝ)) (X := (12506312424468451927/12500000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017877186361356689/25000000000000000000 : ℝ) ≤ (10001769607467703/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (25017877186361356689/25000000000000000000 : ℝ)^1024 ≤ (10001769607467703/10000000000000000 : ℝ)^4137 := by
      have hnat : (25017877186361356689 : ℕ)^1024*10000000000000000^4137 ≤ 10001769607467703^4137*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017877186361356689 25000000000000000000 10001769607467703 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001769607467703/10000000000000000 : ℝ)) (X := (25017877186361356689/25000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7372511512451019/50000000000000000000 : ℝ) ≤ ((27600304518238935519/27610000000000000000 : ℝ)+2*(519871933093/276100000000000 : ℝ)*(11263/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (27600304518238935519/27610000000000000000 : ℝ)+2*(519871933093/276100000000000 : ℝ)*(11263/100000 : ℝ)=(10000729863601517/10000000000000000 : ℝ) by norm_num, show 1+2*(7372511512451019/50000000000000000000 : ℝ)=(25007372511512451019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17877186361356689/50000000000000000000 : ℝ)+(7372511512451019/50000000000000000000 : ℝ) ≤ ((27600304518238935519/27610000000000000000 : ℝ)+(519871933093/276100000000000 : ℝ)*((1753/12500 : ℝ)+(11263/100000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (27600304518238935519/27610000000000000000 : ℝ)+(519871933093/276100000000000 : ℝ)*((1753/12500 : ℝ)+(11263/100000 : ℝ))=(1000124973553461/1000000000000000 : ℝ) by norm_num, show 1+(17877186361356689/50000000000000000000 : ℝ)+(7372511512451019/50000000000000000000 : ℝ)=(12506312424468451927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17877186361356689/50000000000000000000 : ℝ) ≤ ((27600304518238935519/27610000000000000000 : ℝ)+2*(519871933093/276100000000000 : ℝ)*(1753/12500 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (27600304518238935519/27610000000000000000 : ℝ)+2*(519871933093/276100000000000 : ℝ)*(1753/12500 : ℝ)=(10001769607467703/10000000000000000 : ℝ) by norm_num, show 1+2*(17877186361356689/50000000000000000000 : ℝ)=(25017877186361356689/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27600304518238935519/27610000000000000000 : ℝ)*(X 1 0+X 2 0)+(519871933093/276100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (27600304518238935519/27610000000000000000 : ℝ)) (alpha := (519871933093/276100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27600304518238935519/27610000000000000000 : ℝ)*(X 0 1+X 2 1)+(519871933093/276100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (27600304518238935519/27610000000000000000 : ℝ)) (alpha := (519871933093/276100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27600304518238935519/27610000000000000000 : ℝ)*(X 0 2+X 1 2)+(519871933093/276100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (27600304518238935519/27610000000000000000 : ℝ)) (alpha := (519871933093/276100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2195905739/10000000000 : ℝ)*X 0 0+(674270621/1250000000 : ℝ)*X 0 1+(1028254/1953125 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213798493/400000000 : ℝ)*X 1 0+(-8834407/39062500 : ℝ)*X 1 1+(1052932219/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213798501/400000000 : ℝ)*X 2 0+(1316165141/2500000000 : ℝ)*X 2 1+(-565402157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34165559/78125000 : ℝ)*X 0 0+(1061938653/2500000000 : ℝ)*X 0 1+(900473939/2000000000 : ℝ)*X 0 2+(34165559/78125000 : ℝ)*X 1 0+(1061938653/2500000000 : ℝ)*X 1 1+(900473939/2000000000 : ℝ)*X 1 2+(34165559/78125000 : ℝ)*X 2 0+(1061938653/2500000000 : ℝ)*X 2 1+(900473939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1097955249/5000000000 : ℝ)*X 0 0+(1316246491/2500000000 : ℝ)*X 0 1+(5393838527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328075373/2500000000 : ℝ)*X 1 0+(-2132430981/10000000000 : ℝ)*X 1 1+(5393838527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312301493/10000000000 : ℝ)*X 2 0+(5393838527/10000000000 : ℝ)*X 2 1+(-106621549/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186600873/5000000000 : ℝ)*X 0 0+(900346179/2000000000 : ℝ)*X 0 1+(4248395437/10000000000 : ℝ)*X 0 2+(2186600873/5000000000 : ℝ)*X 1 0+(900346179/2000000000 : ℝ)*X 1 1+(4248395437/10000000000 : ℝ)*X 1 2+(2186600873/5000000000 : ℝ)*X 2 0+(900346179/2000000000 : ℝ)*X 2 1+(4248395437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (518950643043034735269903/784375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55574613/6250000000000 : ℝ)*(base19) + (221404999/12500000000000 : ℝ)*(base23) + (20208803/6250000000000 : ℝ)*(upper2) + (72597191/50000000000000 : ℝ)*(upper3) + (36404375761523/625000000000 : ℝ)*(major0) + (36404375761523/625000000000 : ℝ)*(major1) + (36404375761523/625000000000 : ℝ)*(major2) + (965226459387489/12500000000000 : ℝ)*(sp0) + (120654201632049/1562500000000 : ℝ)*(sp1) + (965233260621887/12500000000000 : ℝ)*(sp2) + (1963756535755507/50000000000000 : ℝ)*(sp3) + (7264818129/12500000000000 : ℝ)*(sp4) + (1937429857/100000000000000 : ℝ)*(sp6) + (17356477713/100000000000000 : ℝ)*(sp7) + (490941303498591/12500000000000 : ℝ)*(f.failure) + (482616862102809/6250000000000 : ℝ)*(f.sum) + (37477911273/125500000000000000000000000 : ℝ)*base65 + (7579722177923483/1568750000000000000000000000000 : ℝ)*base68 + (17586917368973483/1568750000000000000000000000000 : ℝ)*base70 + (9409415635479733/1568750000000000000000000000000 : ℝ)*base72 + (755333021427/251000000000000000000000000 : ℝ)*base73 + (8933423008323483/1568750000000000000000000000000 : ℝ)*base76 + (23337880497673483/1568750000000000000000000000000 : ℝ)*base78 + (10854960183354733/1568750000000000000000000000000 : ℝ)*base80 + (221638538771/50200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1388959/156250000000000000000 : ℝ)*base89 + (1388959/156250000000000000000 : ℝ)*base91 + (1388959/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2356418804119290381438076653/276100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1573760737/100000000000000 : ℝ)*(base19) + (68587677/4000000000000 : ℝ)*(base23) + (170608639/100000000000000 : ℝ)*(upper3) + (15796937/25000000000000 : ℝ)*(lower4) + (173381601/100000000000000 : ℝ)*(upper5) + (1170814151544529/20000000000000 : ℝ)*(major0) + (1170814151544529/20000000000000 : ℝ)*(major1) + (1170814151544529/20000000000000 : ℝ)*(major2) + (42909272907/100000000000000 : ℝ)*(sp1) + (23123630421/50000000000000 : ℝ)*(sp2) + (3880403255133883/50000000000000 : ℝ)*(sp4) + (3880381013617061/50000000000000 : ℝ)*(sp5) + (7760758548314999/100000000000000 : ℝ)*(sp6) + (78946694413779/2000000000000 : ℝ)*(sp7) + (78946694413779/2000000000000 : ℝ)*(f.failure) + (3880403255133883/50000000000000 : ℝ)*(f.sum) + (3161182436271/552200000000000000000000000 : ℝ)*base66 + (4077020914874874449/552200000000000000000000000000000 : ℝ)*base68 + (2049530318877525551/552200000000000000000000000000000 : ℝ)*base69 + (6295152446039874449/552200000000000000000000000000000 : ℝ)*base72 + (12657331814467/2761000000000000000000000000 : ℝ)*base74 + (1289675079818125551/552200000000000000000000000000000 : ℝ)*base75 + (3103326424607474449/552200000000000000000000000000000 : ℝ)*base78 + (9911215433086274449/552200000000000000000000000000000 : ℝ)*base80 + (4938086406197/2761000000000000000000000000 : ℝ)*base82 + (127171/25000000000000000000 : ℝ)*base89 + (127171/25000000000000000000 : ℝ)*base91 + (127171/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1082_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_s8_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195912337/10000000000 : ℝ)*x 0 + (1348517551/2500000000 : ℝ)*x 1 + (2632375527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195912337/10000000000 : ℝ)^8275 ≤ (266752527409/2000000000000 : ℝ)^6227 := by
    have hnat : (2195912337 : ℕ)^8275*2000000000000^6227 ≤ 266752527409^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195912337 10000000000 266752527409 2000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348517551/2500000000 : ℝ)^8275 ≤ (8805956872007/20000000000000 : ℝ)^6227 := by
    have hnat : (1348517551 : ℕ)^8275*20000000000000^6227 ≤ 8805956872007^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348517551 2500000000 8805956872007 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632375527/5000000000 : ℝ)^8275 ≤ (42632589251363/100000000000000 : ℝ)^6227 := by
    have hnat : (2632375527 : ℕ)^8275*100000000000000^6227 ≤ 42632589251363^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632375527 5000000000 42632589251363 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195912337/10000000000 : ℝ), (1348517551/2500000000 : ℝ), (2632375527/5000000000 : ℝ)] ![(266752527409/2000000000000 : ℝ), (8805956872007/20000000000000 : ℝ), (42632589251363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195912337/10000000000 : ℝ)|^8275 ≤ (266752527409/2000000000000 : ℝ)^6227
        have hw : |(-2195912337/10000000000 : ℝ)|=(2195912337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348517551/2500000000 : ℝ)|^8275 ≤ (8805956872007/20000000000000 : ℝ)^6227
        have hw : |(1348517551/2500000000 : ℝ)|=(1348517551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632375527/5000000000 : ℝ)|^8275 ≤ (42632589251363/100000000000000 : ℝ)^6227
        have hw : |(2632375527/5000000000 : ℝ)|=(2632375527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344938941/10000000000 : ℝ)*x 0 + (-2261520459/10000000000 : ℝ)*x 1 + (2632375521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344938941/10000000000 : ℝ)^8275 ≤ (10874411456183/25000000000000 : ℝ)^6227 := by
    have hnat : (5344938941 : ℕ)^8275*25000000000000^6227 ≤ 10874411456183^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344938941 10000000000 10874411456183 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261520459/10000000000 : ℝ)^8275 ≤ (6934882521273/50000000000000 : ℝ)^6227 := by
    have hnat : (2261520459 : ℕ)^8275*50000000000000^6227 ≤ 6934882521273^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261520459 10000000000 6934882521273 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632375521/5000000000 : ℝ)^8275 ≤ (42632589122231/100000000000000 : ℝ)^6227 := by
    have hnat : (2632375521 : ℕ)^8275*100000000000000^6227 ≤ 42632589122231^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632375521 5000000000 42632589122231 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344938941/10000000000 : ℝ), (-2261520459/10000000000 : ℝ), (2632375521/5000000000 : ℝ)] ![(10874411456183/25000000000000 : ℝ), (6934882521273/50000000000000 : ℝ), (42632589122231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344938941/10000000000 : ℝ)|^8275 ≤ (10874411456183/25000000000000 : ℝ)^6227
        have hw : |(5344938941/10000000000 : ℝ)|=(5344938941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2261520459/10000000000 : ℝ)|^8275 ≤ (6934882521273/50000000000000 : ℝ)^6227
        have hw : |(-2261520459/10000000000 : ℝ)|=(2261520459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632375521/5000000000 : ℝ)|^8275 ≤ (42632589122231/100000000000000 : ℝ)^6227
        have hw : |(2632375521/5000000000 : ℝ)|=(2632375521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336234739/2500000000 : ℝ)*x 0 + (5264751069/10000000000 : ℝ)*x 1 + (-565380101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336234739/2500000000 : ℝ)^8275 ≤ (5437205748369/12500000000000 : ℝ)^6227 := by
    have hnat : (1336234739 : ℕ)^8275*12500000000000^6227 ≤ 5437205748369^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336234739 2500000000 5437205748369 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264751069/10000000000 : ℝ)^8275 ≤ (21316294706389/50000000000000 : ℝ)^6227 := by
    have hnat : (5264751069 : ℕ)^8275*50000000000000^6227 ≤ 21316294706389^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264751069 10000000000 21316294706389 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565380101/2500000000 : ℝ)^8275 ≤ (1733720574287/12500000000000 : ℝ)^6227 := by
    have hnat : (565380101 : ℕ)^8275*12500000000000^6227 ≤ 1733720574287^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565380101 2500000000 1733720574287 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336234739/2500000000 : ℝ), (5264751069/10000000000 : ℝ), (-565380101/2500000000 : ℝ)] ![(5437205748369/12500000000000 : ℝ), (21316294706389/50000000000000 : ℝ), (1733720574287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336234739/2500000000 : ℝ)|^8275 ≤ (5437205748369/12500000000000 : ℝ)^6227
        have hw : |(1336234739/2500000000 : ℝ)|=(1336234739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264751069/10000000000 : ℝ)|^8275 ≤ (21316294706389/50000000000000 : ℝ)^6227
        have hw : |(5264751069/10000000000 : ℝ)|=(5264751069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565380101/2500000000 : ℝ)|^8275 ≤ (1733720574287/12500000000000 : ℝ)^6227
        have hw : |(-565380101/2500000000 : ℝ)|=(565380101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54664957/125000000 : ℝ)*x 0 + (2123967487/5000000000 : ℝ)*x 1 + (450218779/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54664957/125000000 : ℝ)^8275 ≤ (33316645403743/100000000000000 : ℝ)^6227 := by
    have hnat : (54664957 : ℕ)^8275*100000000000000^6227 ≤ 33316645403743^6227*125000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54664957 125000000 33316645403743 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123967487/5000000000 : ℝ)^8275 ≤ (32054511211477/100000000000000 : ℝ)^6227 := by
    have hnat : (2123967487 : ℕ)^8275*100000000000000^6227 ≤ 32054511211477^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123967487 5000000000 32054511211477 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450218779/1000000000 : ℝ)^8275 ≤ (8657210840119/25000000000000 : ℝ)^6227 := by
    have hnat : (450218779 : ℕ)^8275*25000000000000^6227 ≤ 8657210840119^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450218779 1000000000 8657210840119 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54664957/125000000 : ℝ), (2123967487/5000000000 : ℝ), (450218779/1000000000 : ℝ)] ![(33316645403743/100000000000000 : ℝ), (32054511211477/100000000000000 : ℝ), (8657210840119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54664957/125000000 : ℝ)|^8275 ≤ (33316645403743/100000000000000 : ℝ)^6227
        have hw : |(54664957/125000000 : ℝ)|=(54664957/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123967487/5000000000 : ℝ)|^8275 ≤ (32054511211477/100000000000000 : ℝ)^6227
        have hw : |(2123967487/5000000000 : ℝ)|=(2123967487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450218779/1000000000 : ℝ)|^8275 ≤ (8657210840119/25000000000000 : ℝ)^6227
        have hw : |(450218779/1000000000 : ℝ)|=(450218779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097958687/5000000000 : ℝ)*x 0 + (2632537593/5000000000 : ℝ)*x 1 + (2696872447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097958687/5000000000 : ℝ)^8275 ≤ (416802094577/3125000000000 : ℝ)^6227 := by
    have hnat : (1097958687 : ℕ)^8275*3125000000000^6227 ≤ 416802094577^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097958687 5000000000 416802094577 3125000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632537593/5000000000 : ℝ)^8275 ≤ (2131803863707/5000000000000 : ℝ)^6227 := by
    have hnat : (2632537593 : ℕ)^8275*5000000000000^6227 ≤ 2131803863707^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632537593 5000000000 2131803863707 5000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696872447/5000000000 : ℝ)^8275 ≤ (22013127840297/50000000000000 : ℝ)^6227 := by
    have hnat : (2696872447 : ℕ)^8275*50000000000000^6227 ≤ 22013127840297^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696872447 5000000000 22013127840297 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097958687/5000000000 : ℝ), (2632537593/5000000000 : ℝ), (2696872447/5000000000 : ℝ)] ![(416802094577/3125000000000 : ℝ), (2131803863707/5000000000000 : ℝ), (22013127840297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097958687/5000000000 : ℝ)|^8275 ≤ (416802094577/3125000000000 : ℝ)^6227
        have hw : |(-1097958687/5000000000 : ℝ)|=(1097958687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632537593/5000000000 : ℝ)|^8275 ≤ (2131803863707/5000000000000 : ℝ)^6227
        have hw : |(2632537593/5000000000 : ℝ)|=(2632537593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696872447/5000000000 : ℝ)|^8275 ≤ (22013127840297/50000000000000 : ℝ)^6227
        have hw : |(2696872447/5000000000 : ℝ)|=(2696872447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656162371/5000000000 : ℝ)*x 0 + (-2132526613/10000000000 : ℝ)*x 1 + (2696872457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656162371/5000000000 : ℝ)^8275 ≤ (1348290292091/3125000000000 : ℝ)^6227 := by
    have hnat : (2656162371 : ℕ)^8275*3125000000000^6227 ≤ 1348290292091^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656162371 5000000000 1348290292091 3125000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132526613/10000000000 : ℝ)^8275 ≤ (12828454737409/100000000000000 : ℝ)^6227 := by
    have hnat : (2132526613 : ℕ)^8275*100000000000000^6227 ≤ 12828454737409^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132526613 10000000000 12828454737409 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696872457/5000000000 : ℝ)^8275 ≤ (22013127948767/50000000000000 : ℝ)^6227 := by
    have hnat : (2696872457 : ℕ)^8275*50000000000000^6227 ≤ 22013127948767^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696872457 5000000000 22013127948767 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656162371/5000000000 : ℝ), (-2132526613/10000000000 : ℝ), (2696872457/5000000000 : ℝ)] ![(1348290292091/3125000000000 : ℝ), (12828454737409/100000000000000 : ℝ), (22013127948767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656162371/5000000000 : ℝ)|^8275 ≤ (1348290292091/3125000000000 : ℝ)^6227
        have hw : |(2656162371/5000000000 : ℝ)|=(2656162371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132526613/10000000000 : ℝ)|^8275 ≤ (12828454737409/100000000000000 : ℝ)^6227
        have hw : |(-2132526613/10000000000 : ℝ)|=(2132526613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696872457/5000000000 : ℝ)|^8275 ≤ (22013127948767/50000000000000 : ℝ)^6227
        have hw : |(2696872457/5000000000 : ℝ)|=(2696872457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312324891/10000000000 : ℝ)*x 0 + (674218123/1250000000 : ℝ)*x 1 + (-2132526317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312324891/10000000000 : ℝ)^8275 ≤ (21572645477527/50000000000000 : ℝ)^6227 := by
    have hnat : (5312324891 : ℕ)^8275*50000000000000^6227 ≤ 21572645477527^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312324891 10000000000 21572645477527 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674218123/1250000000 : ℝ)^8275 ≤ (22013128328413/50000000000000 : ℝ)^6227 := by
    have hnat : (674218123 : ℕ)^8275*50000000000000^6227 ≤ 22013128328413^6227*1250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674218123 1250000000 22013128328413 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132526317/10000000000 : ℝ)^8275 ≤ (12828452371159/100000000000000 : ℝ)^6227 := by
    have hnat : (2132526317 : ℕ)^8275*100000000000000^6227 ≤ 12828452371159^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132526317 10000000000 12828452371159 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312324891/10000000000 : ℝ), (674218123/1250000000 : ℝ), (-2132526317/10000000000 : ℝ)] ![(21572645477527/50000000000000 : ℝ), (22013128328413/50000000000000 : ℝ), (12828452371159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312324891/10000000000 : ℝ)|^8275 ≤ (21572645477527/50000000000000 : ℝ)^6227
        have hw : |(5312324891/10000000000 : ℝ)|=(5312324891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674218123/1250000000 : ℝ)|^8275 ≤ (22013128328413/50000000000000 : ℝ)^6227
        have hw : |(674218123/1250000000 : ℝ)|=(674218123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132526317/10000000000 : ℝ)|^8275 ≤ (12828452371159/100000000000000 : ℝ)^6227
        have hw : |(-2132526317/10000000000 : ℝ)|=(2132526317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s8_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437320659/1000000000 : ℝ)*x 0 + (4501550621/10000000000 : ℝ)*x 1 + (2124287143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437320659/1000000000 : ℝ)^8275 ≤ (3331674694733/10000000000000 : ℝ)^6227 := by
    have hnat : (437320659 : ℕ)^8275*10000000000000^6227 ≤ 3331674694733^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437320659 1000000000 3331674694733 10000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501550621/10000000000 : ℝ)^8275 ≤ (4327791356977/12500000000000 : ℝ)^6227 := by
    have hnat : (4501550621 : ℕ)^8275*12500000000000^6227 ≤ 4327791356977^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501550621 10000000000 4327791356977 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124287143/5000000000 : ℝ)^8275 ≤ (4007615273229/12500000000000 : ℝ)^6227 := by
    have hnat : (2124287143 : ℕ)^8275*12500000000000^6227 ≤ 4007615273229^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124287143 5000000000 4007615273229 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437320659/1000000000 : ℝ), (4501550621/10000000000 : ℝ), (2124287143/5000000000 : ℝ)] ![(3331674694733/10000000000000 : ℝ), (4327791356977/12500000000000 : ℝ), (4007615273229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437320659/1000000000 : ℝ)|^8275 ≤ (3331674694733/10000000000000 : ℝ)^6227
        have hw : |(437320659/1000000000 : ℝ)|=(437320659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501550621/10000000000 : ℝ)|^8275 ≤ (4327791356977/12500000000000 : ℝ)^6227
        have hw : |(4501550621/10000000000 : ℝ)|=(4501550621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124287143/5000000000 : ℝ)|^8275 ≤ (4007615273229/12500000000000 : ℝ)^6227
        have hw : |(2124287143/5000000000 : ℝ)|=(2124287143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5637/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14013/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (4137/1024 : ℝ) ≤ (7396341121347487/50000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^4137 ≤ (7396341121347487/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1409 : ℕ)^4137*50000000000000000000^1024 ≤ 7396341121347487^1024*12500^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 7396341121347487 50000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (7396341121347487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2803/20000 : ℝ) ^ (4137/1024 : ℝ) ≤ (35661761916467739/100000000000000000000 : ℝ) := by
    have hpowers : (2803/20000 : ℝ)^4137 ≤ (35661761916467739/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2803 : ℕ)^4137*100000000000000000000^1024 ≤ 35661761916467739^1024*20000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2803 20000 35661761916467739 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2803/20000 : ℝ)) (X := (35661761916467739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007396341121347487/25000000000000000000 : ℝ) ≤ (10000732222421659/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (25007396341121347487/25000000000000000000 : ℝ)^1024 ≤ (10000732222421659/10000000000000000 : ℝ)^4137 := by
      have hnat : (25007396341121347487 : ℕ)^1024*10000000000000000^4137 ≤ 10000732222421659^4137*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007396341121347487 25000000000000000000 10000732222421659 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000732222421659/10000000000000000 : ℝ)) (X := (25007396341121347487/25000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050454444159162713/100000000000000000000 : ℝ) ≤ (10001248623304717/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (100050454444159162713/100000000000000000000 : ℝ)^1024 ≤ (10001248623304717/10000000000000000 : ℝ)^4137 := by
      have hnat : (100050454444159162713 : ℕ)^1024*10000000000000000^4137 ≤ 10001248623304717^4137*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050454444159162713 100000000000000000000 10001248623304717 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001248623304717/10000000000000000 : ℝ)) (X := (100050454444159162713/100000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035661761916467739/50000000000000000000 : ℝ) ≤ (400070600967511/400000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50035661761916467739/50000000000000000000 : ℝ)^1024 ≤ (400070600967511/400000000000000 : ℝ)^4137 := by
      have hnat : (50035661761916467739 : ℕ)^1024*400000000000000^4137 ≤ 400070600967511^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035661761916467739 50000000000000000000 400070600967511 400000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400070600967511/400000000000000 : ℝ)) (X := (50035661761916467739/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7396341121347487/50000000000000000000 : ℝ) ≤ ((5484073348918990217/5486000000000000000 : ℝ)+2*(258200441529/137150000000000 : ℝ)*(1409/12500 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (5484073348918990217/5486000000000000000 : ℝ)+2*(258200441529/137150000000000 : ℝ)*(1409/12500 : ℝ)=(10000732222421659/10000000000000000 : ℝ) by norm_num, show 1+2*(7396341121347487/50000000000000000000 : ℝ)=(25007396341121347487/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35661761916467739/100000000000000000000 : ℝ)+(7396341121347487/50000000000000000000 : ℝ) ≤ ((5484073348918990217/5486000000000000000 : ℝ)+(258200441529/137150000000000 : ℝ)*((2803/20000 : ℝ)+(1409/12500 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (5484073348918990217/5486000000000000000 : ℝ)+(258200441529/137150000000000 : ℝ)*((2803/20000 : ℝ)+(1409/12500 : ℝ))=(10001248623304717/10000000000000000 : ℝ) by norm_num, show 1+(35661761916467739/100000000000000000000 : ℝ)+(7396341121347487/50000000000000000000 : ℝ)=(100050454444159162713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35661761916467739/100000000000000000000 : ℝ) ≤ ((5484073348918990217/5486000000000000000 : ℝ)+2*(258200441529/137150000000000 : ℝ)*(2803/20000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (5484073348918990217/5486000000000000000 : ℝ)+2*(258200441529/137150000000000 : ℝ)*(2803/20000 : ℝ)=(400070600967511/400000000000000 : ℝ) by norm_num, show 1+2*(35661761916467739/100000000000000000000 : ℝ)=(50035661761916467739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5484073348918990217/5486000000000000000 : ℝ)*(X 1 0+X 2 0)+(258200441529/137150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (5484073348918990217/5486000000000000000 : ℝ)) (alpha := (258200441529/137150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5484073348918990217/5486000000000000000 : ℝ)*(X 0 1+X 2 1)+(258200441529/137150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (5484073348918990217/5486000000000000000 : ℝ)) (alpha := (258200441529/137150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5484073348918990217/5486000000000000000 : ℝ)*(X 0 2+X 1 2)+(258200441529/137150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (5484073348918990217/5486000000000000000 : ℝ)) (alpha := (258200441529/137150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2195912337/10000000000 : ℝ)*X 0 0+(1348517551/2500000000 : ℝ)*X 0 1+(2632375527/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344938941/10000000000 : ℝ)*X 1 0+(-2261520459/10000000000 : ℝ)*X 1 1+(2632375521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336234739/2500000000 : ℝ)*X 2 0+(5264751069/10000000000 : ℝ)*X 2 1+(-565380101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54664957/125000000 : ℝ)*X 0 0+(2123967487/5000000000 : ℝ)*X 0 1+(450218779/1000000000 : ℝ)*X 0 2+(54664957/125000000 : ℝ)*X 1 0+(2123967487/5000000000 : ℝ)*X 1 1+(450218779/1000000000 : ℝ)*X 1 2+(54664957/125000000 : ℝ)*X 2 0+(2123967487/5000000000 : ℝ)*X 2 1+(450218779/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1097958687/5000000000 : ℝ)*X 0 0+(2632537593/5000000000 : ℝ)*X 0 1+(2696872447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656162371/5000000000 : ℝ)*X 1 0+(-2132526613/10000000000 : ℝ)*X 1 1+(2696872457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312324891/10000000000 : ℝ)*X 2 0+(674218123/1250000000 : ℝ)*X 2 1+(-2132526317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437320659/1000000000 : ℝ)*X 0 0+(4501550621/10000000000 : ℝ)*X 0 1+(2124287143/5000000000 : ℝ)*X 0 2+(437320659/1000000000 : ℝ)*X 1 0+(4501550621/10000000000 : ℝ)*X 1 1+(2124287143/5000000000 : ℝ)*X 1 2+(437320659/1000000000 : ℝ)*X 2 0+(4501550621/10000000000 : ℝ)*X 2 1+(2124287143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (356985948140796996838289349/137150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13318633/2500000000000 : ℝ)*(base19) + (242322131/50000000000000 : ℝ)*(base23) + (18654489/50000000000000 : ℝ)*(lower2) + (35053911/100000000000000 : ℝ)*(upper3) + (74548607/100000000000000 : ℝ)*(upper5) + (5832971915909999/100000000000000 : ℝ)*(major0) + (5832971915909999/100000000000000 : ℝ)*(major1) + (5832971915909999/100000000000000 : ℝ)*(major2) + (966602452336693/12500000000000 : ℝ)*(sp0) + (386641760284963/5000000000000 : ℝ)*(sp1) + (7732835253800317/100000000000000 : ℝ)*(sp2) + (196655034826117/5000000000000 : ℝ)*(sp3) + (4029937759/25000000000000 : ℝ)*(sp4) + (913761271/12500000000000 : ℝ)*(sp7) + (983277001653127/25000000000000 : ℝ)*(f.failure) + (7732835738444579/100000000000000 : ℝ)*(f.sum) + (6010014831289/6857500000000000000000000000 : ℝ)*base66 + (15913912035503680217/548600000000000000000000000000000 : ℝ)*base68 + (2912303272836480217/548600000000000000000000000000000 : ℝ)*base70 + (20737791345675680217/548600000000000000000000000000000 : ℝ)*base72 + (4976914763939/6857500000000000000000000000 : ℝ)*base74 + (1030837528132480217/548600000000000000000000000000000 : ℝ)*base76 + (400005080273119783/548600000000000000000000000000000 : ℝ)*base77 + (7135946229572280217/548600000000000000000000000000000 : ℝ)*base80 + (15851040628879/6857500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2454223/312500000000000000000 : ℝ)*base89 + (2454223/312500000000000000000 : ℝ)*base91 + (2454223/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1027313363670656680738927791/137150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1515408361/100000000000000 : ℝ)*(base19) + (431707721/20000000000000 : ℝ)*(base23) + (461289149/100000000000000 : ℝ)*(lower1) + (126145093/50000000000000 : ℝ)*(upper3) + (123306537/100000000000000 : ℝ)*(lower4) + (127584729/100000000000000 : ℝ)*(upper5) + (2931180023176141/50000000000000 : ℝ)*(major0) + (2931180023176141/50000000000000 : ℝ)*(major1) + (2931180023176141/50000000000000 : ℝ)*(major2) + (31442080517/100000000000000 : ℝ)*(sp2) + (7771795747321377/100000000000000 : ℝ)*(sp4) + (971474278989127/12500000000000 : ℝ)*(sp5) + (1554352429340451/20000000000000 : ℝ)*(sp6) + (1976462047850977/50000000000000 : ℝ)*(sp7) + (1976462047850977/50000000000000 : ℝ)*(f.failure) + (7771795747321377/100000000000000 : ℝ)*(f.sum) + (54696336818013/6857500000000000000000000000 : ℝ)*base65 + (1265841021519572597/274300000000000000000000000000000 : ℝ)*base67 + (1553246870602227403/274300000000000000000000000000000 : ℝ)*base70 + (9365877258957227403/274300000000000000000000000000000 : ℝ)*base72 + (29009885241383/6857500000000000000000000000 : ℝ)*base73 + (11200268585642027403/274300000000000000000000000000000 : ℝ)*base76 + (257771580477272597/274300000000000000000000000000000 : ℝ)*base77 + (5728126100675727403/274300000000000000000000000000000 : ℝ)*base80 + (3314441189541/13715000000000000000000000000 : ℝ)*base81 + (6176127/625000000000000000000 : ℝ)*base90 + (6176127/625000000000000000000 : ℝ)*base92 + (6176127/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1082_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1082_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1082_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1082_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1082_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
