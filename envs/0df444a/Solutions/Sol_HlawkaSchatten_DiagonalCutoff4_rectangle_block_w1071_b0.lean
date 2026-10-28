-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:57.798795+00:00
-- url     : https://prove2.me/submissions/d033ac7e-3cdc-42a4-a907-fc4f05a3eb8f

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
theorem support_rectangle_w1071_s0_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-957243061/5000000000 : ℝ)*x 0 + (6070886029/10000000000 : ℝ)*x 1 + (4771428361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957243061/5000000000 : ℝ)^1033 ≤ (444189498899/4000000000000 : ℝ)^777 := by
    have hnat : (957243061 : ℕ)^1033*4000000000000^777 ≤ 444189498899^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957243061 5000000000 444189498899 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6070886029/10000000000 : ℝ)^1033 ≤ (25751921625541/50000000000000 : ℝ)^777 := by
    have hnat : (6070886029 : ℕ)^1033*50000000000000^777 ≤ 25751921625541^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6070886029 10000000000 25751921625541 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4771428361/10000000000 : ℝ)^1033 ≤ (37391419261649/100000000000000 : ℝ)^777 := by
    have hnat : (4771428361 : ℕ)^1033*100000000000000^777 ≤ 37391419261649^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771428361 10000000000 37391419261649 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-957243061/5000000000 : ℝ), (6070886029/10000000000 : ℝ), (4771428361/10000000000 : ℝ)] ![(444189498899/4000000000000 : ℝ), (25751921625541/50000000000000 : ℝ), (37391419261649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-957243061/5000000000 : ℝ)|^1033 ≤ (444189498899/4000000000000 : ℝ)^777
        have hw : |(-957243061/5000000000 : ℝ)|=(957243061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6070886029/10000000000 : ℝ)|^1033 ≤ (25751921625541/50000000000000 : ℝ)^777
        have hw : |(6070886029/10000000000 : ℝ)|=(6070886029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4771428361/10000000000 : ℝ)|^1033 ≤ (37391419261649/100000000000000 : ℝ)^777
        have hw : |(4771428361/10000000000 : ℝ)|=(4771428361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5520790171/10000000000 : ℝ)*x 0 + (-1331156913/5000000000 : ℝ)*x 1 + (298214303/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520790171/10000000000 : ℝ)^1033 ≤ (45393930577233/100000000000000 : ℝ)^777 := by
    have hnat : (5520790171 : ℕ)^1033*100000000000000^777 ≤ 45393930577233^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520790171 10000000000 45393930577233 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331156913/5000000000 : ℝ)^1033 ≤ (8607322537359/50000000000000 : ℝ)^777 := by
    have hnat : (1331156913 : ℕ)^1033*50000000000000^777 ≤ 8607322537359^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331156913 5000000000 8607322537359 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298214303/625000000 : ℝ)^1033 ≤ (37391424335431/100000000000000 : ℝ)^777 := by
    have hnat : (298214303 : ℕ)^1033*100000000000000^777 ≤ 37391424335431^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298214303 625000000 37391424335431 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520790171/10000000000 : ℝ), (-1331156913/5000000000 : ℝ), (298214303/625000000 : ℝ)] ![(45393930577233/100000000000000 : ℝ), (8607322537359/50000000000000 : ℝ), (37391424335431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520790171/10000000000 : ℝ)|^1033 ≤ (45393930577233/100000000000000 : ℝ)^777
        have hw : |(5520790171/10000000000 : ℝ)|=(5520790171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1331156913/5000000000 : ℝ)|^1033 ≤ (8607322537359/50000000000000 : ℝ)^777
        have hw : |(-1331156913/5000000000 : ℝ)|=(1331156913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298214303/625000000 : ℝ)|^1033 ≤ (37391424335431/100000000000000 : ℝ)^777
        have hw : |(298214303/625000000 : ℝ)|=(298214303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (690099357/1250000000 : ℝ)*x 0 + (2385712883/5000000000 : ℝ)*x 1 + (-2662311603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690099357/1250000000 : ℝ)^1033 ≤ (45393981790857/100000000000000 : ℝ)^777 := by
    have hnat : (690099357 : ℕ)^1033*100000000000000^777 ≤ 45393981790857^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690099357 1250000000 45393981790857 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385712883/5000000000 : ℝ)^1033 ≤ (3739139222579/10000000000000 : ℝ)^777 := by
    have hnat : (2385712883 : ℕ)^1033*10000000000000^777 ≤ 3739139222579^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385712883 5000000000 3739139222579 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2662311603/10000000000 : ℝ)^1033 ≤ (17214625964857/100000000000000 : ℝ)^777 := by
    have hnat : (2662311603 : ℕ)^1033*100000000000000^777 ≤ 17214625964857^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2662311603 10000000000 17214625964857 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690099357/1250000000 : ℝ), (2385712883/5000000000 : ℝ), (-2662311603/10000000000 : ℝ)] ![(45393981790857/100000000000000 : ℝ), (3739139222579/10000000000000 : ℝ), (17214625964857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690099357/1250000000 : ℝ)|^1033 ≤ (45393981790857/100000000000000 : ℝ)^777
        have hw : |(690099357/1250000000 : ℝ)|=(690099357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2385712883/5000000000 : ℝ)|^1033 ≤ (3739139222579/10000000000000 : ℝ)^777
        have hw : |(2385712883/5000000000 : ℝ)|=(2385712883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2662311603/10000000000 : ℝ)|^1033 ≤ (17214625964857/100000000000000 : ℝ)^777
        have hw : |(-2662311603/10000000000 : ℝ)|=(2662311603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4206796909/10000000000 : ℝ)*x 0 + (1562299697/5000000000 : ℝ)*x 1 + (5673886313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206796909/10000000000 : ℝ)^1033 ≤ (6325341558801/20000000000000 : ℝ)^777 := by
    have hnat : (4206796909 : ℕ)^1033*20000000000000^777 ≤ 6325341558801^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206796909 10000000000 6325341558801 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562299697/5000000000 : ℝ)^1033 ≤ (21298207796239/100000000000000 : ℝ)^777 := by
    have hnat : (1562299697 : ℕ)^1033*100000000000000^777 ≤ 21298207796239^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562299697 5000000000 21298207796239 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673886313/10000000000 : ℝ)^1033 ≤ (1471096387603/3125000000000 : ℝ)^777 := by
    have hnat : (5673886313 : ℕ)^1033*3125000000000^777 ≤ 1471096387603^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673886313 10000000000 1471096387603 3125000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206796909/10000000000 : ℝ), (1562299697/5000000000 : ℝ), (5673886313/10000000000 : ℝ)] ![(6325341558801/20000000000000 : ℝ), (21298207796239/100000000000000 : ℝ), (1471096387603/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206796909/10000000000 : ℝ)|^1033 ≤ (6325341558801/20000000000000 : ℝ)^777
        have hw : |(4206796909/10000000000 : ℝ)|=(4206796909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562299697/5000000000 : ℝ)|^1033 ≤ (21298207796239/100000000000000 : ℝ)^777
        have hw : |(1562299697/5000000000 : ℝ)|=(1562299697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673886313/10000000000 : ℝ)|^1033 ≤ (1471096387603/3125000000000 : ℝ)^777
        have hw : |(5673886313/10000000000 : ℝ)|=(5673886313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-959922597/5000000000 : ℝ)*x 0 + (480497857/1000000000 : ℝ)*x 1 + (3018080513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959922597/5000000000 : ℝ)^1033 ≤ (2786520667337/25000000000000 : ℝ)^777 := by
    have hnat : (959922597 : ℕ)^1033*25000000000000^777 ≤ 2786520667337^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959922597 5000000000 2786520667337 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480497857/1000000000 : ℝ)^1033 ≤ (18870682237211/50000000000000 : ℝ)^777 := by
    have hnat : (480497857 : ℕ)^1033*50000000000000^777 ≤ 18870682237211^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480497857 1000000000 18870682237211 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3018080513/5000000000 : ℝ)^1033 ≤ (10222510567439/20000000000000 : ℝ)^777 := by
    have hnat : (3018080513 : ℕ)^1033*20000000000000^777 ≤ 10222510567439^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018080513 5000000000 10222510567439 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959922597/5000000000 : ℝ), (480497857/1000000000 : ℝ), (3018080513/5000000000 : ℝ)] ![(2786520667337/25000000000000 : ℝ), (18870682237211/50000000000000 : ℝ), (10222510567439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959922597/5000000000 : ℝ)|^1033 ≤ (2786520667337/25000000000000 : ℝ)^777
        have hw : |(-959922597/5000000000 : ℝ)|=(959922597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(480497857/1000000000 : ℝ)|^1033 ≤ (18870682237211/50000000000000 : ℝ)^777
        have hw : |(480497857/1000000000 : ℝ)|=(480497857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3018080513/5000000000 : ℝ)|^1033 ≤ (10222510567439/20000000000000 : ℝ)^777
        have hw : |(3018080513/5000000000 : ℝ)|=(3018080513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5168070707/10000000000 : ℝ)*x 0 + (-1397583643/10000000000 : ℝ)*x 1 + (377259929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168070707/10000000000 : ℝ)^1033 ≤ (20789694463371/50000000000000 : ℝ)^777 := by
    have hnat : (5168070707 : ℕ)^1033*50000000000000^777 ≤ 20789694463371^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168070707 10000000000 20789694463371 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397583643/10000000000 : ℝ)^1033 ≤ (3654041280887/50000000000000 : ℝ)^777 := by
    have hnat : (1397583643 : ℕ)^1033*50000000000000^777 ≤ 3654041280887^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397583643 10000000000 3654041280887 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377259929/625000000 : ℝ)^1033 ≤ (51112528498251/100000000000000 : ℝ)^777 := by
    have hnat : (377259929 : ℕ)^1033*100000000000000^777 ≤ 51112528498251^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377259929 625000000 51112528498251 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168070707/10000000000 : ℝ), (-1397583643/10000000000 : ℝ), (377259929/625000000 : ℝ)] ![(20789694463371/50000000000000 : ℝ), (3654041280887/50000000000000 : ℝ), (51112528498251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168070707/10000000000 : ℝ)|^1033 ≤ (20789694463371/50000000000000 : ℝ)^777
        have hw : |(5168070707/10000000000 : ℝ)|=(5168070707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1397583643/10000000000 : ℝ)|^1033 ≤ (3654041280887/50000000000000 : ℝ)^777
        have hw : |(-1397583643/10000000000 : ℝ)|=(1397583643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377259929/625000000 : ℝ)|^1033 ≤ (51112528498251/100000000000000 : ℝ)^777
        have hw : |(377259929/625000000 : ℝ)|=(377259929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5168070669/10000000000 : ℝ)*x 0 + (6036160311/10000000000 : ℝ)*x 1 + (-698790679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168070669/10000000000 : ℝ)^1033 ≤ (41579388520287/100000000000000 : ℝ)^777 := by
    have hnat : (5168070669 : ℕ)^1033*100000000000000^777 ≤ 41579388520287^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168070669 10000000000 41579388520287 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036160311/10000000000 : ℝ)^1033 ≤ (25556272394003/50000000000000 : ℝ)^777 := by
    have hnat : (6036160311 : ℕ)^1033*50000000000000^777 ≤ 25556272394003^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036160311 10000000000 25556272394003 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (698790679/5000000000 : ℝ)^1033 ≤ (1461613335327/20000000000000 : ℝ)^777 := by
    have hnat : (698790679 : ℕ)^1033*20000000000000^777 ≤ 1461613335327^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698790679 5000000000 1461613335327 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168070669/10000000000 : ℝ), (6036160311/10000000000 : ℝ), (-698790679/5000000000 : ℝ)] ![(41579388520287/100000000000000 : ℝ), (25556272394003/50000000000000 : ℝ), (1461613335327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168070669/10000000000 : ℝ)|^1033 ≤ (41579388520287/100000000000000 : ℝ)^777
        have hw : |(5168070669/10000000000 : ℝ)|=(5168070669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036160311/10000000000 : ℝ)|^1033 ≤ (25556272394003/50000000000000 : ℝ)^777
        have hw : |(6036160311/10000000000 : ℝ)|=(6036160311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-698790679/5000000000 : ℝ)|^1033 ≤ (1461613335327/20000000000000 : ℝ)^777
        have hw : |(-698790679/5000000000 : ℝ)|=(698790679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s0_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4217306169/10000000000 : ℝ)*x 0 + (5608063051/10000000000 : ℝ)*x 1 + (3192726497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217306169/10000000000 : ℝ)^1033 ≤ (31731790796057/100000000000000 : ℝ)^777 := by
    have hnat : (4217306169 : ℕ)^1033*100000000000000^777 ≤ 31731790796057^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217306169 10000000000 31731790796057 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608063051/10000000000 : ℝ)^1033 ≤ (11587605290603/25000000000000 : ℝ)^777 := by
    have hnat : (5608063051 : ℕ)^1033*25000000000000^777 ≤ 11587605290603^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608063051 10000000000 11587605290603 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192726497/10000000000 : ℝ)^1033 ≤ (2191778801869/10000000000000 : ℝ)^777 := by
    have hnat : (3192726497 : ℕ)^1033*10000000000000^777 ≤ 2191778801869^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192726497 10000000000 2191778801869 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217306169/10000000000 : ℝ), (5608063051/10000000000 : ℝ), (3192726497/10000000000 : ℝ)] ![(31731790796057/100000000000000 : ℝ), (11587605290603/25000000000000 : ℝ), (2191778801869/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217306169/10000000000 : ℝ)|^1033 ≤ (31731790796057/100000000000000 : ℝ)^777
        have hw : |(4217306169/10000000000 : ℝ)|=(4217306169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608063051/10000000000 : ℝ)|^1033 ≤ (11587605290603/25000000000000 : ℝ)^777
        have hw : |(5608063051/10000000000 : ℝ)|=(5608063051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192726497/10000000000 : ℝ)|^1033 ≤ (2191778801869/10000000000000 : ℝ)^777
        have hw : |(3192726497/10000000000 : ℝ)|=(3192726497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (59/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/10000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8263/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8263 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8263*1^2048 ≤ 0^2048*1^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8263/2048 : ℝ) ≤ (2479957244811563973/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8263 ≤ (2479957244811563973/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8263*100000000000000000000^2048 ≤ 2479957244811563973^2048*5^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2479957244811563973 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2479957244811563973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8263 := by
      have hnat : (1 : ℕ)^2048*1^8263 ≤ 1^8263*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102479957244811563973/100000000000000000000 : ℝ) ≤ (10060901105082519/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (102479957244811563973/100000000000000000000 : ℝ)^2048 ≤ (10060901105082519/10000000000000000 : ℝ)^8263 := by
      have hnat : (102479957244811563973 : ℕ)^2048*10000000000000000^8263 ≤ 10060901105082519^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102479957244811563973 100000000000000000000 10060901105082519 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060901105082519/10000000000000000 : ℝ)) (X := (102479957244811563973/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52479957244811563973/50000000000000000000 : ℝ) ≤ (5060901105082519/5000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (52479957244811563973/50000000000000000000 : ℝ)^2048 ≤ (5060901105082519/5000000000000000 : ℝ)^8263 := by
      have hnat : (52479957244811563973 : ℕ)^2048*5000000000000000^8263 ≤ 5060901105082519^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52479957244811563973 50000000000000000000 5060901105082519 5000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060901105082519/5000000000000000 : ℝ)) (X := (52479957244811563973/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60901105082519/4000000000000000 : ℝ)*(0 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60901105082519/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2479957244811563973/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60901105082519/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (1 : ℝ)+(60901105082519/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060901105082519/10000000000000000 : ℝ) by norm_num, show 1+(2479957244811563973/100000000000000000000 : ℝ)+(0 : ℝ)=(102479957244811563973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2479957244811563973/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60901105082519/4000000000000000 : ℝ)*(2/5 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60901105082519/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060901105082519/5000000000000000 : ℝ) by norm_num, show 1+2*(2479957244811563973/100000000000000000000 : ℝ)=(52479957244811563973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60901105082519/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60901105082519/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60901105082519/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60901105082519/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60901105082519/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60901105082519/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-957243061/5000000000 : ℝ)*X 0 0+(6070886029/10000000000 : ℝ)*X 0 1+(4771428361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520790171/10000000000 : ℝ)*X 1 0+(-1331156913/5000000000 : ℝ)*X 1 1+(298214303/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((690099357/1250000000 : ℝ)*X 2 0+(2385712883/5000000000 : ℝ)*X 2 1+(-2662311603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206796909/10000000000 : ℝ)*X 0 0+(1562299697/5000000000 : ℝ)*X 0 1+(5673886313/10000000000 : ℝ)*X 0 2+(4206796909/10000000000 : ℝ)*X 1 0+(1562299697/5000000000 : ℝ)*X 1 1+(5673886313/10000000000 : ℝ)*X 1 2+(4206796909/10000000000 : ℝ)*X 2 0+(1562299697/5000000000 : ℝ)*X 2 1+(5673886313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-959922597/5000000000 : ℝ)*X 0 0+(480497857/1000000000 : ℝ)*X 0 1+(3018080513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168070707/10000000000 : ℝ)*X 1 0+(-1397583643/10000000000 : ℝ)*X 1 1+(377259929/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168070669/10000000000 : ℝ)*X 2 0+(6036160311/10000000000 : ℝ)*X 2 1+(-698790679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4217306169/10000000000 : ℝ)*X 0 0+(5608063051/10000000000 : ℝ)*X 0 1+(3192726497/10000000000 : ℝ)*X 0 2+(4217306169/10000000000 : ℝ)*X 1 0+(5608063051/10000000000 : ℝ)*X 1 1+(3192726497/10000000000 : ℝ)*X 1 2+(4217306169/10000000000 : ℝ)*X 2 0+(5608063051/10000000000 : ℝ)*X 2 1+(3192726497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194912704053219826290807/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39778659/20000000000000 : ℝ)*(base1) + (126350103/50000000000000 : ℝ)*(base19) + (670036343/100000000000000 : ℝ)*(base23) + (58928119/25000000000000 : ℝ)*(base24) + (37026993/100000000000000 : ℝ)*(upper3) + (580909177377749/100000000000000 : ℝ)*(major0) + (580909177377749/100000000000000 : ℝ)*(major1) + (580909177377749/100000000000000 : ℝ)*(major2) + (192387841345321/25000000000000 : ℝ)*(sp0) + (384775605841387/50000000000000 : ℝ)*(sp1) + (769550558634161/100000000000000 : ℝ)*(sp2) + (6129160870767/1562500000000 : ℝ)*(sp3) + (297894991/100000000000000 : ℝ)*(sp4) + (33077923/10000000000000 : ℝ)*(sp7) + (392266825401613/100000000000000 : ℝ)*(f.failure) + (38477573219149/5000000000000 : ℝ)*(f.sum) + (298661687469731/200000000000000000000000000000 : ℝ)*base65 + (1284370323730269/400000000000000000000000000000 : ℝ)*base68 + (1317542221869731/400000000000000000000000000000 : ℝ)*base69 + (510891393069731/400000000000000000000000000000 : ℝ)*base71 + (159326663869731/200000000000000000000000000000 : ℝ)*base73 + (1049357002930269/400000000000000000000000000000 : ℝ)*base76 + (835293191730269/400000000000000000000000000000 : ℝ)*base78 + (1446037611730269/400000000000000000000000000000 : ℝ)*base80 + (685928725269731/200000000000000000000000000000 : ℝ)*base81 + (5864381/2000000000000000000000 : ℝ)*base90 + (5864381/2000000000000000000000 : ℝ)*base92 + (5864381/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209983053736069541446167/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1925096019/100000000000000 : ℝ)*(base19) + (2011148821/100000000000000 : ℝ)*(base23) + (241983/1000000000000 : ℝ)*(base39) + (188877801/50000000000000 : ℝ)*(base45) + (209718827/100000000000000 : ℝ)*(upper3) + (346217001/100000000000000 : ℝ)*(upper5) + (153280556501731/25000000000000 : ℝ)*(major0) + (153280556501731/25000000000000 : ℝ)*(major1) + (613122201808623/100000000000000 : ℝ)*(major2) + (125529091/12500000000000 : ℝ)*(sp2) + (812225023085159/100000000000000 : ℝ)*(sp4) + (40611154899457/5000000000000 : ℝ)*(sp5) + (812222031901909/100000000000000 : ℝ)*(sp6) + (16560764990119/4000000000000 : ℝ)*(sp7) + (16560764990119/4000000000000 : ℝ)*(f.failure) + (812225047283459/100000000000000 : ℝ)*(f.sum) + (191472425477107/400000000000000000000000000000 : ℝ)*base66 + (2418251718761337/400000000000000000000000000000 : ℝ)*base67 + (579134449559611/100000000000000000000000000000 : ℝ)*base70 + (1527509558761337/400000000000000000000000000000 : ℝ)*base71 + (125257535877107/400000000000000000000000000000 : ℝ)*base74 + (674326832159611/100000000000000000000000000000 : ℝ)*base76 + (987969014940389/100000000000000000000000000000 : ℝ)*base77 + (1611511714140389/100000000000000000000000000000 : ℝ)*base79 + (524061437109611/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (280503/80000000000000000000 : ℝ)*base90 + (280503/80000000000000000000 : ℝ)*base92 + (519497/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1071_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (59/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_s1_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-531064129/2500000000 : ℝ)*x 0 + (5720926033/10000000000 : ℝ)*x 1 + (1246763469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531064129/2500000000 : ℝ)^1033 ≤ (3187720808007/25000000000000 : ℝ)^777 := by
    have hnat : (531064129 : ℕ)^1033*25000000000000^777 ≤ 3187720808007^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531064129 2500000000 3187720808007 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720926033/10000000000 : ℝ)^1033 ≤ (47594656895527/100000000000000 : ℝ)^777 := by
    have hnat : (5720926033 : ℕ)^1033*100000000000000^777 ≤ 47594656895527^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720926033 10000000000 47594656895527 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1246763469/2500000000 : ℝ)^1033 ≤ (9913614963401/25000000000000 : ℝ)^777 := by
    have hnat : (1246763469 : ℕ)^1033*25000000000000^777 ≤ 9913614963401^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246763469 2500000000 9913614963401 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531064129/2500000000 : ℝ), (5720926033/10000000000 : ℝ), (1246763469/2500000000 : ℝ)] ![(3187720808007/25000000000000 : ℝ), (47594656895527/100000000000000 : ℝ), (9913614963401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531064129/2500000000 : ℝ)|^1033 ≤ (3187720808007/25000000000000 : ℝ)^777
        have hw : |(-531064129/2500000000 : ℝ)|=(531064129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720926033/10000000000 : ℝ)|^1033 ≤ (47594656895527/100000000000000 : ℝ)^777
        have hw : |(5720926033/10000000000 : ℝ)|=(5720926033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1246763469/2500000000 : ℝ)|^1033 ≤ (9913614963401/25000000000000 : ℝ)^777
        have hw : |(1246763469/2500000000 : ℝ)|=(1246763469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (542303827/1000000000 : ℝ)*x 0 + (-39402543/156250000 : ℝ)*x 1 + (997410837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542303827/1000000000 : ℝ)^1033 ≤ (5541061818909/12500000000000 : ℝ)^777 := by
    have hnat : (542303827 : ℕ)^1033*12500000000000^777 ≤ 5541061818909^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542303827 1000000000 5541061818909 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39402543/156250000 : ℝ)^1033 ≤ (16017042322921/100000000000000 : ℝ)^777 := by
    have hnat : (39402543 : ℕ)^1033*100000000000000^777 ≤ 16017042322921^777*156250000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39402543 156250000 16017042322921 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997410837/2000000000 : ℝ)^1033 ≤ (39654463120127/100000000000000 : ℝ)^777 := by
    have hnat : (997410837 : ℕ)^1033*100000000000000^777 ≤ 39654463120127^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997410837 2000000000 39654463120127 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542303827/1000000000 : ℝ), (-39402543/156250000 : ℝ), (997410837/2000000000 : ℝ)] ![(5541061818909/12500000000000 : ℝ), (16017042322921/100000000000000 : ℝ), (39654463120127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542303827/1000000000 : ℝ)|^1033 ≤ (5541061818909/12500000000000 : ℝ)^777
        have hw : |(542303827/1000000000 : ℝ)|=(542303827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39402543/156250000 : ℝ)|^1033 ≤ (16017042322921/100000000000000 : ℝ)^777
        have hw : |(-39402543/156250000 : ℝ)|=(39402543/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(997410837/2000000000 : ℝ)|^1033 ≤ (39654463120127/100000000000000 : ℝ)^777
        have hw : |(997410837/2000000000 : ℝ)|=(997410837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2711519449/5000000000 : ℝ)*x 0 + (2493526743/5000000000 : ℝ)*x 1 + (-1260881409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711519449/5000000000 : ℝ)^1033 ≤ (8865700275181/20000000000000 : ℝ)^777 := by
    have hnat : (2711519449 : ℕ)^1033*20000000000000^777 ≤ 8865700275181^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711519449 5000000000 8865700275181 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493526743/5000000000 : ℝ)^1033 ≤ (39654455730807/100000000000000 : ℝ)^777 := by
    have hnat : (2493526743 : ℕ)^1033*100000000000000^777 ≤ 39654455730807^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493526743 5000000000 39654455730807 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260881409/5000000000 : ℝ)^1033 ≤ (16017042880237/100000000000000 : ℝ)^777 := by
    have hnat : (1260881409 : ℕ)^1033*100000000000000^777 ≤ 16017042880237^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260881409 5000000000 16017042880237 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711519449/5000000000 : ℝ), (2493526743/5000000000 : ℝ), (-1260881409/5000000000 : ℝ)] ![(8865700275181/20000000000000 : ℝ), (39654455730807/100000000000000 : ℝ), (16017042880237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711519449/5000000000 : ℝ)|^1033 ≤ (8865700275181/20000000000000 : ℝ)^777
        have hw : |(2711519449/5000000000 : ℝ)|=(2711519449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2493526743/5000000000 : ℝ)|^1033 ≤ (39654455730807/100000000000000 : ℝ)^777
        have hw : |(2493526743/5000000000 : ℝ)|=(2493526743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1260881409/5000000000 : ℝ)|^1033 ≤ (16017042880237/100000000000000 : ℝ)^777
        have hw : |(-1260881409/5000000000 : ℝ)|=(1260881409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4323387277/10000000000 : ℝ)*x 0 + (1831751401/5000000000 : ℝ)*x 1 + (1020643283/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323387277/10000000000 : ℝ)^1033 ≤ (16398656755173/50000000000000 : ℝ)^777 := by
    have hnat : (4323387277 : ℕ)^1033*50000000000000^777 ≤ 16398656755173^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323387277 10000000000 16398656755173 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831751401/5000000000 : ℝ)^1033 ≤ (1315777651361/5000000000000 : ℝ)^777 := by
    have hnat : (1831751401 : ℕ)^1033*5000000000000^777 ≤ 1315777651361^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831751401 5000000000 1315777651361 5000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020643283/2000000000 : ℝ)^1033 ≤ (40887133439783/100000000000000 : ℝ)^777 := by
    have hnat : (1020643283 : ℕ)^1033*100000000000000^777 ≤ 40887133439783^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020643283 2000000000 40887133439783 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323387277/10000000000 : ℝ), (1831751401/5000000000 : ℝ), (1020643283/2000000000 : ℝ)] ![(16398656755173/50000000000000 : ℝ), (1315777651361/5000000000000 : ℝ), (40887133439783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323387277/10000000000 : ℝ)|^1033 ≤ (16398656755173/50000000000000 : ℝ)^777
        have hw : |(4323387277/10000000000 : ℝ)|=(4323387277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1831751401/5000000000 : ℝ)|^1033 ≤ (1315777651361/5000000000000 : ℝ)^777
        have hw : |(1831751401/5000000000 : ℝ)|=(1831751401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1020643283/2000000000 : ℝ)|^1033 ≤ (40887133439783/100000000000000 : ℝ)^777
        have hw : |(1020643283/2000000000 : ℝ)|=(1020643283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-132823181/625000000 : ℝ)*x 0 + (2498674023/5000000000 : ℝ)*x 1 + (571042081/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132823181/625000000 : ℝ)^1033 ≤ (12758180665131/100000000000000 : ℝ)^777 := by
    have hnat : (132823181 : ℕ)^1033*100000000000000^777 ≤ 12758180665131^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132823181 625000000 12758180665131 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498674023/5000000000 : ℝ)^1033 ≤ (39763319320647/100000000000000 : ℝ)^777 := by
    have hnat : (2498674023 : ℕ)^1033*100000000000000^777 ≤ 39763319320647^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498674023 5000000000 39763319320647 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571042081/1000000000 : ℝ)^1033 ≤ (1899139999987/4000000000000 : ℝ)^777 := by
    have hnat : (571042081 : ℕ)^1033*4000000000000^777 ≤ 1899139999987^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571042081 1000000000 1899139999987 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132823181/625000000 : ℝ), (2498674023/5000000000 : ℝ), (571042081/1000000000 : ℝ)] ![(12758180665131/100000000000000 : ℝ), (39763319320647/100000000000000 : ℝ), (1899139999987/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132823181/625000000 : ℝ)|^1033 ≤ (12758180665131/100000000000000 : ℝ)^777
        have hw : |(-132823181/625000000 : ℝ)|=(132823181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498674023/5000000000 : ℝ)|^1033 ≤ (39763319320647/100000000000000 : ℝ)^777
        have hw : |(2498674023/5000000000 : ℝ)|=(2498674023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571042081/1000000000 : ℝ)|^1033 ≤ (1899139999987/4000000000000 : ℝ)^777
        have hw : |(571042081/1000000000 : ℝ)|=(571042081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (10225721/19531250 : ℝ)*x 0 + (-359678753/2000000000 : ℝ)*x 1 + (1142084533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10225721/19531250 : ℝ)^1033 ≤ (21151456868171/50000000000000 : ℝ)^777 := by
    have hnat : (10225721 : ℕ)^1033*50000000000000^777 ≤ 21151456868171^777*19531250^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10225721 19531250 21151456868171 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359678753/2000000000 : ℝ)^1033 ≤ (10218565748947/100000000000000 : ℝ)^777 := by
    have hnat : (359678753 : ℕ)^1033*100000000000000^777 ≤ 10218565748947^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359678753 2000000000 10218565748947 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142084533/2000000000 : ℝ)^1033 ≤ (47478520504313/100000000000000 : ℝ)^777 := by
    have hnat : (1142084533 : ℕ)^1033*100000000000000^777 ≤ 47478520504313^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142084533 2000000000 47478520504313 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10225721/19531250 : ℝ), (-359678753/2000000000 : ℝ), (1142084533/2000000000 : ℝ)] ![(21151456868171/50000000000000 : ℝ), (10218565748947/100000000000000 : ℝ), (47478520504313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10225721/19531250 : ℝ)|^1033 ≤ (21151456868171/50000000000000 : ℝ)^777
        have hw : |(10225721/19531250 : ℝ)|=(10225721/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359678753/2000000000 : ℝ)|^1033 ≤ (10218565748947/100000000000000 : ℝ)^777
        have hw : |(-359678753/2000000000 : ℝ)|=(359678753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142084533/2000000000 : ℝ)|^1033 ≤ (47478520504313/100000000000000 : ℝ)^777
        have hw : |(1142084533/2000000000 : ℝ)|=(1142084533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1047113419/2000000000 : ℝ)*x 0 + (5710424943/10000000000 : ℝ)*x 1 + (-449598339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047113419/2000000000 : ℝ)^1033 ≤ (21151445820011/50000000000000 : ℝ)^777 := by
    have hnat : (1047113419 : ℕ)^1033*50000000000000^777 ≤ 21151445820011^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047113419 2000000000 21151445820011 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5710424943/10000000000 : ℝ)^1033 ≤ (11869636421169/25000000000000 : ℝ)^777 := by
    have hnat : (5710424943 : ℕ)^1033*25000000000000^777 ≤ 11869636421169^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710424943 10000000000 11869636421169 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449598339/2500000000 : ℝ)^1033 ≤ (2554640664827/25000000000000 : ℝ)^777 := by
    have hnat : (449598339 : ℕ)^1033*25000000000000^777 ≤ 2554640664827^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449598339 2500000000 2554640664827 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047113419/2000000000 : ℝ), (5710424943/10000000000 : ℝ), (-449598339/2500000000 : ℝ)] ![(21151445820011/50000000000000 : ℝ), (11869636421169/25000000000000 : ℝ), (2554640664827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047113419/2000000000 : ℝ)|^1033 ≤ (21151445820011/50000000000000 : ℝ)^777
        have hw : |(1047113419/2000000000 : ℝ)|=(1047113419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5710424943/10000000000 : ℝ)|^1033 ≤ (11869636421169/25000000000000 : ℝ)^777
        have hw : |(5710424943/10000000000 : ℝ)|=(5710424943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449598339/2500000000 : ℝ)|^1033 ≤ (2554640664827/25000000000000 : ℝ)^777
        have hw : |(-449598339/2500000000 : ℝ)|=(449598339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4325176867/10000000000 : ℝ)*x 0 + (635377227/1250000000 : ℝ)*x 1 + (184205413/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325176867/10000000000 : ℝ)^1033 ≤ (8203840871171/25000000000000 : ℝ)^777 := by
    have hnat : (4325176867 : ℕ)^1033*25000000000000^777 ≤ 8203840871171^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325176867 10000000000 8203840871171 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635377227/1250000000 : ℝ)^1033 ≤ (5084015364823/12500000000000 : ℝ)^777 := by
    have hnat : (635377227 : ℕ)^1033*12500000000000^777 ≤ 5084015364823^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635377227 1250000000 5084015364823 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184205413/500000000 : ℝ)^1033 ≤ (13256256790901/50000000000000 : ℝ)^777 := by
    have hnat : (184205413 : ℕ)^1033*50000000000000^777 ≤ 13256256790901^777*500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184205413 500000000 13256256790901 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325176867/10000000000 : ℝ), (635377227/1250000000 : ℝ), (184205413/500000000 : ℝ)] ![(8203840871171/25000000000000 : ℝ), (5084015364823/12500000000000 : ℝ), (13256256790901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325176867/10000000000 : ℝ)|^1033 ≤ (8203840871171/25000000000000 : ℝ)^777
        have hw : |(4325176867/10000000000 : ℝ)|=(4325176867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635377227/1250000000 : ℝ)|^1033 ≤ (5084015364823/12500000000000 : ℝ)^777
        have hw : |(635377227/1250000000 : ℝ)|=(635377227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184205413/500000000 : ℝ)|^1033 ≤ (13256256790901/50000000000000 : ℝ)^777
        have hw : |(184205413/500000000 : ℝ)|=(184205413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_8 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4263827/5000000000 : ℝ)*x 0 + (5489856823/10000000000 : ℝ)*x 1 + (3186351823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4263827/5000000000 : ℝ)^1033 ≤ (4155208729/50000000000000 : ℝ)^777 := by
    have hnat : (4263827 : ℕ)^1033*50000000000000^777 ≤ 4155208729^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263827 5000000000 4155208729 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489856823/10000000000 : ℝ)^1033 ≤ (5632012279441/12500000000000 : ℝ)^777 := by
    have hnat : (5489856823 : ℕ)^1033*12500000000000^777 ≤ 5632012279441^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489856823 10000000000 5632012279441 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186351823/5000000000 : ℝ)^1033 ≤ (2197423653737/4000000000000 : ℝ)^777 := by
    have hnat : (3186351823 : ℕ)^1033*4000000000000^777 ≤ 2197423653737^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186351823 5000000000 2197423653737 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4263827/5000000000 : ℝ), (5489856823/10000000000 : ℝ), (3186351823/5000000000 : ℝ)] ![(4155208729/50000000000000 : ℝ), (5632012279441/12500000000000 : ℝ), (2197423653737/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4263827/5000000000 : ℝ)|^1033 ≤ (4155208729/50000000000000 : ℝ)^777
        have hw : |(4263827/5000000000 : ℝ)|=(4263827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489856823/10000000000 : ℝ)|^1033 ≤ (5632012279441/12500000000000 : ℝ)^777
        have hw : |(5489856823/10000000000 : ℝ)|=(5489856823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186351823/5000000000 : ℝ)|^1033 ≤ (2197423653737/4000000000000 : ℝ)^777
        have hw : |(3186351823/5000000000 : ℝ)|=(3186351823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_9 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (241247657/2500000000 : ℝ)*x 0 + (-2227855571/5000000000 : ℝ)*x 1 + (3464247821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241247657/2500000000 : ℝ)^1033 ≤ (2233168835781/50000000000000 : ℝ)^777 := by
    have hnat : (241247657 : ℕ)^1033*50000000000000^777 ≤ 2233168835781^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241247657 2500000000 2233168835781 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227855571/5000000000 : ℝ)^1033 ≤ (34138536861359/100000000000000 : ℝ)^777 := by
    have hnat : (2227855571 : ℕ)^1033*100000000000000^777 ≤ 34138536861359^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227855571 5000000000 34138536861359 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3464247821/5000000000 : ℝ)^1033 ≤ (61395125455853/100000000000000 : ℝ)^777 := by
    have hnat : (3464247821 : ℕ)^1033*100000000000000^777 ≤ 61395125455853^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464247821 5000000000 61395125455853 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(241247657/2500000000 : ℝ), (-2227855571/5000000000 : ℝ), (3464247821/5000000000 : ℝ)] ![(2233168835781/50000000000000 : ℝ), (34138536861359/100000000000000 : ℝ), (61395125455853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(241247657/2500000000 : ℝ)|^1033 ≤ (2233168835781/50000000000000 : ℝ)^777
        have hw : |(241247657/2500000000 : ℝ)|=(241247657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227855571/5000000000 : ℝ)|^1033 ≤ (34138536861359/100000000000000 : ℝ)^777
        have hw : |(-2227855571/5000000000 : ℝ)|=(2227855571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3464247821/5000000000 : ℝ)|^1033 ≤ (61395125455853/100000000000000 : ℝ)^777
        have hw : |(3464247821/5000000000 : ℝ)|=(3464247821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_10 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (964984327/10000000000 : ℝ)*x 0 + (1385696401/2000000000 : ℝ)*x 1 + (-27848317/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964984327/10000000000 : ℝ)^1033 ≤ (446629889969/10000000000000 : ℝ)^777 := by
    have hnat : (964984327 : ℕ)^1033*10000000000000^777 ≤ 446629889969^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964984327 10000000000 446629889969 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385696401/2000000000 : ℝ)^1033 ≤ (30697482400667/50000000000000 : ℝ)^777 := by
    have hnat : (1385696401 : ℕ)^1033*50000000000000^777 ≤ 30697482400667^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385696401 2000000000 30697482400667 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27848317/62500000 : ℝ)^1033 ≤ (17069368142311/50000000000000 : ℝ)^777 := by
    have hnat : (27848317 : ℕ)^1033*50000000000000^777 ≤ 17069368142311^777*62500000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27848317 62500000 17069368142311 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(964984327/10000000000 : ℝ), (1385696401/2000000000 : ℝ), (-27848317/62500000 : ℝ)] ![(446629889969/10000000000000 : ℝ), (30697482400667/50000000000000 : ℝ), (17069368142311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(964984327/10000000000 : ℝ)|^1033 ≤ (446629889969/10000000000000 : ℝ)^777
        have hw : |(964984327/10000000000 : ℝ)|=(964984327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385696401/2000000000 : ℝ)|^1033 ≤ (30697482400667/50000000000000 : ℝ)^777
        have hw : |(1385696401/2000000000 : ℝ)|=(1385696401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27848317/62500000 : ℝ)|^1033 ≤ (17069368142311/50000000000000 : ℝ)^777
        have hw : |(-27848317/62500000 : ℝ)|=(27848317/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s1_11 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (962247169/5000000000 : ℝ)*x 0 + (5829269301/10000000000 : ℝ)*x 1 + (5021717543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962247169/5000000000 : ℝ)^1033 ≤ (11181981596861/100000000000000 : ℝ)^777 := by
    have hnat : (962247169 : ℕ)^1033*100000000000000^777 ≤ 11181981596861^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962247169 5000000000 11181981596861 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5829269301/10000000000 : ℝ)^1033 ≤ (48796700508099/100000000000000 : ℝ)^777 := by
    have hnat : (5829269301 : ℕ)^1033*100000000000000^777 ≤ 48796700508099^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5829269301 10000000000 48796700508099 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5021717543/10000000000 : ℝ)^1033 ≤ (5002664733849/12500000000000 : ℝ)^777 := by
    have hnat : (5021717543 : ℕ)^1033*12500000000000^777 ≤ 5002664733849^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021717543 10000000000 5002664733849 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(962247169/5000000000 : ℝ), (5829269301/10000000000 : ℝ), (5021717543/10000000000 : ℝ)] ![(11181981596861/100000000000000 : ℝ), (48796700508099/100000000000000 : ℝ), (5002664733849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(962247169/5000000000 : ℝ)|^1033 ≤ (11181981596861/100000000000000 : ℝ)^777
        have hw : |(962247169/5000000000 : ℝ)|=(962247169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5829269301/10000000000 : ℝ)|^1033 ≤ (48796700508099/100000000000000 : ℝ)^777
        have hw : |(5829269301/10000000000 : ℝ)|=(5829269301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5021717543/10000000000 : ℝ)|^1033 ≤ (5002664733849/12500000000000 : ℝ)^777
        have hw : |(5021717543/10000000000 : ℝ)|=(5021717543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (59/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (59/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (59/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (59/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (59/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (59/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (59/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (59/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (153467397/100000000000000000000 : ℝ) := by
    have hpowers : (59/50000 : ℝ)^8263 ≤ (153467397/100000000000000000000 : ℝ)^2048 := by
      have hnat : (59 : ℕ)^8263*100000000000000000000^2048 ≤ 153467397^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 50000 153467397 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/50000 : ℝ)) (X := (153467397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/10000 : ℝ) ^ (8263/2048 : ℝ) ≤ (74473090856770283/12500000000000000000 : ℝ) := by
    have hpowers : (2809/10000 : ℝ)^8263 ≤ (74473090856770283/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2809 : ℕ)^8263*12500000000000000000^2048 ≤ 74473090856770283^2048*10000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 10000 74473090856770283 12500000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/10000 : ℝ)) (X := (74473090856770283/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000153467397/50000000000000000000 : ℝ) ≤ (1250000000000951/1250000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50000000000153467397/50000000000000000000 : ℝ)^2048 ≤ (1250000000000951/1250000000000000 : ℝ)^8263 := by
      have hnat : (50000000000153467397 : ℕ)^2048*1250000000000000^8263 ≤ 1250000000000951^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000153467397 50000000000000000000 1250000000000951 1250000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000000951/1250000000000000 : ℝ)) (X := (50000000000153467397/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100595784727007629661/100000000000000000000 : ℝ) ≤ (2503683416128127/2500000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (100595784727007629661/100000000000000000000 : ℝ)^2048 ≤ (2503683416128127/2500000000000000 : ℝ)^8263 := by
      have hnat : (100595784727007629661 : ℕ)^2048*2500000000000000^8263 ≤ 2503683416128127^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100595784727007629661 100000000000000000000 2503683416128127 2500000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503683416128127/2500000000000000 : ℝ)) (X := (100595784727007629661/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6324473090856770283/6250000000000000000 : ℝ) ≤ (156710427015897/156250000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (6324473090856770283/6250000000000000000 : ℝ)^2048 ≤ (156710427015897/156250000000000 : ℝ)^8263 := by
      have hnat : (6324473090856770283 : ℕ)^2048*156250000000000^8263 ≤ 156710427015897^8263*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6324473090856770283 6250000000000000000 156710427015897 156250000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156710427015897/156250000000000 : ℝ)) (X := (6324473090856770283/6250000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(153467397/100000000000000000000 : ℝ) ≤ ((17482282678461853411/17482500000000000000 : ℝ)+2*(147336645049/27972000000000 : ℝ)*(59/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (17482282678461853411/17482500000000000000 : ℝ)+2*(147336645049/27972000000000 : ℝ)*(59/50000 : ℝ)=(1250000000000951/1250000000000000 : ℝ) by norm_num, show 1+2*(153467397/100000000000000000000 : ℝ)=(50000000000153467397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74473090856770283/12500000000000000000 : ℝ)+(153467397/100000000000000000000 : ℝ) ≤ ((17482282678461853411/17482500000000000000 : ℝ)+(147336645049/27972000000000 : ℝ)*((2809/10000 : ℝ)+(59/50000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (17482282678461853411/17482500000000000000 : ℝ)+(147336645049/27972000000000 : ℝ)*((2809/10000 : ℝ)+(59/50000 : ℝ))=(2503683416128127/2500000000000000 : ℝ) by norm_num, show 1+(74473090856770283/12500000000000000000 : ℝ)+(153467397/100000000000000000000 : ℝ)=(100595784727007629661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74473090856770283/12500000000000000000 : ℝ) ≤ ((17482282678461853411/17482500000000000000 : ℝ)+2*(147336645049/27972000000000 : ℝ)*(2809/10000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (17482282678461853411/17482500000000000000 : ℝ)+2*(147336645049/27972000000000 : ℝ)*(2809/10000 : ℝ)=(156710427015897/156250000000000 : ℝ) by norm_num, show 1+2*(74473090856770283/12500000000000000000 : ℝ)=(6324473090856770283/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17482282678461853411/17482500000000000000 : ℝ)*(X 1 0+X 2 0)+(147336645049/27972000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (59/50000 : ℝ)) (hi := (2809/10000 : ℝ)) (c := (17482282678461853411/17482500000000000000 : ℝ)) (alpha := (147336645049/27972000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17482282678461853411/17482500000000000000 : ℝ)*(X 0 1+X 2 1)+(147336645049/27972000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (59/50000 : ℝ)) (hi := (2809/10000 : ℝ)) (c := (17482282678461853411/17482500000000000000 : ℝ)) (alpha := (147336645049/27972000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17482282678461853411/17482500000000000000 : ℝ)*(X 0 2+X 1 2)+(147336645049/27972000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (59/50000 : ℝ)) (hi := (2809/10000 : ℝ)) (c := (17482282678461853411/17482500000000000000 : ℝ)) (alpha := (147336645049/27972000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531064129/2500000000 : ℝ)*X 0 0+(5720926033/10000000000 : ℝ)*X 0 1+(1246763469/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((542303827/1000000000 : ℝ)*X 1 0+(-39402543/156250000 : ℝ)*X 1 1+(997410837/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711519449/5000000000 : ℝ)*X 2 0+(2493526743/5000000000 : ℝ)*X 2 1+(-1260881409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323387277/10000000000 : ℝ)*X 0 0+(1831751401/5000000000 : ℝ)*X 0 1+(1020643283/2000000000 : ℝ)*X 0 2+(4323387277/10000000000 : ℝ)*X 1 0+(1831751401/5000000000 : ℝ)*X 1 1+(1020643283/2000000000 : ℝ)*X 1 2+(4323387277/10000000000 : ℝ)*X 2 0+(1831751401/5000000000 : ℝ)*X 2 1+(1020643283/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132823181/625000000 : ℝ)*X 0 0+(2498674023/5000000000 : ℝ)*X 0 1+(571042081/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10225721/19531250 : ℝ)*X 1 0+(-359678753/2000000000 : ℝ)*X 1 1+(1142084533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047113419/2000000000 : ℝ)*X 2 0+(5710424943/10000000000 : ℝ)*X 2 1+(-449598339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325176867/10000000000 : ℝ)*X 0 0+(635377227/1250000000 : ℝ)*X 0 1+(184205413/500000000 : ℝ)*X 0 2+(4325176867/10000000000 : ℝ)*X 1 0+(635377227/1250000000 : ℝ)*X 1 1+(184205413/500000000 : ℝ)*X 1 2+(4325176867/10000000000 : ℝ)*X 2 0+(635377227/1250000000 : ℝ)*X 2 1+(184205413/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((4263827/5000000000 : ℝ)*X 0 0+(5489856823/10000000000 : ℝ)*X 0 1+(3186351823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((241247657/2500000000 : ℝ)*X 1 0+(-2227855571/5000000000 : ℝ)*X 1 1+(3464247821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((964984327/10000000000 : ℝ)*X 2 0+(1385696401/2000000000 : ℝ)*X 2 1+(-27848317/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((962247169/5000000000 : ℝ)*X 0 0+(5829269301/10000000000 : ℝ)*X 0 1+(5021717543/10000000000 : ℝ)*X 0 2+(962247169/5000000000 : ℝ)*X 1 0+(5829269301/10000000000 : ℝ)*X 1 1+(5021717543/10000000000 : ℝ)*X 1 2+(962247169/5000000000 : ℝ)*X 2 0+(5829269301/10000000000 : ℝ)*X 2 1+(5021717543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (301982897253339931390161/115625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25715257498021/2500000000000 : ℝ)*(major0) + (25715257498021/2500000000000 : ℝ)*(major1) + (25715257498021/2500000000000 : ℝ)*(major2) + (34065905164091/2500000000000 : ℝ)*(sp0) + (136263683492627/10000000000000 : ℝ)*(sp1) + (340658988385691/25000000000000 : ℝ)*(sp2) + (694582716048561/100000000000000 : ℝ)*(sp3) + (1032543803/100000000000000 : ℝ)*(sp4) + (11404719/2500000000000 : ℝ)*(sp5) + (1175884809/100000000000000 : ℝ)*(sp6) + (43555077/25000000000000 : ℝ)*(sp8) + (61106361/50000000000000 : ℝ)*(sp9) + (283900179/100000000000000 : ℝ)*(sp10) + (95851807/25000000000000 : ℝ)*(sp11) + (173645774863947/25000000000000 : ℝ)*(f.failure) + (170329676665969/12500000000000 : ℝ)*(f.sum) + (417049628087/199800000000000000000000000 : ℝ)*base66 + (21781168854035767/6243750000000000000000000000000 : ℝ)*base68 + (14107884600504517/6243750000000000000000000000000 : ℝ)*base70 + (42388985440254517/6243750000000000000000000000000 : ℝ)*base72 + (733810903007/499500000000000000000000000 : ℝ)*base74 + (51426096757779517/6243750000000000000000000000000 : ℝ)*base76 + (50011571623854517/6243750000000000000000000000000 : ℝ)*base78 + (44413417350635767/6243750000000000000000000000000 : ℝ)*base80 + (1876714500817/999000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1325339/500000000000000000000 : ℝ)*base90 + (1325339/500000000000000000000 : ℝ)*base92 + (1325339/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38957450945690853467781923/6070312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9841739/12500000000000 : ℝ)*(lower4) + (66163309166377/6250000000000 : ℝ)*(major0) + (66163309166377/6250000000000 : ℝ)*(major1) + (66163309166377/6250000000000 : ℝ)*(major2) + (1534922667/100000000000000 : ℝ)*(sp0) + (2665875529/100000000000000 : ℝ)*(sp1) + (5629011297/100000000000000 : ℝ)*(sp2) + (350594498225569/25000000000000 : ℝ)*(sp4) + (350594964406377/25000000000000 : ℝ)*(sp5) + (87648578470627/6250000000000 : ℝ)*(sp6) + (89355132222281/12500000000000 : ℝ)*(sp7) + (1678358193/50000000000000 : ℝ)*(sp8) + (90260073/25000000000000 : ℝ)*(sp9) + (868540557/50000000000000 : ℝ)*(sp11) + (357421397429681/50000000000000 : ℝ)*(f.failure) + (1402382884541329/100000000000000 : ℝ)*(f.sum) + (5550854424377/1748250000000000000000000000 : ℝ)*base65 + (9618829397164463/1951171875000000000000000000000 : ℝ)*base68 + (84256345950393829/15609375000000000000000000000000 : ℝ)*base70 + (32843571602418671/15609375000000000000000000000000 : ℝ)*base71 + (180128239337/699300000000000000000000000 : ℝ)*base73 + (11747176388445713/1951171875000000000000000000000 : ℝ)*base76 + (70941919080018829/15609375000000000000000000000000 : ℝ)*base78 + (95338090768987579/15609375000000000000000000000000 : ℝ)*base80 + (3446053571713/1748250000000000000000000000 : ℝ)*base82 + (9927903/1000000000000000000000 : ℝ)*base89 + (9927903/1000000000000000000000 : ℝ)*base91 + (9927903/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1071_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (59/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_s2_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-218140029/1000000000 : ℝ)*x 0 + (5524868413/10000000000 : ℝ)*x 1 + (5146851079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218140029/1000000000 : ℝ)^1033 ≤ (13208909582177/100000000000000 : ℝ)^777 := by
    have hnat : (218140029 : ℕ)^1033*100000000000000^777 ≤ 13208909582177^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218140029 1000000000 13208909582177 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524868413/10000000000 : ℝ)^1033 ≤ (45438516902673/100000000000000 : ℝ)^777 := by
    have hnat : (5524868413 : ℕ)^1033*100000000000000^777 ≤ 45438516902673^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524868413 10000000000 45438516902673 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146851079/10000000000 : ℝ)^1033 ≤ (20676286746869/50000000000000 : ℝ)^777 := by
    have hnat : (5146851079 : ℕ)^1033*50000000000000^777 ≤ 20676286746869^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146851079 10000000000 20676286746869 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218140029/1000000000 : ℝ), (5524868413/10000000000 : ℝ), (5146851079/10000000000 : ℝ)] ![(13208909582177/100000000000000 : ℝ), (45438516902673/100000000000000 : ℝ), (20676286746869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218140029/1000000000 : ℝ)|^1033 ≤ (13208909582177/100000000000000 : ℝ)^777
        have hw : |(-218140029/1000000000 : ℝ)|=(218140029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524868413/10000000000 : ℝ)|^1033 ≤ (45438516902673/100000000000000 : ℝ)^777
        have hw : |(5524868413/10000000000 : ℝ)|=(5524868413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146851079/10000000000 : ℝ)|^1033 ≤ (20676286746869/50000000000000 : ℝ)^777
        have hw : |(5146851079/10000000000 : ℝ)|=(5146851079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5376979893/10000000000 : ℝ)*x 0 + (-2378496657/10000000000 : ℝ)*x 1 + (20104891/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376979893/10000000000 : ℝ)^1033 ≤ (43828668334997/100000000000000 : ℝ)^777 := by
    have hnat : (5376979893 : ℕ)^1033*100000000000000^777 ≤ 43828668334997^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376979893 10000000000 43828668334997 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2378496657/10000000000 : ℝ)^1033 ≤ (1852343412027/12500000000000 : ℝ)^777 := by
    have hnat : (2378496657 : ℕ)^1033*12500000000000^777 ≤ 1852343412027^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378496657 10000000000 1852343412027 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20104891/39062500 : ℝ)^1033 ≤ (1292268261157/3125000000000 : ℝ)^777 := by
    have hnat : (20104891 : ℕ)^1033*3125000000000^777 ≤ 1292268261157^777*39062500^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20104891 39062500 1292268261157 3125000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376979893/10000000000 : ℝ), (-2378496657/10000000000 : ℝ), (20104891/39062500 : ℝ)] ![(43828668334997/100000000000000 : ℝ), (1852343412027/12500000000000 : ℝ), (1292268261157/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376979893/10000000000 : ℝ)|^1033 ≤ (43828668334997/100000000000000 : ℝ)^777
        have hw : |(5376979893/10000000000 : ℝ)|=(5376979893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2378496657/10000000000 : ℝ)|^1033 ≤ (1852343412027/12500000000000 : ℝ)^777
        have hw : |(-2378496657/10000000000 : ℝ)|=(2378496657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20104891/39062500 : ℝ)|^1033 ≤ (1292268261157/3125000000000 : ℝ)^777
        have hw : |(20104891/39062500 : ℝ)|=(20104891/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5376979521/10000000000 : ℝ)*x 0 + (5146852509/10000000000 : ℝ)*x 1 + (-2378496611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376979521/10000000000 : ℝ)^1033 ≤ (1753146572149/4000000000000 : ℝ)^777 := by
    have hnat : (5376979521 : ℕ)^1033*4000000000000^777 ≤ 1753146572149^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376979521 10000000000 1753146572149 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5146852509/10000000000 : ℝ)^1033 ≤ (8270517753713/20000000000000 : ℝ)^777 := by
    have hnat : (5146852509 : ℕ)^1033*20000000000000^777 ≤ 8270517753713^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146852509 10000000000 8270517753713 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2378496611/10000000000 : ℝ)^1033 ≤ (14818746915197/100000000000000 : ℝ)^777 := by
    have hnat : (2378496611 : ℕ)^1033*100000000000000^777 ≤ 14818746915197^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378496611 10000000000 14818746915197 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376979521/10000000000 : ℝ), (5146852509/10000000000 : ℝ), (-2378496611/10000000000 : ℝ)] ![(1753146572149/4000000000000 : ℝ), (8270517753713/20000000000000 : ℝ), (14818746915197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376979521/10000000000 : ℝ)|^1033 ≤ (1753146572149/4000000000000 : ℝ)^777
        have hw : |(5376979521/10000000000 : ℝ)|=(5376979521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5146852509/10000000000 : ℝ)|^1033 ≤ (8270517753713/20000000000000 : ℝ)^777
        have hw : |(5146852509/10000000000 : ℝ)|=(5146852509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2378496611/10000000000 : ℝ)|^1033 ≤ (14818746915197/100000000000000 : ℝ)^777
        have hw : |(-2378496611/10000000000 : ℝ)|=(2378496611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4362395703/10000000000 : ℝ)*x 0 + (4007471021/10000000000 : ℝ)*x 1 + (4749056359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362395703/10000000000 : ℝ)^1033 ≤ (33191312949099/100000000000000 : ℝ)^777 := by
    have hnat : (4362395703 : ℕ)^1033*100000000000000^777 ≤ 33191312949099^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362395703 10000000000 33191312949099 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007471021/10000000000 : ℝ)^1033 ≤ (14825084497311/50000000000000 : ℝ)^777 := by
    have hnat : (4007471021 : ℕ)^1033*50000000000000^777 ≤ 14825084497311^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007471021 10000000000 14825084497311 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4749056359/10000000000 : ℝ)^1033 ≤ (37158518043047/100000000000000 : ℝ)^777 := by
    have hnat : (4749056359 : ℕ)^1033*100000000000000^777 ≤ 37158518043047^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749056359 10000000000 37158518043047 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362395703/10000000000 : ℝ), (4007471021/10000000000 : ℝ), (4749056359/10000000000 : ℝ)] ![(33191312949099/100000000000000 : ℝ), (14825084497311/50000000000000 : ℝ), (37158518043047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362395703/10000000000 : ℝ)|^1033 ≤ (33191312949099/100000000000000 : ℝ)^777
        have hw : |(4362395703/10000000000 : ℝ)|=(4362395703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007471021/10000000000 : ℝ)|^1033 ≤ (14825084497311/50000000000000 : ℝ)^777
        have hw : |(4007471021/10000000000 : ℝ)|=(4007471021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4749056359/10000000000 : ℝ)|^1033 ≤ (37158518043047/100000000000000 : ℝ)^777
        have hw : |(4749056359/10000000000 : ℝ)|=(4749056359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-218152417/1000000000 : ℝ)*x 0 + (5149593081/10000000000 : ℝ)*x 1 + (5522098027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218152417/1000000000 : ℝ)^1033 ≤ (3302476715001/25000000000000 : ℝ)^777 := by
    have hnat : (218152417 : ℕ)^1033*25000000000000^777 ≤ 3302476715001^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218152417 1000000000 3302476715001 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149593081/10000000000 : ℝ)^1033 ≤ (20690932648847/50000000000000 : ℝ)^777 := by
    have hnat : (5149593081 : ℕ)^1033*50000000000000^777 ≤ 20690932648847^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149593081 10000000000 20690932648847 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522098027/10000000000 : ℝ)^1033 ≤ (22704113917169/50000000000000 : ℝ)^777 := by
    have hnat : (5522098027 : ℕ)^1033*50000000000000^777 ≤ 22704113917169^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522098027 10000000000 22704113917169 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218152417/1000000000 : ℝ), (5149593081/10000000000 : ℝ), (5522098027/10000000000 : ℝ)] ![(3302476715001/25000000000000 : ℝ), (20690932648847/50000000000000 : ℝ), (22704113917169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218152417/1000000000 : ℝ)|^1033 ≤ (3302476715001/25000000000000 : ℝ)^777
        have hw : |(-218152417/1000000000 : ℝ)|=(218152417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149593081/10000000000 : ℝ)|^1033 ≤ (20690932648847/50000000000000 : ℝ)^777
        have hw : |(5149593081/10000000000 : ℝ)|=(5149593081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522098027/10000000000 : ℝ)|^1033 ≤ (22704113917169/50000000000000 : ℝ)^777
        have hw : |(5522098027/10000000000 : ℝ)|=(5522098027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (528153013/1000000000 : ℝ)*x 0 + (-200325279/1000000000 : ℝ)*x 1 + (1380524529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528153013/1000000000 : ℝ)^1033 ≤ (21398669880533/50000000000000 : ℝ)^777 := by
    have hnat : (528153013 : ℕ)^1033*50000000000000^777 ≤ 21398669880533^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528153013 1000000000 21398669880533 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200325279/1000000000 : ℝ)^1033 ≤ (2948607853811/25000000000000 : ℝ)^777 := by
    have hnat : (200325279 : ℕ)^1033*25000000000000^777 ≤ 2948607853811^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200325279 1000000000 2948607853811 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380524529/2500000000 : ℝ)^1033 ≤ (45408228807309/100000000000000 : ℝ)^777 := by
    have hnat : (1380524529 : ℕ)^1033*100000000000000^777 ≤ 45408228807309^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380524529 2500000000 45408228807309 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528153013/1000000000 : ℝ), (-200325279/1000000000 : ℝ), (1380524529/2500000000 : ℝ)] ![(21398669880533/50000000000000 : ℝ), (2948607853811/25000000000000 : ℝ), (45408228807309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528153013/1000000000 : ℝ)|^1033 ≤ (21398669880533/50000000000000 : ℝ)^777
        have hw : |(528153013/1000000000 : ℝ)|=(528153013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200325279/1000000000 : ℝ)|^1033 ≤ (2948607853811/25000000000000 : ℝ)^777
        have hw : |(-200325279/1000000000 : ℝ)|=(200325279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380524529/2500000000 : ℝ)|^1033 ≤ (45408228807309/100000000000000 : ℝ)^777
        have hw : |(1380524529/2500000000 : ℝ)|=(1380524529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2640765187/5000000000 : ℝ)*x 0 + (2761048977/5000000000 : ℝ)*x 1 + (-2003252681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640765187/5000000000 : ℝ)^1033 ≤ (10699335597419/25000000000000 : ℝ)^777 := by
    have hnat : (2640765187 : ℕ)^1033*25000000000000^777 ≤ 10699335597419^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640765187 5000000000 10699335597419 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761048977/5000000000 : ℝ)^1033 ≤ (45408227036283/100000000000000 : ℝ)^777 := by
    have hnat : (2761048977 : ℕ)^1033*100000000000000^777 ≤ 45408227036283^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761048977 5000000000 45408227036283 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003252681/10000000000 : ℝ)^1033 ≤ (11794430562051/100000000000000 : ℝ)^777 := by
    have hnat : (2003252681 : ℕ)^1033*100000000000000^777 ≤ 11794430562051^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003252681 10000000000 11794430562051 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640765187/5000000000 : ℝ), (2761048977/5000000000 : ℝ), (-2003252681/10000000000 : ℝ)] ![(10699335597419/25000000000000 : ℝ), (45408227036283/100000000000000 : ℝ), (11794430562051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640765187/5000000000 : ℝ)|^1033 ≤ (10699335597419/25000000000000 : ℝ)^777
        have hw : |(2640765187/5000000000 : ℝ)|=(2640765187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761048977/5000000000 : ℝ)|^1033 ≤ (45408227036283/100000000000000 : ℝ)^777
        have hw : |(2761048977/5000000000 : ℝ)|=(2761048977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2003252681/10000000000 : ℝ)|^1033 ≤ (11794430562051/100000000000000 : ℝ)^777
        have hw : |(-2003252681/10000000000 : ℝ)|=(2003252681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s2_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1090659047/2500000000 : ℝ)*x 0 + (4743684871/10000000000 : ℝ)*x 1 + (2006450987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090659047/2500000000 : ℝ)^1033 ≤ (518652274197/1562500000000 : ℝ)^777 := by
    have hnat : (1090659047 : ℕ)^1033*1562500000000^777 ≤ 518652274197^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090659047 2500000000 518652274197 1562500000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4743684871/10000000000 : ℝ)^1033 ≤ (18551326249967/50000000000000 : ℝ)^777 := by
    have hnat : (4743684871 : ℕ)^1033*50000000000000^777 ≤ 18551326249967^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4743684871 10000000000 18551326249967 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006450987/5000000000 : ℝ)^1033 ≤ (14851800965813/50000000000000 : ℝ)^777 := by
    have hnat : (2006450987 : ℕ)^1033*50000000000000^777 ≤ 14851800965813^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006450987 5000000000 14851800965813 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090659047/2500000000 : ℝ), (4743684871/10000000000 : ℝ), (2006450987/5000000000 : ℝ)] ![(518652274197/1562500000000 : ℝ), (18551326249967/50000000000000 : ℝ), (14851800965813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090659047/2500000000 : ℝ)|^1033 ≤ (518652274197/1562500000000 : ℝ)^777
        have hw : |(1090659047/2500000000 : ℝ)|=(1090659047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4743684871/10000000000 : ℝ)|^1033 ≤ (18551326249967/50000000000000 : ℝ)^777
        have hw : |(4743684871/10000000000 : ℝ)|=(4743684871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006450987/5000000000 : ℝ)|^1033 ≤ (14851800965813/50000000000000 : ℝ)^777
        have hw : |(2006450987/5000000000 : ℝ)|=(2006450987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (273/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4181/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5243/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (682228511520539/100000000000000000000 : ℝ) := by
    have hpowers : (5243/100000 : ℝ)^8263 ≤ (682228511520539/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5243 : ℕ)^8263*100000000000000000000^2048 ≤ 682228511520539^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5243 100000 682228511520539 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5243/100000 : ℝ)) (X := (682228511520539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20767/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (176128560879034237/100000000000000000000 : ℝ) := by
    have hpowers : (20767/100000 : ℝ)^8263 ≤ (176128560879034237/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20767 : ℕ)^8263*100000000000000000000^2048 ≤ 176128560879034237^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20767 100000 176128560879034237 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20767/100000 : ℝ)) (X := (176128560879034237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000682228511520539/50000000000000000000 : ℝ) ≤ (10000033818148907/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50000682228511520539/50000000000000000000 : ℝ)^2048 ≤ (10000033818148907/10000000000000000 : ℝ)^8263 := by
      have hnat : (50000682228511520539 : ℕ)^2048*10000000000000000^8263 ≤ 10000033818148907^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000682228511520539 50000000000000000000 10000033818148907 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033818148907/10000000000000000 : ℝ)) (X := (50000682228511520539/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12522101348673819347/12500000000000000000 : ℝ) ≤ (10004379377523459/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (12522101348673819347/12500000000000000000 : ℝ)^2048 ≤ (10004379377523459/10000000000000000 : ℝ)^8263 := by
      have hnat : (12522101348673819347 : ℕ)^2048*10000000000000000^8263 ≤ 10004379377523459^8263*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12522101348673819347 12500000000000000000 10004379377523459 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004379377523459/10000000000000000 : ℝ)) (X := (12522101348673819347/12500000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50176128560879034237/50000000000000000000 : ℝ) ≤ (10008724936898011/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50176128560879034237/50000000000000000000 : ℝ)^2048 ≤ (10008724936898011/10000000000000000 : ℝ)^8263 := by
      have hnat : (50176128560879034237 : ℕ)^2048*10000000000000000^8263 ≤ 10008724936898011^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50176128560879034237 50000000000000000000 10008724936898011 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008724936898011/10000000000000000 : ℝ)) (X := (50176128560879034237/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(682228511520539/100000000000000000000 : ℝ) ≤ ((38798739364335519999/38810000000000000000 : ℝ)+2*(543194921819/194050000000000 : ℝ)*(5243/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (38798739364335519999/38810000000000000000 : ℝ)+2*(543194921819/194050000000000 : ℝ)*(5243/100000 : ℝ)=(10000033818148907/10000000000000000 : ℝ) by norm_num, show 1+2*(682228511520539/100000000000000000000 : ℝ)=(50000682228511520539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(176128560879034237/100000000000000000000 : ℝ)+(682228511520539/100000000000000000000 : ℝ) ≤ ((38798739364335519999/38810000000000000000 : ℝ)+(543194921819/194050000000000 : ℝ)*((20767/100000 : ℝ)+(5243/100000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (38798739364335519999/38810000000000000000 : ℝ)+(543194921819/194050000000000 : ℝ)*((20767/100000 : ℝ)+(5243/100000 : ℝ))=(10004379377523459/10000000000000000 : ℝ) by norm_num, show 1+(176128560879034237/100000000000000000000 : ℝ)+(682228511520539/100000000000000000000 : ℝ)=(12522101348673819347/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(176128560879034237/100000000000000000000 : ℝ) ≤ ((38798739364335519999/38810000000000000000 : ℝ)+2*(543194921819/194050000000000 : ℝ)*(20767/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (38798739364335519999/38810000000000000000 : ℝ)+2*(543194921819/194050000000000 : ℝ)*(20767/100000 : ℝ)=(10008724936898011/10000000000000000 : ℝ) by norm_num, show 1+2*(176128560879034237/100000000000000000000 : ℝ)=(50176128560879034237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38798739364335519999/38810000000000000000 : ℝ)*(X 1 0+X 2 0)+(543194921819/194050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5243/100000 : ℝ)) (hi := (20767/100000 : ℝ)) (c := (38798739364335519999/38810000000000000000 : ℝ)) (alpha := (543194921819/194050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38798739364335519999/38810000000000000000 : ℝ)*(X 0 1+X 2 1)+(543194921819/194050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5243/100000 : ℝ)) (hi := (20767/100000 : ℝ)) (c := (38798739364335519999/38810000000000000000 : ℝ)) (alpha := (543194921819/194050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38798739364335519999/38810000000000000000 : ℝ)*(X 0 2+X 1 2)+(543194921819/194050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5243/100000 : ℝ)) (hi := (20767/100000 : ℝ)) (c := (38798739364335519999/38810000000000000000 : ℝ)) (alpha := (543194921819/194050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-218140029/1000000000 : ℝ)*X 0 0+(5524868413/10000000000 : ℝ)*X 0 1+(5146851079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376979893/10000000000 : ℝ)*X 1 0+(-2378496657/10000000000 : ℝ)*X 1 1+(20104891/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376979521/10000000000 : ℝ)*X 2 0+(5146852509/10000000000 : ℝ)*X 2 1+(-2378496611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362395703/10000000000 : ℝ)*X 0 0+(4007471021/10000000000 : ℝ)*X 0 1+(4749056359/10000000000 : ℝ)*X 0 2+(4362395703/10000000000 : ℝ)*X 1 0+(4007471021/10000000000 : ℝ)*X 1 1+(4749056359/10000000000 : ℝ)*X 1 2+(4362395703/10000000000 : ℝ)*X 2 0+(4007471021/10000000000 : ℝ)*X 2 1+(4749056359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-218152417/1000000000 : ℝ)*X 0 0+(5149593081/10000000000 : ℝ)*X 0 1+(5522098027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528153013/1000000000 : ℝ)*X 1 0+(-200325279/1000000000 : ℝ)*X 1 1+(1380524529/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640765187/5000000000 : ℝ)*X 2 0+(2761048977/5000000000 : ℝ)*X 2 1+(-2003252681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090659047/2500000000 : ℝ)*X 0 0+(4743684871/10000000000 : ℝ)*X 0 1+(2006450987/5000000000 : ℝ)*X 0 2+(1090659047/2500000000 : ℝ)*X 1 0+(4743684871/10000000000 : ℝ)*X 1 1+(2006450987/5000000000 : ℝ)*X 1 2+(1090659047/2500000000 : ℝ)*X 2 0+(4743684871/10000000000 : ℝ)*X 2 1+(2006450987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51784359890164898852334603/60640625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (511546149/100000000000000 : ℝ)*(base1) + (3511725917/100000000000000 : ℝ)*(base19) + (3328703363/100000000000000 : ℝ)*(base23) + (296683023/100000000000000 : ℝ)*(upper3) + (70722349/25000000000000 : ℝ)*(upper5) + (124810516516951/6250000000000 : ℝ)*(major0) + (124810516516951/6250000000000 : ℝ)*(major1) + (124810516516951/6250000000000 : ℝ)*(major2) + (2645419357060213/100000000000000 : ℝ)*(sp0) + (1322726499388971/50000000000000 : ℝ)*(sp1) + (165340823862531/6250000000000 : ℝ)*(sp2) + (1348471033259707/100000000000000 : ℝ)*(sp3) + (18832494897/50000000000000 : ℝ)*(sp4) + (1688953509/20000000000000 : ℝ)*(sp7) + (6742399947867/500000000000 : ℝ)*(f.failure) + (1322728255251929/50000000000000 : ℝ)*(f.sum) + (13903810468753/19405000000000000000000000000 : ℝ)*base65 + (2718895137230240549/242562500000000000000000000000000 : ℝ)*base67 + (1086355620410053049/242562500000000000000000000000000 : ℝ)*base69 + (1560356515203865549/242562500000000000000000000000000 : ℝ)*base71 + (4647154704921/2425625000000000000000000000 : ℝ)*base73 + (55050173027115549/242562500000000000000000000000000 : ℝ)*base75 + (669695728359259451/242562500000000000000000000000000 : ℝ)*base78 + (896213278513928049/242562500000000000000000000000000 : ℝ)*base79 + (7120465628073/19405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (78379/10000000000000000000 : ℝ)*base90 + (78379/10000000000000000000 : ℝ)*base92 + (78379/10000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3117287653462116175250293989/970250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (600043967/100000000000000 : ℝ)*(base19) + (6179661/800000000000 : ℝ)*(base23) + (103758611/100000000000000 : ℝ)*(upper3) + (8958437/100000000000000 : ℝ)*(lower4) + (61508351/100000000000000 : ℝ)*(upper5) + (2026461976775337/100000000000000 : ℝ)*(major0) + (2026461976775337/100000000000000 : ℝ)*(major1) + (2026461976775337/100000000000000 : ℝ)*(major2) + (5032098331/100000000000000 : ℝ)*(sp1) + (6771265939/100000000000000 : ℝ)*(sp2) + (1342263913122869/50000000000000 : ℝ)*(sp4) + (33556527426293/1250000000000 : ℝ)*(sp5) + (1342260141261087/50000000000000 : ℝ)*(sp6) + (1368396020209247/100000000000000 : ℝ)*(sp7) + (1368396020209247/100000000000000 : ℝ)*(f.failure) + (1342263913122869/50000000000000 : ℝ)*(f.sum) + (17338824346637/9702500000000000000000000000 : ℝ)*base66 + (68621551579064663/3881000000000000000000000000000000 : ℝ)*base67 + (20922432885329935337/3881000000000000000000000000000000 : ℝ)*base70 + (7623114123244935337/3881000000000000000000000000000000 : ℝ)*base72 + (1406948392041/1212812500000000000000000000 : ℝ)*base73 + (43787778630419935337/3881000000000000000000000000000000 : ℝ)*base76 + (32751977912316935337/3881000000000000000000000000000000 : ℝ)*base78 + (14069411908309935337/3881000000000000000000000000000000 : ℝ)*base80 + (2332937707231/19405000000000000000000000000 : ℝ)*base81 + (10828561/2000000000000000000000 : ℝ)*base89 + (10828561/2000000000000000000000 : ℝ)*base91 + (10828561/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1071_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1071_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1071_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1071_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1071_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
