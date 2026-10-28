-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:57.100857+00:00
-- url     : https://prove2.me/submissions/dd6ee93e-f1bf-4b46-9486-54aa9903cff2

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
theorem support_rectangle_w1093_s3_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87446363/400000000 : ℝ)*x 0 + (42456541/78125000 : ℝ)*x 1 + (2613625697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87446363/400000000 : ℝ)^4143 ≤ (13270657591013/100000000000000 : ℝ)^3119 := by
    have hnat : (87446363 : ℕ)^4143*100000000000000^3119 ≤ 13270657591013^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87446363 400000000 13270657591013 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42456541/78125000 : ℝ)^4143 ≤ (4448392333659/10000000000000 : ℝ)^3119 := by
    have hnat : (42456541 : ℕ)^4143*10000000000000^3119 ≤ 4448392333659^3119*78125000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42456541 78125000 4448392333659 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613625697/5000000000 : ℝ)^4143 ≤ (844908381291/2000000000000 : ℝ)^3119 := by
    have hnat : (2613625697 : ℕ)^4143*2000000000000^3119 ≤ 844908381291^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613625697 5000000000 844908381291 2000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87446363/400000000 : ℝ), (42456541/78125000 : ℝ), (2613625697/5000000000 : ℝ)] ![(13270657591013/100000000000000 : ℝ), (4448392333659/10000000000000 : ℝ), (844908381291/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87446363/400000000 : ℝ)|^4143 ≤ (13270657591013/100000000000000 : ℝ)^3119
        have hw : |(-87446363/400000000 : ℝ)|=(87446363/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42456541/78125000 : ℝ)|^4143 ≤ (4448392333659/10000000000000 : ℝ)^3119
        have hw : |(42456541/78125000 : ℝ)|=(42456541/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613625697/5000000000 : ℝ)|^4143 ≤ (844908381291/2000000000000 : ℝ)^3119
        have hw : |(2613625697/5000000000 : ℝ)|=(2613625697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354999789/10000000000 : ℝ)*x 0 + (-1146092209/5000000000 : ℝ)*x 1 + (2613625637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354999789/10000000000 : ℝ)^4143 ≤ (10905570455793/25000000000000 : ℝ)^3119 := by
    have hnat : (5354999789 : ℕ)^4143*25000000000000^3119 ≤ 10905570455793^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354999789 10000000000 10905570455793 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146092209/5000000000 : ℝ)^4143 ≤ (14132300387209/100000000000000 : ℝ)^3119 := by
    have hnat : (1146092209 : ℕ)^4143*100000000000000^3119 ≤ 14132300387209^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146092209 5000000000 14132300387209 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613625637/5000000000 : ℝ)^4143 ≤ (42245417776339/100000000000000 : ℝ)^3119 := by
    have hnat : (2613625637 : ℕ)^4143*100000000000000^3119 ≤ 42245417776339^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613625637 5000000000 42245417776339 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354999789/10000000000 : ℝ), (-1146092209/5000000000 : ℝ), (2613625637/5000000000 : ℝ)] ![(10905570455793/25000000000000 : ℝ), (14132300387209/100000000000000 : ℝ), (42245417776339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354999789/10000000000 : ℝ)|^4143 ≤ (10905570455793/25000000000000 : ℝ)^3119
        have hw : |(5354999789/10000000000 : ℝ)|=(5354999789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1146092209/5000000000 : ℝ)|^4143 ≤ (14132300387209/100000000000000 : ℝ)^3119
        have hw : |(-1146092209/5000000000 : ℝ)|=(1146092209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613625637/5000000000 : ℝ)|^4143 ≤ (42245417776339/100000000000000 : ℝ)^3119
        have hw : |(2613625637/5000000000 : ℝ)|=(2613625637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677499833/5000000000 : ℝ)*x 0 + (2613625859/5000000000 : ℝ)*x 1 + (-1146091999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677499833/5000000000 : ℝ)^4143 ≤ (43622280492247/100000000000000 : ℝ)^3119 := by
    have hnat : (2677499833 : ℕ)^4143*100000000000000^3119 ≤ 43622280492247^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677499833 5000000000 43622280492247 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613625859/5000000000 : ℝ)^4143 ≤ (66008472723/156250000000 : ℝ)^3119 := by
    have hnat : (2613625859 : ℕ)^4143*156250000000^3119 ≤ 66008472723^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613625859 5000000000 66008472723 156250000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146091999/5000000000 : ℝ)^4143 ≤ (1766537118447/12500000000000 : ℝ)^3119 := by
    have hnat : (1146091999 : ℕ)^4143*12500000000000^3119 ≤ 1766537118447^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146091999 5000000000 1766537118447 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677499833/5000000000 : ℝ), (2613625859/5000000000 : ℝ), (-1146091999/5000000000 : ℝ)] ![(43622280492247/100000000000000 : ℝ), (66008472723/156250000000 : ℝ), (1766537118447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677499833/5000000000 : ℝ)|^4143 ≤ (43622280492247/100000000000000 : ℝ)^3119
        have hw : |(2677499833/5000000000 : ℝ)|=(2677499833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613625859/5000000000 : ℝ)|^4143 ≤ (66008472723/156250000000 : ℝ)^3119
        have hw : |(2613625859/5000000000 : ℝ)|=(2613625859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1146091999/5000000000 : ℝ)|^4143 ≤ (1766537118447/12500000000000 : ℝ)^3119
        have hw : |(-1146091999/5000000000 : ℝ)|=(1146091999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17476113/40000000 : ℝ)*x 0 + (4169704307/10000000000 : ℝ)*x 1 + (1144484133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17476113/40000000 : ℝ)^4143 ≤ (6658087090029/20000000000000 : ℝ)^3119 := by
    have hnat : (17476113 : ℕ)^4143*20000000000000^3119 ≤ 6658087090029^3119*40000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17476113 40000000 6658087090029 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169704307/10000000000 : ℝ)^4143 ≤ (7822073438147/25000000000000 : ℝ)^3119 := by
    have hnat : (4169704307 : ℕ)^4143*25000000000000^3119 ≤ 7822073438147^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169704307 10000000000 7822073438147 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144484133/2500000000 : ℝ)^4143 ≤ (17710635388839/50000000000000 : ℝ)^3119 := by
    have hnat : (1144484133 : ℕ)^4143*50000000000000^3119 ≤ 17710635388839^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144484133 2500000000 17710635388839 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17476113/40000000 : ℝ), (4169704307/10000000000 : ℝ), (1144484133/2500000000 : ℝ)] ![(6658087090029/20000000000000 : ℝ), (7822073438147/25000000000000 : ℝ), (17710635388839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17476113/40000000 : ℝ)|^4143 ≤ (6658087090029/20000000000000 : ℝ)^3119
        have hw : |(17476113/40000000 : ℝ)|=(17476113/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169704307/10000000000 : ℝ)|^4143 ≤ (7822073438147/25000000000000 : ℝ)^3119
        have hw : |(4169704307/10000000000 : ℝ)|=(4169704307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1144484133/2500000000 : ℝ)|^4143 ≤ (17710635388839/50000000000000 : ℝ)^3119
        have hw : |(1144484133/2500000000 : ℝ)|=(1144484133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-546545083/2500000000 : ℝ)*x 0 + (65351047/125000000 : ℝ)*x 1 + (5433599629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546545083/2500000000 : ℝ)^4143 ≤ (6635414495919/50000000000000 : ℝ)^3119 := by
    have hnat : (546545083 : ℕ)^4143*50000000000000^3119 ≤ 6635414495919^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546545083 2500000000 6635414495919 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65351047/125000000 : ℝ)^4143 ≤ (21127177412089/50000000000000 : ℝ)^3119 := by
    have hnat : (65351047 : ℕ)^4143*50000000000000^3119 ≤ 21127177412089^3119*125000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65351047 125000000 21127177412089 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433599629/10000000000 : ℝ)^4143 ≤ (44474816163411/100000000000000 : ℝ)^3119 := by
    have hnat : (5433599629 : ℕ)^4143*100000000000000^3119 ≤ 44474816163411^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433599629 10000000000 44474816163411 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546545083/2500000000 : ℝ), (65351047/125000000 : ℝ), (5433599629/10000000000 : ℝ)] ![(6635414495919/50000000000000 : ℝ), (21127177412089/50000000000000 : ℝ), (44474816163411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546545083/2500000000 : ℝ)|^4143 ≤ (6635414495919/50000000000000 : ℝ)^3119
        have hw : |(-546545083/2500000000 : ℝ)|=(546545083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65351047/125000000 : ℝ)|^4143 ≤ (21127177412089/50000000000000 : ℝ)^3119
        have hw : |(65351047/125000000 : ℝ)|=(65351047/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433599629/10000000000 : ℝ)|^4143 ≤ (44474816163411/100000000000000 : ℝ)^3119
        have hw : |(5433599629/10000000000 : ℝ)|=(5433599629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651350727/5000000000 : ℝ)*x 0 + (-2085836413/10000000000 : ℝ)*x 1 + (2716799823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651350727/5000000000 : ℝ)^4143 ≤ (344458363331/800000000000 : ℝ)^3119 := by
    have hnat : (2651350727 : ℕ)^4143*800000000000^3119 ≤ 344458363331^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651350727 5000000000 344458363331 800000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085836413/10000000000 : ℝ)^4143 ≤ (3116972052883/25000000000000 : ℝ)^3119 := by
    have hnat : (2085836413 : ℕ)^4143*25000000000000^3119 ≤ 3116972052883^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085836413 10000000000 3116972052883 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716799823/5000000000 : ℝ)^4143 ≤ (22237408174121/50000000000000 : ℝ)^3119 := by
    have hnat : (2716799823 : ℕ)^4143*50000000000000^3119 ≤ 22237408174121^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716799823 5000000000 22237408174121 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651350727/5000000000 : ℝ), (-2085836413/10000000000 : ℝ), (2716799823/5000000000 : ℝ)] ![(344458363331/800000000000 : ℝ), (3116972052883/25000000000000 : ℝ), (22237408174121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651350727/5000000000 : ℝ)|^4143 ≤ (344458363331/800000000000 : ℝ)^3119
        have hw : |(2651350727/5000000000 : ℝ)|=(2651350727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085836413/10000000000 : ℝ)|^4143 ≤ (3116972052883/25000000000000 : ℝ)^3119
        have hw : |(-2085836413/10000000000 : ℝ)|=(2085836413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716799823/5000000000 : ℝ)|^4143 ≤ (22237408174121/50000000000000 : ℝ)^3119
        have hw : |(2716799823/5000000000 : ℝ)|=(2716799823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302701913/10000000000 : ℝ)*x 0 + (543359999/1000000000 : ℝ)*x 1 + (-2085835321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302701913/10000000000 : ℝ)^4143 ≤ (43057300367021/100000000000000 : ℝ)^3119 := by
    have hnat : (5302701913 : ℕ)^4143*100000000000000^3119 ≤ 43057300367021^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302701913 10000000000 43057300367021 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543359999/1000000000 : ℝ)^4143 ≤ (44474820088353/100000000000000 : ℝ)^3119 := by
    have hnat : (543359999 : ℕ)^4143*100000000000000^3119 ≤ 44474820088353^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543359999 1000000000 44474820088353 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085835321/10000000000 : ℝ)^4143 ≤ (6233939770609/50000000000000 : ℝ)^3119 := by
    have hnat : (2085835321 : ℕ)^4143*50000000000000^3119 ≤ 6233939770609^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085835321 10000000000 6233939770609 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302701913/10000000000 : ℝ), (543359999/1000000000 : ℝ), (-2085835321/10000000000 : ℝ)] ![(43057300367021/100000000000000 : ℝ), (44474820088353/100000000000000 : ℝ), (6233939770609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302701913/10000000000 : ℝ)|^4143 ≤ (43057300367021/100000000000000 : ℝ)^3119
        have hw : |(5302701913/10000000000 : ℝ)|=(5302701913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543359999/1000000000 : ℝ)|^4143 ≤ (44474820088353/100000000000000 : ℝ)^3119
        have hw : |(543359999/1000000000 : ℝ)|=(543359999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085835321/10000000000 : ℝ)|^4143 ≤ (6233939770609/50000000000000 : ℝ)^3119
        have hw : |(-2085835321/10000000000 : ℝ)|=(2085835321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s3_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184534227/5000000000 : ℝ)*x 0 + (4576296927/10000000000 : ℝ)*x 1 + (4171353939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184534227/5000000000 : ℝ)^4143 ≤ (16645421182761/50000000000000 : ℝ)^3119 := by
    have hnat : (2184534227 : ℕ)^4143*50000000000000^3119 ≤ 16645421182761^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184534227 5000000000 16645421182761 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4576296927/10000000000 : ℝ)^4143 ≤ (17702210239041/50000000000000 : ℝ)^3119 := by
    have hnat : (4576296927 : ℕ)^4143*50000000000000^3119 ≤ 17702210239041^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576296927 10000000000 17702210239041 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171353939/10000000000 : ℝ)^4143 ≤ (3913092143283/12500000000000 : ℝ)^3119 := by
    have hnat : (4171353939 : ℕ)^4143*12500000000000^3119 ≤ 3913092143283^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171353939 10000000000 3913092143283 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184534227/5000000000 : ℝ), (4576296927/10000000000 : ℝ), (4171353939/10000000000 : ℝ)] ![(16645421182761/50000000000000 : ℝ), (17702210239041/50000000000000 : ℝ), (3913092143283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184534227/5000000000 : ℝ)|^4143 ≤ (16645421182761/50000000000000 : ℝ)^3119
        have hw : |(2184534227/5000000000 : ℝ)|=(2184534227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4576296927/10000000000 : ℝ)|^4143 ≤ (17702210239041/50000000000000 : ℝ)^3119
        have hw : |(4576296927/10000000000 : ℝ)|=(4576296927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171353939/10000000000 : ℝ)|^4143 ≤ (3913092143283/12500000000000 : ℝ)^3119
        have hw : |(4171353939/10000000000 : ℝ)|=(4171353939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2621/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3717/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16653/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16653/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16653/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16653/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16653/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16653/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8843/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (5477260851302377/100000000000000000000 : ℝ) := by
    have hpowers : (8843/100000 : ℝ)^8285 ≤ (5477260851302377/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8843 : ℕ)^8285*100000000000000000000^2048 ≤ 5477260851302377^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8843 100000 5477260851302377 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8843/100000 : ℝ)) (X := (5477260851302377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16653/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (70895354778569921/100000000000000000000 : ℝ) := by
    have hpowers : (16653/100000 : ℝ)^8285 ≤ (70895354778569921/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16653 : ℕ)^8285*100000000000000000000^2048 ≤ 70895354778569921^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16653 100000 70895354778569921 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16653/100000 : ℝ)) (X := (70895354778569921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005477260851302377/50000000000000000000 : ℝ) ≤ (10000270777736221/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50005477260851302377/50000000000000000000 : ℝ)^2048 ≤ (10000270777736221/10000000000000000 : ℝ)^8285 := by
      have hnat : (50005477260851302377 : ℕ)^2048*10000000000000000^8285 ≤ 10000270777736221^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005477260851302377 50000000000000000000 10000270777736221 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000270777736221/10000000000000000 : ℝ)) (X := (50005477260851302377/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50038186307814936149/50000000000000000000 : ℝ) ≤ (10001887340658153/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50038186307814936149/50000000000000000000 : ℝ)^2048 ≤ (10001887340658153/10000000000000000 : ℝ)^8285 := by
      have hnat : (50038186307814936149 : ℕ)^2048*10000000000000000^8285 ≤ 10001887340658153^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038186307814936149 50000000000000000000 10001887340658153 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001887340658153/10000000000000000 : ℝ)) (X := (50038186307814936149/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50070895354778569921/50000000000000000000 : ℝ) ≤ (2000700780716017/2000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50070895354778569921/50000000000000000000 : ℝ)^2048 ≤ (2000700780716017/2000000000000000 : ℝ)^8285 := by
      have hnat : (50070895354778569921 : ℕ)^2048*2000000000000000^8285 ≤ 2000700780716017^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070895354778569921 50000000000000000000 2000700780716017 2000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000700780716017/2000000000000000 : ℝ)) (X := (50070895354778569921/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477260851302377/100000000000000000000 : ℝ) ≤ ((39036762121141298329/39050000000000000000 : ℝ)+2*(404140730483/195250000000000 : ℝ)*(8843/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (39036762121141298329/39050000000000000000 : ℝ)+2*(404140730483/195250000000000 : ℝ)*(8843/100000 : ℝ)=(10000270777736221/10000000000000000 : ℝ) by norm_num, show 1+2*(5477260851302377/100000000000000000000 : ℝ)=(50005477260851302377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70895354778569921/100000000000000000000 : ℝ)+(5477260851302377/100000000000000000000 : ℝ) ≤ ((39036762121141298329/39050000000000000000 : ℝ)+(404140730483/195250000000000 : ℝ)*((16653/100000 : ℝ)+(8843/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (39036762121141298329/39050000000000000000 : ℝ)+(404140730483/195250000000000 : ℝ)*((16653/100000 : ℝ)+(8843/100000 : ℝ))=(10001887340658153/10000000000000000 : ℝ) by norm_num, show 1+(70895354778569921/100000000000000000000 : ℝ)+(5477260851302377/100000000000000000000 : ℝ)=(50038186307814936149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70895354778569921/100000000000000000000 : ℝ) ≤ ((39036762121141298329/39050000000000000000 : ℝ)+2*(404140730483/195250000000000 : ℝ)*(16653/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (39036762121141298329/39050000000000000000 : ℝ)+2*(404140730483/195250000000000 : ℝ)*(16653/100000 : ℝ)=(2000700780716017/2000000000000000 : ℝ) by norm_num, show 1+2*(70895354778569921/100000000000000000000 : ℝ)=(50070895354778569921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39036762121141298329/39050000000000000000 : ℝ)*(X 1 0+X 2 0)+(404140730483/195250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (8843/100000 : ℝ)) (hi := (16653/100000 : ℝ)) (c := (39036762121141298329/39050000000000000000 : ℝ)) (alpha := (404140730483/195250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39036762121141298329/39050000000000000000 : ℝ)*(X 0 1+X 2 1)+(404140730483/195250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (8843/100000 : ℝ)) (hi := (16653/100000 : ℝ)) (c := (39036762121141298329/39050000000000000000 : ℝ)) (alpha := (404140730483/195250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39036762121141298329/39050000000000000000 : ℝ)*(X 0 2+X 1 2)+(404140730483/195250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (8843/100000 : ℝ)) (hi := (16653/100000 : ℝ)) (c := (39036762121141298329/39050000000000000000 : ℝ)) (alpha := (404140730483/195250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87446363/400000000 : ℝ)*X 0 0+(42456541/78125000 : ℝ)*X 0 1+(2613625697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354999789/10000000000 : ℝ)*X 1 0+(-1146092209/5000000000 : ℝ)*X 1 1+(2613625637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677499833/5000000000 : ℝ)*X 2 0+(2613625859/5000000000 : ℝ)*X 2 1+(-1146091999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17476113/40000000 : ℝ)*X 0 0+(4169704307/10000000000 : ℝ)*X 0 1+(1144484133/2500000000 : ℝ)*X 0 2+(17476113/40000000 : ℝ)*X 1 0+(4169704307/10000000000 : ℝ)*X 1 1+(1144484133/2500000000 : ℝ)*X 1 2+(17476113/40000000 : ℝ)*X 2 0+(4169704307/10000000000 : ℝ)*X 2 1+(1144484133/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-546545083/2500000000 : ℝ)*X 0 0+(65351047/125000000 : ℝ)*X 0 1+(5433599629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651350727/5000000000 : ℝ)*X 1 0+(-2085836413/10000000000 : ℝ)*X 1 1+(2716799823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302701913/10000000000 : ℝ)*X 2 0+(543359999/1000000000 : ℝ)*X 2 1+(-2085835321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184534227/5000000000 : ℝ)*X 0 0+(4576296927/10000000000 : ℝ)*X 0 1+(4171353939/10000000000 : ℝ)*X 0 2+(2184534227/5000000000 : ℝ)*X 1 0+(4576296927/10000000000 : ℝ)*X 1 1+(4171353939/10000000000 : ℝ)*X 1 2+(2184534227/5000000000 : ℝ)*X 2 0+(4576296927/10000000000 : ℝ)*X 2 1+(4171353939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133519143283910227181253/19525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912697559/50000000000000 : ℝ)*(base19) + (1314847271/100000000000000 : ℝ)*(base23) + (214030601/100000000000000 : ℝ)*(lower2) + (17823201/20000000000000 : ℝ)*(upper3) + (179401679/100000000000000 : ℝ)*(upper5) + (1819065643039507/50000000000000 : ℝ)*(major0) + (1819065643039507/50000000000000 : ℝ)*(major1) + (1819065643039507/50000000000000 : ℝ)*(major2) + (482661338471721/10000000000000 : ℝ)*(sp0) + (4826646654336827/100000000000000 : ℝ)*(sp1) + (4826647164884673/100000000000000 : ℝ)*(sp2) + (244960000233517/10000000000000 : ℝ)*(sp3) + (17547507367/50000000000000 : ℝ)*(sp4) + (6931072647/50000000000000 : ℝ)*(sp7) + (153100866530029/6250000000000 : ℝ)*(f.failure) + (603331059966493/12500000000000 : ℝ)*(f.sum) + (32535398444037/9762500000000000000000000000 : ℝ)*base65 + (11092695697976283803/1952500000000000000000000000000000 : ℝ)*base67 + (4037854109033716197/1952500000000000000000000000000000 : ℝ)*base70 + (5357049600448783803/1952500000000000000000000000000000 : ℝ)*base71 + (60006961136237/9762500000000000000000000000 : ℝ)*base73 + (31139809902363716197/1952500000000000000000000000000000 : ℝ)*base76 + (12535240681911283803/1952500000000000000000000000000000 : ℝ)*base77 + (5414442776058716197/1952500000000000000000000000000000 : ℝ)*base80 + (1258492448993/610156250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (300851/312500000000000000000 : ℝ)*base90 + (300851/312500000000000000000 : ℝ)*base92 + (300851/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3042302627024057617486409079/488125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (693787339/50000000000000 : ℝ)*(base19) + (159382677/6250000000000 : ℝ)*(base23) + (40790093/20000000000000 : ℝ)*(upper2) + (233798427/100000000000000 : ℝ)*(upper3) + (33629753/20000000000000 : ℝ)*(upper5) + (1833822348061083/50000000000000 : ℝ)*(major0) + (1833822348061083/50000000000000 : ℝ)*(major1) + (1833822348061083/50000000000000 : ℝ)*(major2) + (791080803/4000000000000 : ℝ)*(sp1) + (6993712877/12500000000000 : ℝ)*(sp2) + (486580345372849/10000000000000 : ℝ)*(sp4) + (4865782289133737/100000000000000 : ℝ)*(sp5) + (2432872476951321/50000000000000 : ℝ)*(sp6) + (308685716345187/12500000000000 : ℝ)*(sp7) + (308685716345187/12500000000000 : ℝ)*(f.failure) + (486580345372849/10000000000000 : ℝ)*(f.sum) + (7523103542061/4881250000000000000000000000 : ℝ)*base66 + (3183734011655630307/1952500000000000000000000000000000 : ℝ)*base67 + (3769644581350630307/1952500000000000000000000000000000 : ℝ)*base69 + (2890625170493130307/1952500000000000000000000000000000 : ℝ)*base71 + (16771929031331/19525000000000000000000000000 : ℝ)*base73 + (15393946188345630307/1952500000000000000000000000000000 : ℝ)*base75 + (8364032008629369693/1952500000000000000000000000000000 : ℝ)*base78 + (7108976227385630307/1952500000000000000000000000000000 : ℝ)*base79 + (48045040711003/9762500000000000000000000000 : ℝ)*base81 + (3069453/625000000000000000000 : ℝ)*base90 + (3069453/625000000000000000000 : ℝ)*base92 + (3069453/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1093_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3717/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1093_s4_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189582429/10000000000 : ℝ)*x 0 + (5404354639/10000000000 : ℝ)*x 1 + (262754817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189582429/10000000000 : ℝ)^4143 ≤ (13298268050659/100000000000000 : ℝ)^3119 := by
    have hnat : (2189582429 : ℕ)^4143*100000000000000^3119 ≤ 13298268050659^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189582429 10000000000 13298268050659 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404354639/10000000000 : ℝ)^4143 ≤ (44157133716153/100000000000000 : ℝ)^3119 := by
    have hnat : (5404354639 : ℕ)^4143*100000000000000^3119 ≤ 44157133716153^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404354639 10000000000 44157133716153 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262754817/500000000 : ℝ)^4143 ≤ (42544598211031/100000000000000 : ℝ)^3119 := by
    have hnat : (262754817 : ℕ)^4143*100000000000000^3119 ≤ 42544598211031^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262754817 500000000 42544598211031 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189582429/10000000000 : ℝ), (5404354639/10000000000 : ℝ), (262754817/500000000 : ℝ)] ![(13298268050659/100000000000000 : ℝ), (44157133716153/100000000000000 : ℝ), (42544598211031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189582429/10000000000 : ℝ)|^4143 ≤ (13298268050659/100000000000000 : ℝ)^3119
        have hw : |(-2189582429/10000000000 : ℝ)|=(2189582429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404354639/10000000000 : ℝ)|^4143 ≤ (44157133716153/100000000000000 : ℝ)^3119
        have hw : |(5404354639/10000000000 : ℝ)|=(5404354639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262754817/500000000 : ℝ)|^4143 ≤ (42544598211031/100000000000000 : ℝ)^3119
        have hw : |(262754817/500000000 : ℝ)|=(262754817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83555091/156250000 : ℝ)*x 0 + (-2265472939/10000000000 : ℝ)*x 1 + (5255097281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83555091/156250000 : ℝ)^4143 ≤ (43541428105209/100000000000000 : ℝ)^3119 := by
    have hnat : (83555091 : ℕ)^4143*100000000000000^3119 ≤ 43541428105209^3119*156250000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83555091 156250000 43541428105209 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265472939/10000000000 : ℝ)^4143 ≤ (6956981769327/50000000000000 : ℝ)^3119 := by
    have hnat : (2265472939 : ℕ)^4143*50000000000000^3119 ≤ 6956981769327^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265472939 10000000000 6956981769327 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255097281/10000000000 : ℝ)^4143 ≤ (42544608330389/100000000000000 : ℝ)^3119 := by
    have hnat : (5255097281 : ℕ)^4143*100000000000000^3119 ≤ 42544608330389^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255097281 10000000000 42544608330389 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83555091/156250000 : ℝ), (-2265472939/10000000000 : ℝ), (5255097281/10000000000 : ℝ)] ![(43541428105209/100000000000000 : ℝ), (6956981769327/50000000000000 : ℝ), (42544608330389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83555091/156250000 : ℝ)|^4143 ≤ (43541428105209/100000000000000 : ℝ)^3119
        have hw : |(83555091/156250000 : ℝ)|=(83555091/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265472939/10000000000 : ℝ)|^4143 ≤ (6956981769327/50000000000000 : ℝ)^3119
        have hw : |(-2265472939/10000000000 : ℝ)|=(2265472939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255097281/10000000000 : ℝ)|^4143 ≤ (42544608330389/100000000000000 : ℝ)^3119
        have hw : |(5255097281/10000000000 : ℝ)|=(5255097281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534752591/1000000000 : ℝ)*x 0 + (5255097057/10000000000 : ℝ)*x 1 + (-1132736561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534752591/1000000000 : ℝ)^4143 ≤ (10885357258837/25000000000000 : ℝ)^3119 := by
    have hnat : (534752591 : ℕ)^4143*25000000000000^3119 ≤ 10885357258837^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534752591 1000000000 10885357258837 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255097057/10000000000 : ℝ)^4143 ≤ (4254460592153/10000000000000 : ℝ)^3119 := by
    have hnat : (5255097057 : ℕ)^4143*10000000000000^3119 ≤ 4254460592153^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255097057 10000000000 4254460592153 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132736561/5000000000 : ℝ)^4143 ≤ (2782793006319/20000000000000 : ℝ)^3119 := by
    have hnat : (1132736561 : ℕ)^4143*20000000000000^3119 ≤ 2782793006319^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132736561 5000000000 2782793006319 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534752591/1000000000 : ℝ), (5255097057/10000000000 : ℝ), (-1132736561/5000000000 : ℝ)] ![(10885357258837/25000000000000 : ℝ), (4254460592153/10000000000000 : ℝ), (2782793006319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534752591/1000000000 : ℝ)|^4143 ≤ (10885357258837/25000000000000 : ℝ)^3119
        have hw : |(534752591/1000000000 : ℝ)|=(534752591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255097057/10000000000 : ℝ)|^4143 ≤ (4254460592153/10000000000000 : ℝ)^3119
        have hw : |(5255097057/10000000000 : ℝ)|=(5255097057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132736561/5000000000 : ℝ)|^4143 ≤ (2782793006319/20000000000000 : ℝ)^3119
        have hw : |(-1132736561/5000000000 : ℝ)|=(1132736561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371066201/10000000000 : ℝ)*x 0 + (2113253737/5000000000 : ℝ)*x 1 + (1130150173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371066201/10000000000 : ℝ)^4143 ≤ (4163882955291/12500000000000 : ℝ)^3119 := by
    have hnat : (4371066201 : ℕ)^4143*12500000000000^3119 ≤ 4163882955291^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371066201 10000000000 4163882955291 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113253737/5000000000 : ℝ)^4143 ≤ (15927864233781/50000000000000 : ℝ)^3119 := by
    have hnat : (2113253737 : ℕ)^4143*50000000000000^3119 ≤ 15927864233781^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113253737 5000000000 15927864233781 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130150173/2500000000 : ℝ)^4143 ≤ (8708301968913/25000000000000 : ℝ)^3119 := by
    have hnat : (1130150173 : ℕ)^4143*25000000000000^3119 ≤ 8708301968913^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130150173 2500000000 8708301968913 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371066201/10000000000 : ℝ), (2113253737/5000000000 : ℝ), (1130150173/2500000000 : ℝ)] ![(4163882955291/12500000000000 : ℝ), (15927864233781/50000000000000 : ℝ), (8708301968913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371066201/10000000000 : ℝ)|^4143 ≤ (4163882955291/12500000000000 : ℝ)^3119
        have hw : |(4371066201/10000000000 : ℝ)|=(4371066201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113253737/5000000000 : ℝ)|^4143 ≤ (15927864233781/50000000000000 : ℝ)^3119
        have hw : |(2113253737/5000000000 : ℝ)|=(2113253737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130150173/2500000000 : ℝ)|^4143 ≤ (8708301968913/25000000000000 : ℝ)^3119
        have hw : |(1130150173/2500000000 : ℝ)|=(1130150173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-54739727/250000000 : ℝ)*x 0 + (1313882489/2500000000 : ℝ)*x 1 + (5403920037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54739727/250000000 : ℝ)^4143 ≤ (13298321706933/100000000000000 : ℝ)^3119 := by
    have hnat : (54739727 : ℕ)^4143*100000000000000^3119 ≤ 13298321706933^3119*250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54739727 250000000 13298321706933 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313882489/2500000000 : ℝ)^4143 ≤ (21274630654201/50000000000000 : ℝ)^3119 := by
    have hnat : (1313882489 : ℕ)^4143*50000000000000^3119 ≤ 21274630654201^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313882489 2500000000 21274630654201 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403920037/10000000000 : ℝ)^4143 ≤ (44152416969163/100000000000000 : ℝ)^3119 := by
    have hnat : (5403920037 : ℕ)^4143*100000000000000^3119 ≤ 44152416969163^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403920037 10000000000 44152416969163 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54739727/250000000 : ℝ), (1313882489/2500000000 : ℝ), (5403920037/10000000000 : ℝ)] ![(13298321706933/100000000000000 : ℝ), (21274630654201/50000000000000 : ℝ), (44152416969163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54739727/250000000 : ℝ)|^4143 ≤ (13298321706933/100000000000000 : ℝ)^3119
        have hw : |(-54739727/250000000 : ℝ)|=(54739727/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313882489/2500000000 : ℝ)|^4143 ≤ (21274630654201/50000000000000 : ℝ)^3119
        have hw : |(1313882489/2500000000 : ℝ)|=(1313882489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403920037/10000000000 : ℝ)|^4143 ≤ (44152416969163/100000000000000 : ℝ)^3119
        have hw : |(5403920037/10000000000 : ℝ)|=(5403920037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309852877/10000000000 : ℝ)*x 0 + (-2116650147/10000000000 : ℝ)*x 1 + (5403920161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309852877/10000000000 : ℝ)^4143 ≤ (2156722286559/5000000000000 : ℝ)^3119 := by
    have hnat : (5309852877 : ℕ)^4143*5000000000000^3119 ≤ 2156722286559^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309852877 10000000000 2156722286559 5000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116650147/10000000000 : ℝ)^4143 ≤ (12713135940723/100000000000000 : ℝ)^3119 := by
    have hnat : (2116650147 : ℕ)^4143*100000000000000^3119 ≤ 12713135940723^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116650147 10000000000 12713135940723 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403920161/10000000000 : ℝ)^4143 ≤ (44152418314921/100000000000000 : ℝ)^3119 := by
    have hnat : (5403920161 : ℕ)^4143*100000000000000^3119 ≤ 44152418314921^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403920161 10000000000 44152418314921 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309852877/10000000000 : ℝ), (-2116650147/10000000000 : ℝ), (5403920161/10000000000 : ℝ)] ![(2156722286559/5000000000000 : ℝ), (12713135940723/100000000000000 : ℝ), (44152418314921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309852877/10000000000 : ℝ)|^4143 ≤ (2156722286559/5000000000000 : ℝ)^3119
        have hw : |(5309852877/10000000000 : ℝ)|=(5309852877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116650147/10000000000 : ℝ)|^4143 ≤ (12713135940723/100000000000000 : ℝ)^3119
        have hw : |(-2116650147/10000000000 : ℝ)|=(2116650147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403920161/10000000000 : ℝ)|^4143 ≤ (44152418314921/100000000000000 : ℝ)^3119
        have hw : |(5403920161/10000000000 : ℝ)|=(5403920161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309852771/10000000000 : ℝ)*x 0 + (216156807/400000000 : ℝ)*x 1 + (-2116650271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309852771/10000000000 : ℝ)^4143 ≤ (43134444587387/100000000000000 : ℝ)^3119 := by
    have hnat : (5309852771 : ℕ)^4143*100000000000000^3119 ≤ 43134444587387^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309852771 10000000000 43134444587387 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216156807/400000000 : ℝ)^4143 ≤ (44152418466861/100000000000000 : ℝ)^3119 := by
    have hnat : (216156807 : ℕ)^4143*100000000000000^3119 ≤ 44152418466861^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216156807 400000000 44152418466861 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116650271/10000000000 : ℝ)^4143 ≤ (397285529063/3125000000000 : ℝ)^3119 := by
    have hnat : (2116650271 : ℕ)^4143*3125000000000^3119 ≤ 397285529063^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116650271 10000000000 397285529063 3125000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309852771/10000000000 : ℝ), (216156807/400000000 : ℝ), (-2116650271/10000000000 : ℝ)] ![(43134444587387/100000000000000 : ℝ), (44152418466861/100000000000000 : ℝ), (397285529063/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309852771/10000000000 : ℝ)|^4143 ≤ (43134444587387/100000000000000 : ℝ)^3119
        have hw : |(5309852771/10000000000 : ℝ)|=(5309852771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216156807/400000000 : ℝ)|^4143 ≤ (44152418466861/100000000000000 : ℝ)^3119
        have hw : |(216156807/400000000 : ℝ)|=(216156807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2116650271/10000000000 : ℝ)|^4143 ≤ (397285529063/3125000000000 : ℝ)^3119
        have hw : |(-2116650271/10000000000 : ℝ)|=(2116650271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092770197/2500000000 : ℝ)*x 0 + (2259873961/5000000000 : ℝ)*x 1 + (2113682241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092770197/2500000000 : ℝ)^4143 ≤ (33311211303699/100000000000000 : ℝ)^3119 := by
    have hnat : (1092770197 : ℕ)^4143*100000000000000^3119 ≤ 33311211303699^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092770197 2500000000 33311211303699 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259873961/5000000000 : ℝ)^4143 ≤ (17412239931699/50000000000000 : ℝ)^3119 := by
    have hnat : (2259873961 : ℕ)^4143*50000000000000^3119 ≤ 17412239931699^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259873961 5000000000 17412239931699 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113682241/5000000000 : ℝ)^4143 ≤ (1274572352533/4000000000000 : ℝ)^3119 := by
    have hnat : (2113682241 : ℕ)^4143*4000000000000^3119 ≤ 1274572352533^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113682241 5000000000 1274572352533 4000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092770197/2500000000 : ℝ), (2259873961/5000000000 : ℝ), (2113682241/5000000000 : ℝ)] ![(33311211303699/100000000000000 : ℝ), (17412239931699/50000000000000 : ℝ), (1274572352533/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092770197/2500000000 : ℝ)|^4143 ≤ (33311211303699/100000000000000 : ℝ)^3119
        have hw : |(1092770197/2500000000 : ℝ)|=(1092770197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259873961/5000000000 : ℝ)|^4143 ≤ (17412239931699/50000000000000 : ℝ)^3119
        have hw : |(2259873961/5000000000 : ℝ)|=(2259873961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113682241/5000000000 : ℝ)|^4143 ≤ (1274572352533/4000000000000 : ℝ)^3119
        have hw : |(2113682241/5000000000 : ℝ)|=(2113682241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_8 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18298397/10000000000 : ℝ)*x 0 + (2966663321/5000000000 : ℝ)*x 1 + (118666507/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18298397/10000000000 : ℝ)^4143 ≤ (2310121907/10000000000000 : ℝ)^3119 := by
    have hnat : (18298397 : ℕ)^4143*10000000000000^3119 ≤ 2310121907^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18298397 10000000000 2310121907 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2966663321/5000000000 : ℝ)^4143 ≤ (12497114152683/25000000000000 : ℝ)^3119 := by
    have hnat : (2966663321 : ℕ)^4143*25000000000000^3119 ≤ 12497114152683^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966663321 5000000000 12497114152683 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118666507/200000000 : ℝ)^4143 ≤ (4998844215189/10000000000000 : ℝ)^3119 := by
    have hnat : (118666507 : ℕ)^4143*10000000000000^3119 ≤ 4998844215189^3119*200000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118666507 200000000 4998844215189 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18298397/10000000000 : ℝ), (2966663321/5000000000 : ℝ), (118666507/200000000 : ℝ)] ![(2310121907/10000000000000 : ℝ), (12497114152683/25000000000000 : ℝ), (4998844215189/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18298397/10000000000 : ℝ)|^4143 ≤ (2310121907/10000000000000 : ℝ)^3119
        have hw : |(-18298397/10000000000 : ℝ)|=(18298397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2966663321/5000000000 : ℝ)|^4143 ≤ (12497114152683/25000000000000 : ℝ)^3119
        have hw : |(2966663321/5000000000 : ℝ)|=(2966663321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118666507/200000000 : ℝ)|^4143 ≤ (4998844215189/10000000000000 : ℝ)^3119
        have hw : |(118666507/200000000 : ℝ)|=(118666507/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s4_9 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1390598503/10000000000 : ℝ)*x 0 + (2802939089/5000000000 : ℝ)*x 1 + (1401665609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1390598503/10000000000 : ℝ)^4143 ≤ (7276223349593/100000000000000 : ℝ)^3119 := by
    have hnat : (1390598503 : ℕ)^4143*100000000000000^3119 ≤ 7276223349593^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390598503 10000000000 7276223349593 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2802939089/5000000000 : ℝ)^4143 ≤ (46357580913577/100000000000000 : ℝ)^3119 := by
    have hnat : (2802939089 : ℕ)^4143*100000000000000^3119 ≤ 46357580913577^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802939089 5000000000 46357580913577 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401665609/2500000000 : ℝ)^4143 ≤ (46366195721493/100000000000000 : ℝ)^3119 := by
    have hnat : (1401665609 : ℕ)^4143*100000000000000^3119 ≤ 46366195721493^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401665609 2500000000 46366195721493 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1390598503/10000000000 : ℝ), (2802939089/5000000000 : ℝ), (1401665609/2500000000 : ℝ)] ![(7276223349593/100000000000000 : ℝ), (46357580913577/100000000000000 : ℝ), (46366195721493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1390598503/10000000000 : ℝ)|^4143 ≤ (7276223349593/100000000000000 : ℝ)^3119
        have hw : |(1390598503/10000000000 : ℝ)|=(1390598503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2802939089/5000000000 : ℝ)|^4143 ≤ (46357580913577/100000000000000 : ℝ)^3119
        have hw : |(2802939089/5000000000 : ℝ)|=(2802939089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401665609/2500000000 : ℝ)|^4143 ≤ (46366195721493/100000000000000 : ℝ)^3119
        have hw : |(1401665609/2500000000 : ℝ)|=(1401665609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3717/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11079/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3717/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2621/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3717/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2621/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3717/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2621/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3717/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2621/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3717/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2621/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3717/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2621/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2621/25000 : ℝ) ^ (8285/2048 : ℝ) ≤ (10905109422761143/100000000000000000000 : ℝ) := by
    have hpowers : (2621/25000 : ℝ)^8285 ≤ (10905109422761143/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2621 : ℕ)^8285*100000000000000000000^2048 ≤ 10905109422761143^2048*25000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2621 25000 10905109422761143 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2621/25000 : ℝ)) (X := (10905109422761143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3717/25000 : ℝ) ^ (8285/2048 : ℝ) ≤ (44814862551253791/100000000000000000000 : ℝ) := by
    have hpowers : (3717/25000 : ℝ)^8285 ≤ (44814862551253791/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3717 : ℕ)^8285*100000000000000000000^2048 ≤ 44814862551253791^2048*25000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3717 25000 44814862551253791 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3717/25000 : ℝ)) (X := (44814862551253791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010905109422761143/50000000000000000000 : ℝ) ≤ (10000539090666599/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50010905109422761143/50000000000000000000 : ℝ)^2048 ≤ (10000539090666599/10000000000000000 : ℝ)^8285 := by
      have hnat : (50010905109422761143 : ℕ)^2048*10000000000000000^8285 ≤ 10000539090666599^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010905109422761143 50000000000000000000 10000539090666599 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539090666599/10000000000000000 : ℝ)) (X := (50010905109422761143/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027859985987007467/50000000000000000000 : ℝ) ≤ (10001377073952447/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50027859985987007467/50000000000000000000 : ℝ)^2048 ≤ (10001377073952447/10000000000000000 : ℝ)^8285 := by
      have hnat : (50027859985987007467 : ℕ)^2048*10000000000000000^8285 ≤ 10001377073952447^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027859985987007467 50000000000000000000 10001377073952447 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001377073952447/10000000000000000 : ℝ)) (X := (50027859985987007467/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044814862551253791/50000000000000000000 : ℝ) ≤ (2000443011447659/2000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50044814862551253791/50000000000000000000 : ℝ)^2048 ≤ (2000443011447659/2000000000000000 : ℝ)^8285 := by
      have hnat : (50044814862551253791 : ℕ)^2048*2000000000000000^8285 ≤ 2000443011447659^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044814862551253791 50000000000000000000 2000443011447659 2000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000443011447659/2000000000000000 : ℝ)) (X := (50044814862551253791/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10905109422761143/100000000000000000000 : ℝ) ≤ ((1369524766873272161/1370000000000000000 : ℝ)+2*(104747910731/54800000000000 : ℝ)*(2621/25000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (1369524766873272161/1370000000000000000 : ℝ)+2*(104747910731/54800000000000 : ℝ)*(2621/25000 : ℝ)=(10000539090666599/10000000000000000 : ℝ) by norm_num, show 1+2*(10905109422761143/100000000000000000000 : ℝ)=(50010905109422761143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44814862551253791/100000000000000000000 : ℝ)+(10905109422761143/100000000000000000000 : ℝ) ≤ ((1369524766873272161/1370000000000000000 : ℝ)+(104747910731/54800000000000 : ℝ)*((3717/25000 : ℝ)+(2621/25000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (1369524766873272161/1370000000000000000 : ℝ)+(104747910731/54800000000000 : ℝ)*((3717/25000 : ℝ)+(2621/25000 : ℝ))=(10001377073952447/10000000000000000 : ℝ) by norm_num, show 1+(44814862551253791/100000000000000000000 : ℝ)+(10905109422761143/100000000000000000000 : ℝ)=(50027859985987007467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44814862551253791/100000000000000000000 : ℝ) ≤ ((1369524766873272161/1370000000000000000 : ℝ)+2*(104747910731/54800000000000 : ℝ)*(3717/25000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (1369524766873272161/1370000000000000000 : ℝ)+2*(104747910731/54800000000000 : ℝ)*(3717/25000 : ℝ)=(2000443011447659/2000000000000000 : ℝ) by norm_num, show 1+2*(44814862551253791/100000000000000000000 : ℝ)=(50044814862551253791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1369524766873272161/1370000000000000000 : ℝ)*(X 1 0+X 2 0)+(104747910731/54800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (3717/25000 : ℝ)) (c := (1369524766873272161/1370000000000000000 : ℝ)) (alpha := (104747910731/54800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1369524766873272161/1370000000000000000 : ℝ)*(X 0 1+X 2 1)+(104747910731/54800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (3717/25000 : ℝ)) (c := (1369524766873272161/1370000000000000000 : ℝ)) (alpha := (104747910731/54800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1369524766873272161/1370000000000000000 : ℝ)*(X 0 2+X 1 2)+(104747910731/54800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (3717/25000 : ℝ)) (c := (1369524766873272161/1370000000000000000 : ℝ)) (alpha := (104747910731/54800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189582429/10000000000 : ℝ)*X 0 0+(5404354639/10000000000 : ℝ)*X 0 1+(262754817/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83555091/156250000 : ℝ)*X 1 0+(-2265472939/10000000000 : ℝ)*X 1 1+(5255097281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534752591/1000000000 : ℝ)*X 2 0+(5255097057/10000000000 : ℝ)*X 2 1+(-1132736561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371066201/10000000000 : ℝ)*X 0 0+(2113253737/5000000000 : ℝ)*X 0 1+(1130150173/2500000000 : ℝ)*X 0 2+(4371066201/10000000000 : ℝ)*X 1 0+(2113253737/5000000000 : ℝ)*X 1 1+(1130150173/2500000000 : ℝ)*X 1 2+(4371066201/10000000000 : ℝ)*X 2 0+(2113253737/5000000000 : ℝ)*X 2 1+(1130150173/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-54739727/250000000 : ℝ)*X 0 0+(1313882489/2500000000 : ℝ)*X 0 1+(5403920037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309852877/10000000000 : ℝ)*X 1 0+(-2116650147/10000000000 : ℝ)*X 1 1+(5403920161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309852771/10000000000 : ℝ)*X 2 0+(216156807/400000000 : ℝ)*X 2 1+(-2116650271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092770197/2500000000 : ℝ)*X 0 0+(2259873961/5000000000 : ℝ)*X 0 1+(2113682241/5000000000 : ℝ)*X 0 2+(1092770197/2500000000 : ℝ)*X 1 0+(2259873961/5000000000 : ℝ)*X 1 1+(2113682241/5000000000 : ℝ)*X 1 2+(1092770197/2500000000 : ℝ)*X 2 0+(2259873961/5000000000 : ℝ)*X 2 1+(2113682241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-18298397/10000000000 : ℝ)*X 0 0+(2966663321/5000000000 : ℝ)*X 0 1+(118666507/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1390598503/10000000000 : ℝ)*X 0 0+(2802939089/5000000000 : ℝ)*X 0 1+(1401665609/2500000000 : ℝ)*X 0 2+(1390598503/10000000000 : ℝ)*X 1 0+(2802939089/5000000000 : ℝ)*X 1 1+(1401665609/2500000000 : ℝ)*X 1 2+(1390598503/10000000000 : ℝ)*X 2 0+(2802939089/5000000000 : ℝ)*X 2 1+(1401665609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s4_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5902087671955075854411/2740000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18843437/10000000000000 : ℝ)*(lower2) + (26163143/20000000000000 : ℝ)*(lower4) + (59574349/20000000000000 : ℝ)*(lower5) + (5050068954612727/100000000000000 : ℝ)*(major0) + (5050068954612727/100000000000000 : ℝ)*(major1) + (5050068954612727/100000000000000 : ℝ)*(major2) + (1674955259121317/25000000000000 : ℝ)*(sp0) + (1674960757017551/25000000000000 : ℝ)*(sp1) + (1674960757017551/25000000000000 : ℝ)*(sp2) + (340028486050701/10000000000000 : ℝ)*(sp3) + (16265002159/100000000000000 : ℝ)*(sp4) + (1689948683/20000000000000 : ℝ)*(sp7) + (5726582777/100000000000000 : ℝ)*(sp8) + (299820651/20000000000000 : ℝ)*(sp9) + (42503685116921/1250000000000 : ℝ)*(f.failure) + (1674960757017551/25000000000000 : ℝ)*(f.sum) + (7647293953723/2740000000000000000000000000 : ℝ)*base66 + (5186778956588681953/137000000000000000000000000000000 : ℝ)*base68 + (4531640604509681953/137000000000000000000000000000000 : ℝ)*base70 + (2849191472294318047/137000000000000000000000000000000 : ℝ)*base71 + (745964274477/2740000000000000000000000000 : ℝ)*base73 + (266959298336681953/137000000000000000000000000000000 : ℝ)*base76 + (9642468328766318047/137000000000000000000000000000000 : ℝ)*base77 + (68923062705318047/137000000000000000000000000000000 : ℝ)*base79 + (544912849643/2740000000000000000000000000 : ℝ)*base82 + (18801/62500000000000000000 : ℝ)*base89 + (18801/62500000000000000000 : ℝ)*base91 + (18801/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (264080452092303089249502357/34250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50563187/25000000000000 : ℝ)*(lower3) + (87376557/100000000000000 : ℝ)*(lower4) + (38644851/25000000000000 : ℝ)*(lower5) + (5079580363466979/100000000000000 : ℝ)*(major0) + (5079580363466979/100000000000000 : ℝ)*(major1) + (5079580363466979/100000000000000 : ℝ)*(major2) + (6217983121/50000000000000 : ℝ)*(sp1) + (65631361/800000000000 : ℝ)*(sp2) + (1684748309704473/25000000000000 : ℝ)*(sp4) + (6738982705753921/100000000000000 : ℝ)*(sp5) + (6738986937800037/100000000000000 : ℝ)*(sp6) + (684032801919093/20000000000000 : ℝ)*(sp7) + (1902902271/100000000000000 : ℝ)*(sp8) + (1318605719/100000000000000 : ℝ)*(sp9) + (106880166506287/3125000000000 : ℝ)*(f.failure) + (6738995141720163/100000000000000 : ℝ)*(f.sum) + (3209445744551/2740000000000000000000000000 : ℝ)*base66 + (911237066607303381/137000000000000000000000000000000 : ℝ)*base68 + (1091593048621303381/137000000000000000000000000000000 : ℝ)*base70 + (683699293820696619/137000000000000000000000000000000 : ℝ)*base71 + (34163644733269/2740000000000000000000000000 : ℝ)*base73 + (196834736394303381/137000000000000000000000000000000 : ℝ)*base76 + (104485976003303381/137000000000000000000000000000000 : ℝ)*base78 + (874143202249303381/137000000000000000000000000000000 : ℝ)*base80 + (2556009628269/2740000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (87853/156250000000000000000 : ℝ)*base90 + (87853/156250000000000000000 : ℝ)*base92 + (87853/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1093_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3717/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1093_s5_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190336059/10000000000 : ℝ)*x 0 + (1079246427/2000000000 : ℝ)*x 1 + (2631362319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190336059/10000000000 : ℝ)^4143 ≤ (3326087056331/25000000000000 : ℝ)^3119 := by
    have hnat : (2190336059 : ℕ)^4143*25000000000000^3119 ≤ 3326087056331^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190336059 10000000000 3326087056331 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079246427/2000000000 : ℝ)^4143 ≤ (22034500279297/50000000000000 : ℝ)^3119 := by
    have hnat : (1079246427 : ℕ)^4143*50000000000000^3119 ≤ 22034500279297^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079246427 2000000000 22034500279297 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631362319/5000000000 : ℝ)^4143 ≤ (42626651197839/100000000000000 : ℝ)^3119 := by
    have hnat : (2631362319 : ℕ)^4143*100000000000000^3119 ≤ 42626651197839^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631362319 5000000000 42626651197839 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190336059/10000000000 : ℝ), (1079246427/2000000000 : ℝ), (2631362319/5000000000 : ℝ)] ![(3326087056331/25000000000000 : ℝ), (22034500279297/50000000000000 : ℝ), (42626651197839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190336059/10000000000 : ℝ)|^4143 ≤ (3326087056331/25000000000000 : ℝ)^3119
        have hw : |(-2190336059/10000000000 : ℝ)|=(2190336059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079246427/2000000000 : ℝ)|^4143 ≤ (22034500279297/50000000000000 : ℝ)^3119
        have hw : |(1079246427/2000000000 : ℝ)|=(1079246427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631362319/5000000000 : ℝ)|^4143 ≤ (42626651197839/100000000000000 : ℝ)^3119
        have hw : |(2631362319/5000000000 : ℝ)|=(2631362319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267274939/500000000 : ℝ)*x 0 + (-2258101971/10000000000 : ℝ)*x 1 + (2631361423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267274939/500000000 : ℝ)^4143 ≤ (10879876459261/25000000000000 : ℝ)^3119 := by
    have hnat : (267274939 : ℕ)^4143*25000000000000^3119 ≤ 10879876459261^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267274939 500000000 10879876459261 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258101971/10000000000 : ℝ)^4143 ≤ (3463465559189/25000000000000 : ℝ)^3119 := by
    have hnat : (2258101971 : ℕ)^4143*25000000000000^3119 ≤ 3463465559189^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258101971 10000000000 3463465559189 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631361423/5000000000 : ℝ)^4143 ≤ (42626631917791/100000000000000 : ℝ)^3119 := by
    have hnat : (2631361423 : ℕ)^4143*100000000000000^3119 ≤ 42626631917791^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631361423 5000000000 42626631917791 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267274939/500000000 : ℝ), (-2258101971/10000000000 : ℝ), (2631361423/5000000000 : ℝ)] ![(10879876459261/25000000000000 : ℝ), (3463465559189/25000000000000 : ℝ), (42626631917791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267274939/500000000 : ℝ)|^4143 ≤ (10879876459261/25000000000000 : ℝ)^3119
        have hw : |(267274939/500000000 : ℝ)|=(267274939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258101971/10000000000 : ℝ)|^4143 ≤ (3463465559189/25000000000000 : ℝ)^3119
        have hw : |(-2258101971/10000000000 : ℝ)|=(2258101971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631361423/5000000000 : ℝ)|^4143 ≤ (42626631917791/100000000000000 : ℝ)^3119
        have hw : |(2631361423/5000000000 : ℝ)|=(2631361423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345498357/10000000000 : ℝ)*x 0 + (2631362087/5000000000 : ℝ)*x 1 + (-1129050389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345498357/10000000000 : ℝ)^4143 ≤ (10879875315657/25000000000000 : ℝ)^3119 := by
    have hnat : (5345498357 : ℕ)^4143*25000000000000^3119 ≤ 10879875315657^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345498357 10000000000 10879875315657 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631362087/5000000000 : ℝ)^4143 ≤ (42626646205683/100000000000000 : ℝ)^3119 := by
    have hnat : (2631362087 : ℕ)^4143*100000000000000^3119 ≤ 42626646205683^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631362087 5000000000 42626646205683 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129050389/5000000000 : ℝ)^4143 ≤ (2770770502899/20000000000000 : ℝ)^3119 := by
    have hnat : (1129050389 : ℕ)^4143*20000000000000^3119 ≤ 2770770502899^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129050389 5000000000 2770770502899 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345498357/10000000000 : ℝ), (2631362087/5000000000 : ℝ), (-1129050389/5000000000 : ℝ)] ![(10879875315657/25000000000000 : ℝ), (42626646205683/100000000000000 : ℝ), (2770770502899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345498357/10000000000 : ℝ)|^4143 ≤ (10879875315657/25000000000000 : ℝ)^3119
        have hw : |(5345498357/10000000000 : ℝ)|=(5345498357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631362087/5000000000 : ℝ)|^4143 ≤ (42626646205683/100000000000000 : ℝ)^3119
        have hw : |(2631362087/5000000000 : ℝ)|=(2631362087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129050389/5000000000 : ℝ)|^4143 ≤ (2770770502899/20000000000000 : ℝ)^3119
        have hw : |(-1129050389/5000000000 : ℝ)|=(1129050389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371505143/10000000000 : ℝ)*x 0 + (4241966507/10000000000 : ℝ)*x 1 + (1126256829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371505143/10000000000 : ℝ)^4143 ≤ (33315507037837/100000000000000 : ℝ)^3119 := by
    have hnat : (4371505143 : ℕ)^4143*100000000000000^3119 ≤ 33315507037837^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371505143 10000000000 33315507037837 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241966507/10000000000 : ℝ)^4143 ≤ (6402118335021/20000000000000 : ℝ)^3119 := by
    have hnat : (4241966507 : ℕ)^4143*20000000000000^3119 ≤ 6402118335021^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241966507 10000000000 6402118335021 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126256829/2500000000 : ℝ)^4143 ≤ (34673901266237/100000000000000 : ℝ)^3119 := by
    have hnat : (1126256829 : ℕ)^4143*100000000000000^3119 ≤ 34673901266237^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126256829 2500000000 34673901266237 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371505143/10000000000 : ℝ), (4241966507/10000000000 : ℝ), (1126256829/2500000000 : ℝ)] ![(33315507037837/100000000000000 : ℝ), (6402118335021/20000000000000 : ℝ), (34673901266237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371505143/10000000000 : ℝ)|^4143 ≤ (33315507037837/100000000000000 : ℝ)^3119
        have hw : |(4371505143/10000000000 : ℝ)|=(4371505143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241966507/10000000000 : ℝ)|^4143 ≤ (6402118335021/20000000000000 : ℝ)^3119
        have hw : |(4241966507/10000000000 : ℝ)|=(4241966507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126256829/2500000000 : ℝ)|^4143 ≤ (34673901266237/100000000000000 : ℝ)^3119
        have hw : |(1126256829/2500000000 : ℝ)|=(1126256829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095170823/5000000000 : ℝ)*x 0 + (5263070591/10000000000 : ℝ)*x 1 + (5395884853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095170823/5000000000 : ℝ)^4143 ≤ (6652196651487/50000000000000 : ℝ)^3119 := by
    have hnat : (1095170823 : ℕ)^4143*50000000000000^3119 ≤ 6652196651487^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095170823 5000000000 6652196651487 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263070591/10000000000 : ℝ)^4143 ≤ (42630373331069/100000000000000 : ℝ)^3119 := by
    have hnat : (5263070591 : ℕ)^4143*100000000000000^3119 ≤ 42630373331069^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263070591 10000000000 42630373331069 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395884853/10000000000 : ℝ)^4143 ≤ (11016308337167/25000000000000 : ℝ)^3119 := by
    have hnat : (5395884853 : ℕ)^4143*25000000000000^3119 ≤ 11016308337167^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395884853 10000000000 11016308337167 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095170823/5000000000 : ℝ), (5263070591/10000000000 : ℝ), (5395884853/10000000000 : ℝ)] ![(6652196651487/50000000000000 : ℝ), (42630373331069/100000000000000 : ℝ), (11016308337167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095170823/5000000000 : ℝ)|^4143 ≤ (6652196651487/50000000000000 : ℝ)^3119
        have hw : |(-1095170823/5000000000 : ℝ)|=(1095170823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263070591/10000000000 : ℝ)|^4143 ≤ (42630373331069/100000000000000 : ℝ)^3119
        have hw : |(5263070591/10000000000 : ℝ)|=(5263070591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395884853/10000000000 : ℝ)|^4143 ≤ (11016308337167/25000000000000 : ℝ)^3119
        have hw : |(5395884853/10000000000 : ℝ)|=(5395884853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327949759/2500000000 : ℝ)*x 0 + (-42498809/200000000 : ℝ)*x 1 + (168621401/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327949759/2500000000 : ℝ)^4143 ≤ (43155447009869/100000000000000 : ℝ)^3119 := by
    have hnat : (1327949759 : ℕ)^4143*100000000000000^3119 ≤ 43155447009869^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327949759 2500000000 43155447009869 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42498809/200000000 : ℝ)^4143 ≤ (6389659928877/50000000000000 : ℝ)^3119 := by
    have hnat : (42498809 : ℕ)^4143*50000000000000^3119 ≤ 6389659928877^3119*200000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42498809 200000000 6389659928877 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168621401/312500000 : ℝ)^4143 ≤ (44065233120869/100000000000000 : ℝ)^3119 := by
    have hnat : (168621401 : ℕ)^4143*100000000000000^3119 ≤ 44065233120869^3119*312500000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168621401 312500000 44065233120869 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327949759/2500000000 : ℝ), (-42498809/200000000 : ℝ), (168621401/312500000 : ℝ)] ![(43155447009869/100000000000000 : ℝ), (6389659928877/50000000000000 : ℝ), (44065233120869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327949759/2500000000 : ℝ)|^4143 ≤ (43155447009869/100000000000000 : ℝ)^3119
        have hw : |(1327949759/2500000000 : ℝ)|=(1327949759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42498809/200000000 : ℝ)|^4143 ≤ (6389659928877/50000000000000 : ℝ)^3119
        have hw : |(-42498809/200000000 : ℝ)|=(42498809/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168621401/312500000 : ℝ)|^4143 ≤ (44065233120869/100000000000000 : ℝ)^3119
        have hw : |(168621401/312500000 : ℝ)|=(168621401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311799019/10000000000 : ℝ)*x 0 + (1348971211/2500000000 : ℝ)*x 1 + (-265617557/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311799019/10000000000 : ℝ)^4143 ≤ (43155446826409/100000000000000 : ℝ)^3119 := by
    have hnat : (5311799019 : ℕ)^4143*100000000000000^3119 ≤ 43155446826409^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311799019 10000000000 43155446826409 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348971211/2500000000 : ℝ)^4143 ≤ (275407707819/625000000000 : ℝ)^3119 := by
    have hnat : (1348971211 : ℕ)^4143*625000000000^3119 ≤ 275407707819^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348971211 2500000000 275407707819 625000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265617557/1250000000 : ℝ)^4143 ≤ (3194829976421/25000000000000 : ℝ)^3119 := by
    have hnat : (265617557 : ℕ)^4143*25000000000000^3119 ≤ 3194829976421^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265617557 1250000000 3194829976421 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311799019/10000000000 : ℝ), (1348971211/2500000000 : ℝ), (-265617557/1250000000 : ℝ)] ![(43155446826409/100000000000000 : ℝ), (275407707819/625000000000 : ℝ), (3194829976421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311799019/10000000000 : ℝ)|^4143 ≤ (43155446826409/100000000000000 : ℝ)^3119
        have hw : |(5311799019/10000000000 : ℝ)|=(5311799019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348971211/2500000000 : ℝ)|^4143 ≤ (275407707819/625000000000 : ℝ)^3119
        have hw : |(1348971211/2500000000 : ℝ)|=(1348971211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265617557/1250000000 : ℝ)|^4143 ≤ (3194829976421/25000000000000 : ℝ)^3119
        have hw : |(-265617557/1250000000 : ℝ)|=(265617557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s5_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371516047/10000000000 : ℝ)*x 0 + (4504344913/10000000000 : ℝ)*x 1 + (4242651477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371516047/10000000000 : ℝ)^4143 ≤ (33315617420537/100000000000000 : ℝ)^3119 := by
    have hnat : (4371516047 : ℕ)^4143*100000000000000^3119 ≤ 33315617420537^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371516047 10000000000 33315617420537 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504344913/10000000000 : ℝ)^4143 ≤ (1386676992341/4000000000000 : ℝ)^3119 := by
    have hnat : (4504344913 : ℕ)^4143*4000000000000^3119 ≤ 1386676992341^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504344913 10000000000 1386676992341 4000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242651477/10000000000 : ℝ)^4143 ≤ (16008728879353/50000000000000 : ℝ)^3119 := by
    have hnat : (4242651477 : ℕ)^4143*50000000000000^3119 ≤ 16008728879353^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242651477 10000000000 16008728879353 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371516047/10000000000 : ℝ), (4504344913/10000000000 : ℝ), (4242651477/10000000000 : ℝ)] ![(33315617420537/100000000000000 : ℝ), (1386676992341/4000000000000 : ℝ), (16008728879353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371516047/10000000000 : ℝ)|^4143 ≤ (33315617420537/100000000000000 : ℝ)^3119
        have hw : |(4371516047/10000000000 : ℝ)|=(4371516047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504344913/10000000000 : ℝ)|^4143 ≤ (1386676992341/4000000000000 : ℝ)^3119
        have hw : |(4504344913/10000000000 : ℝ)|=(4504344913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242651477/10000000000 : ℝ)|^4143 ≤ (16008728879353/50000000000000 : ℝ)^3119
        have hw : |(4242651477/10000000000 : ℝ)|=(4242651477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11241/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11079/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (13633672917520511/100000000000000000000 : ℝ) := by
    have hpowers : (11079/100000 : ℝ)^8285 ≤ (13633672917520511/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11079 : ℕ)^8285*100000000000000000000^2048 ≤ 13633672917520511^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11079 100000 13633672917520511 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11079/100000 : ℝ)) (X := (13633672917520511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (18812535644125579/50000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8285 ≤ (18812535644125579/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8285*50000000000000000000^2048 ≤ 18812535644125579^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 18812535644125579 50000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (18812535644125579/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013633672917520511/50000000000000000000 : ℝ) ≤ (10000673962506637/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50013633672917520511/50000000000000000000 : ℝ)^2048 ≤ (10000673962506637/10000000000000000 : ℝ)^8285 := by
      have hnat : (50013633672917520511 : ℕ)^2048*10000000000000000^8285 ≤ 10000673962506637^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013633672917520511 50000000000000000000 10000673962506637 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000673962506637/10000000000000000 : ℝ)) (X := (50013633672917520511/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051258744205771669/100000000000000000000 : ℝ) ≤ (400050673583493/400000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (100051258744205771669/100000000000000000000 : ℝ)^2048 ≤ (400050673583493/400000000000000 : ℝ)^8285 := by
      have hnat : (100051258744205771669 : ℕ)^2048*400000000000000^8285 ≤ 400050673583493^8285*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051258744205771669 100000000000000000000 400050673583493 400000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400050673583493/400000000000000 : ℝ)) (X := (100051258744205771669/100000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018812535644125579/25000000000000000000 : ℝ) ≤ (10001859716668013/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (25018812535644125579/25000000000000000000 : ℝ)^2048 ≤ (10001859716668013/10000000000000000 : ℝ)^8285 := by
      have hnat : (25018812535644125579 : ℕ)^2048*10000000000000000^8285 ≤ 10001859716668013^8285*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018812535644125579 25000000000000000000 10001859716668013 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001859716668013/10000000000000000 : ℝ)) (X := (25018812535644125579/25000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13633672917520511/100000000000000000000 : ℝ) ≤ ((3948624093895886027/3950000000000000000 : ℝ)+2*(37054817543/19750000000000 : ℝ)*(11079/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (3948624093895886027/3950000000000000000 : ℝ)+2*(37054817543/19750000000000 : ℝ)*(11079/100000 : ℝ)=(10000673962506637/10000000000000000 : ℝ) by norm_num, show 1+2*(13633672917520511/100000000000000000000 : ℝ)=(50013633672917520511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18812535644125579/50000000000000000000 : ℝ)+(13633672917520511/100000000000000000000 : ℝ) ≤ ((3948624093895886027/3950000000000000000 : ℝ)+(37054817543/19750000000000 : ℝ)*((14239/100000 : ℝ)+(11079/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (3948624093895886027/3950000000000000000 : ℝ)+(37054817543/19750000000000 : ℝ)*((14239/100000 : ℝ)+(11079/100000 : ℝ))=(400050673583493/400000000000000 : ℝ) by norm_num, show 1+(18812535644125579/50000000000000000000 : ℝ)+(13633672917520511/100000000000000000000 : ℝ)=(100051258744205771669/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18812535644125579/50000000000000000000 : ℝ) ≤ ((3948624093895886027/3950000000000000000 : ℝ)+2*(37054817543/19750000000000 : ℝ)*(14239/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (3948624093895886027/3950000000000000000 : ℝ)+2*(37054817543/19750000000000 : ℝ)*(14239/100000 : ℝ)=(10001859716668013/10000000000000000 : ℝ) by norm_num, show 1+2*(18812535644125579/50000000000000000000 : ℝ)=(25018812535644125579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3948624093895886027/3950000000000000000 : ℝ)*(X 1 0+X 2 0)+(37054817543/19750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (3948624093895886027/3950000000000000000 : ℝ)) (alpha := (37054817543/19750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3948624093895886027/3950000000000000000 : ℝ)*(X 0 1+X 2 1)+(37054817543/19750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (3948624093895886027/3950000000000000000 : ℝ)) (alpha := (37054817543/19750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3948624093895886027/3950000000000000000 : ℝ)*(X 0 2+X 1 2)+(37054817543/19750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (3948624093895886027/3950000000000000000 : ℝ)) (alpha := (37054817543/19750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190336059/10000000000 : ℝ)*X 0 0+(1079246427/2000000000 : ℝ)*X 0 1+(2631362319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267274939/500000000 : ℝ)*X 1 0+(-2258101971/10000000000 : ℝ)*X 1 1+(2631361423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345498357/10000000000 : ℝ)*X 2 0+(2631362087/5000000000 : ℝ)*X 2 1+(-1129050389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371505143/10000000000 : ℝ)*X 0 0+(4241966507/10000000000 : ℝ)*X 0 1+(1126256829/2500000000 : ℝ)*X 0 2+(4371505143/10000000000 : ℝ)*X 1 0+(4241966507/10000000000 : ℝ)*X 1 1+(1126256829/2500000000 : ℝ)*X 1 2+(4371505143/10000000000 : ℝ)*X 2 0+(4241966507/10000000000 : ℝ)*X 2 1+(1126256829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1095170823/5000000000 : ℝ)*X 0 0+(5263070591/10000000000 : ℝ)*X 0 1+(5395884853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327949759/2500000000 : ℝ)*X 1 0+(-42498809/200000000 : ℝ)*X 1 1+(168621401/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311799019/10000000000 : ℝ)*X 2 0+(1348971211/2500000000 : ℝ)*X 2 1+(-265617557/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371516047/10000000000 : ℝ)*X 0 0+(4504344913/10000000000 : ℝ)*X 0 1+(4242651477/10000000000 : ℝ)*X 0 2+(4371516047/10000000000 : ℝ)*X 1 0+(4504344913/10000000000 : ℝ)*X 1 1+(4242651477/10000000000 : ℝ)*X 1 2+(4371516047/10000000000 : ℝ)*X 2 0+(4504344913/10000000000 : ℝ)*X 2 1+(4242651477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17698175186037537161724291/3085937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2450797471/100000000000000 : ℝ)*(base19) + (417662939/20000000000000 : ℝ)*(base23) + (103757/160000000000 : ℝ)*(lower2) + (91415407/50000000000000 : ℝ)*(upper5) + (176433677120399/3125000000000 : ℝ)*(major0) + (176433677120399/3125000000000 : ℝ)*(major1) + (176433677120399/3125000000000 : ℝ)*(major2) + (234070323063927/3125000000000 : ℝ)*(sp0) + (936279284573423/12500000000000 : ℝ)*(sp1) + (1872572600695733/25000000000000 : ℝ)*(sp2) + (3801434631747229/100000000000000 : ℝ)*(sp3) + (42153051963/100000000000000 : ℝ)*(sp4) + (55763712771/100000000000000 : ℝ)*(sp5) + (28021690507/100000000000000 : ℝ)*(sp7) + (475182831679717/12500000000000 : ℝ)*(f.failure) + (7490292491097627/100000000000000 : ℝ)*(f.sum) + (241747398299/987500000000000000000000000 : ℝ)*base65 + (140375902350491477/12343750000000000000000000000000 : ℝ)*base68 + (203796725952522727/12343750000000000000000000000000 : ℝ)*base70 + (130327004649710227/12343750000000000000000000000000 : ℝ)*base72 + (1296911590613/493750000000000000000000000 : ℝ)*base74 + (156400160786116477/12343750000000000000000000000000 : ℝ)*base76 + (89834103617210227/12343750000000000000000000000000 : ℝ)*base78 + (270931615820022727/12343750000000000000000000000000 : ℝ)*base80 + (5124714818277/1975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6703477/625000000000000000000 : ℝ)*base89 + (6703477/625000000000000000000 : ℝ)*base91 + (6703477/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1378157614145837653331953293/197500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1329170357/100000000000000 : ℝ)*(base19) + (137978311/10000000000000 : ℝ)*(base23) + (16986749/12500000000000 : ℝ)*(upper3) + (8529253/25000000000000 : ℝ)*(lower4) + (7822577/6250000000000 : ℝ)*(upper5) + (5675287725958351/100000000000000 : ℝ)*(major0) + (5675287725958351/100000000000000 : ℝ)*(major1) + (5675287725958351/100000000000000 : ℝ)*(major2) + (4320487861/12500000000000 : ℝ)*(sp1) + (36216366739/100000000000000 : ℝ)*(sp2) + (3764655144081751/50000000000000 : ℝ)*(sp4) + (3764637197545129/50000000000000 : ℝ)*(sp5) + (7529272692013653/100000000000000 : ℝ)*(sp6) + (955316232788187/25000000000000 : ℝ)*(sp7) + (955316232788187/25000000000000 : ℝ)*(f.failure) + (3764655144081751/50000000000000 : ℝ)*(f.sum) + (3611191426607/987500000000000000000000000 : ℝ)*base66 + (5720196774206538523/395000000000000000000000000000000 : ℝ)*base68 + (2302381615626538523/395000000000000000000000000000000 : ℝ)*base70 + (5824190193016538523/395000000000000000000000000000000 : ℝ)*base72 + (3025504892207/987500000000000000000000000 : ℝ)*base74 + (9565211341336538523/395000000000000000000000000000000 : ℝ)*base76 + (4068054282306538523/395000000000000000000000000000000 : ℝ)*base78 + (5353974118426538523/395000000000000000000000000000000 : ℝ)*base80 + (1126712829167/246875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4413547/1250000000000000000000 : ℝ)*base89 + (4413547/1250000000000000000000 : ℝ)*base91 + (4413547/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1093_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1093_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1093_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1093_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1093_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
