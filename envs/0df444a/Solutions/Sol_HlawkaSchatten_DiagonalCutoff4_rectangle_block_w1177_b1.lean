-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:20.664754+00:00
-- url     : https://prove2.me/submissions/9228c47c-67cc-4c4d-858e-c65ab2940fd6

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
theorem support_rectangle_w1177_s3_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-536706401/2500000000 : ℝ)*x 0 + (1085132293/2000000000 : ℝ)*x 1 + (523527359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536706401/2500000000 : ℝ)^4185 ≤ (652084069947/5000000000000 : ℝ)^3161 := by
    have hnat : (536706401 : ℕ)^4185*5000000000000^3161 ≤ 652084069947^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536706401 2500000000 652084069947 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085132293/2000000000 : ℝ)^4185 ≤ (22253542035277/50000000000000 : ℝ)^3161 := by
    have hnat : (1085132293 : ℕ)^4185*50000000000000^3161 ≤ 22253542035277^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085132293 2000000000 22253542035277 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523527359/1000000000 : ℝ)^4185 ≤ (8490246902491/20000000000000 : ℝ)^3161 := by
    have hnat : (523527359 : ℕ)^4185*20000000000000^3161 ≤ 8490246902491^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523527359 1000000000 8490246902491 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536706401/2500000000 : ℝ), (1085132293/2000000000 : ℝ), (523527359/1000000000 : ℝ)] ![(652084069947/5000000000000 : ℝ), (22253542035277/50000000000000 : ℝ), (8490246902491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536706401/2500000000 : ℝ)|^4185 ≤ (652084069947/5000000000000 : ℝ)^3161
        have hw : |(-536706401/2500000000 : ℝ)|=(536706401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085132293/2000000000 : ℝ)|^4185 ≤ (22253542035277/50000000000000 : ℝ)^3161
        have hw : |(1085132293/2000000000 : ℝ)|=(1085132293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523527359/1000000000 : ℝ)|^4185 ≤ (8490246902491/20000000000000 : ℝ)^3161
        have hw : |(523527359/1000000000 : ℝ)|=(523527359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535296289/1000000000 : ℝ)*x 0 + (-561018201/2500000000 : ℝ)*x 1 + (5235273393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535296289/1000000000 : ℝ)^4185 ≤ (21859632150661/50000000000000 : ℝ)^3161 := by
    have hnat : (535296289 : ℕ)^4185*50000000000000^3161 ≤ 21859632150661^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535296289 1000000000 21859632150661 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561018201/2500000000 : ℝ)^4185 ≤ (6914751639611/50000000000000 : ℝ)^3161 := by
    have hnat : (561018201 : ℕ)^4185*50000000000000^3161 ≤ 6914751639611^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561018201 2500000000 6914751639611 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235273393/10000000000 : ℝ)^4185 ≤ (42451232397563/100000000000000 : ℝ)^3161 := by
    have hnat : (5235273393 : ℕ)^4185*100000000000000^3161 ≤ 42451232397563^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235273393 10000000000 42451232397563 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535296289/1000000000 : ℝ), (-561018201/2500000000 : ℝ), (5235273393/10000000000 : ℝ)] ![(21859632150661/50000000000000 : ℝ), (6914751639611/50000000000000 : ℝ), (42451232397563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535296289/1000000000 : ℝ)|^4185 ≤ (21859632150661/50000000000000 : ℝ)^3161
        have hw : |(535296289/1000000000 : ℝ)|=(535296289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561018201/2500000000 : ℝ)|^4185 ≤ (6914751639611/50000000000000 : ℝ)^3161
        have hw : |(-561018201/2500000000 : ℝ)|=(561018201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235273393/10000000000 : ℝ)|^4185 ≤ (42451232397563/100000000000000 : ℝ)^3161
        have hw : |(5235273393/10000000000 : ℝ)|=(5235273393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352962977/10000000000 : ℝ)*x 0 + (5235273371/10000000000 : ℝ)*x 1 + (-2244072719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352962977/10000000000 : ℝ)^4185 ≤ (2185963262103/5000000000000 : ℝ)^3161 := by
    have hnat : (5352962977 : ℕ)^4185*5000000000000^3161 ≤ 2185963262103^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352962977 10000000000 2185963262103 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235273371/10000000000 : ℝ)^4185 ≤ (42451232161383/100000000000000 : ℝ)^3161 := by
    have hnat : (5235273371 : ℕ)^4185*100000000000000^3161 ≤ 42451232161383^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235273371 10000000000 42451232161383 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244072719/10000000000 : ℝ)^4185 ≤ (13829502585701/100000000000000 : ℝ)^3161 := by
    have hnat : (2244072719 : ℕ)^4185*100000000000000^3161 ≤ 13829502585701^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244072719 10000000000 13829502585701 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352962977/10000000000 : ℝ), (5235273371/10000000000 : ℝ), (-2244072719/10000000000 : ℝ)] ![(2185963262103/5000000000000 : ℝ), (42451232161383/100000000000000 : ℝ), (13829502585701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352962977/10000000000 : ℝ)|^4185 ≤ (2185963262103/5000000000000 : ℝ)^3161
        have hw : |(5352962977/10000000000 : ℝ)|=(5352962977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235273371/10000000000 : ℝ)|^4185 ≤ (42451232161383/100000000000000 : ℝ)^3161
        have hw : |(5235273371/10000000000 : ℝ)|=(5235273371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244072719/10000000000 : ℝ)|^4185 ≤ (13829502585701/100000000000000 : ℝ)^3161
        have hw : |(-2244072719/10000000000 : ℝ)|=(2244072719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871544467/2000000000 : ℝ)*x 0 + (4171147967/10000000000 : ℝ)*x 1 + (2276260919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871544467/2000000000 : ℝ)^4185 ≤ (416206040699/1250000000000 : ℝ)^3161 := by
    have hnat : (871544467 : ℕ)^4185*1250000000000^3161 ≤ 416206040699^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871544467 2000000000 416206040699 1250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171147967/10000000000 : ℝ)^4185 ≤ (31422310186043/100000000000000 : ℝ)^3161 := by
    have hnat : (4171147967 : ℕ)^4185*100000000000000^3161 ≤ 31422310186043^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171147967 10000000000 31422310186043 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276260919/5000000000 : ℝ)^4185 ≤ (35281206540763/100000000000000 : ℝ)^3161 := by
    have hnat : (2276260919 : ℕ)^4185*100000000000000^3161 ≤ 35281206540763^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276260919 5000000000 35281206540763 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871544467/2000000000 : ℝ), (4171147967/10000000000 : ℝ), (2276260919/5000000000 : ℝ)] ![(416206040699/1250000000000 : ℝ), (31422310186043/100000000000000 : ℝ), (35281206540763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871544467/2000000000 : ℝ)|^4185 ≤ (416206040699/1250000000000 : ℝ)^3161
        have hw : |(871544467/2000000000 : ℝ)|=(871544467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171147967/10000000000 : ℝ)|^4185 ≤ (31422310186043/100000000000000 : ℝ)^3161
        have hw : |(4171147967/10000000000 : ℝ)|=(4171147967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2276260919/5000000000 : ℝ)|^4185 ≤ (35281206540763/100000000000000 : ℝ)^3161
        have hw : |(2276260919/5000000000 : ℝ)|=(2276260919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146841991/10000000000 : ℝ)*x 0 + (261799733/500000000 : ℝ)*x 1 + (1356234131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146841991/10000000000 : ℝ)^4185 ≤ (815113324789/6250000000000 : ℝ)^3161 := by
    have hnat : (2146841991 : ℕ)^4185*6250000000000^3161 ≤ 815113324789^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146841991 10000000000 815113324789 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261799733/500000000 : ℝ)^4185 ≤ (1698359029023/4000000000000 : ℝ)^3161 := by
    have hnat : (261799733 : ℕ)^4185*4000000000000^3161 ≤ 1698359029023^3161*500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261799733 500000000 1698359029023 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356234131/2500000000 : ℝ)^4185 ≤ (44499211062799/100000000000000 : ℝ)^3161 := by
    have hnat : (1356234131 : ℕ)^4185*100000000000000^3161 ≤ 44499211062799^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356234131 2500000000 44499211062799 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146841991/10000000000 : ℝ), (261799733/500000000 : ℝ), (1356234131/2500000000 : ℝ)] ![(815113324789/6250000000000 : ℝ), (1698359029023/4000000000000 : ℝ), (44499211062799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146841991/10000000000 : ℝ)|^4185 ≤ (815113324789/6250000000000 : ℝ)^3161
        have hw : |(-2146841991/10000000000 : ℝ)|=(2146841991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261799733/500000000 : ℝ)|^4185 ≤ (1698359029023/4000000000000 : ℝ)^3161
        have hw : |(261799733/500000000 : ℝ)|=(261799733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356234131/2500000000 : ℝ)|^4185 ≤ (44499211062799/100000000000000 : ℝ)^3161
        have hw : |(1356234131/2500000000 : ℝ)|=(1356234131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304606933/10000000000 : ℝ)*x 0 + (-128400643/625000000 : ℝ)*x 1 + (5424936399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304606933/10000000000 : ℝ)^4185 ≤ (43197153906353/100000000000000 : ℝ)^3161 := by
    have hnat : (5304606933 : ℕ)^4185*100000000000000^3161 ≤ 43197153906353^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304606933 10000000000 43197153906353 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128400643/625000000 : ℝ)^4185 ≤ (12303636373571/100000000000000 : ℝ)^3161 := by
    have hnat : (128400643 : ℕ)^4185*100000000000000^3161 ≤ 12303636373571^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128400643 625000000 12303636373571 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424936399/10000000000 : ℝ)^4185 ≤ (22249604852651/50000000000000 : ℝ)^3161 := by
    have hnat : (5424936399 : ℕ)^4185*50000000000000^3161 ≤ 22249604852651^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424936399 10000000000 22249604852651 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304606933/10000000000 : ℝ), (-128400643/625000000 : ℝ), (5424936399/10000000000 : ℝ)] ![(43197153906353/100000000000000 : ℝ), (12303636373571/100000000000000 : ℝ), (22249604852651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304606933/10000000000 : ℝ)|^4185 ≤ (43197153906353/100000000000000 : ℝ)^3161
        have hw : |(5304606933/10000000000 : ℝ)|=(5304606933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128400643/625000000 : ℝ)|^4185 ≤ (12303636373571/100000000000000 : ℝ)^3161
        have hw : |(-128400643/625000000 : ℝ)|=(128400643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424936399/10000000000 : ℝ)|^4185 ≤ (22249604852651/50000000000000 : ℝ)^3161
        have hw : |(5424936399/10000000000 : ℝ)|=(5424936399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304608073/10000000000 : ℝ)*x 0 + (271246767/500000000 : ℝ)*x 1 + (-513602547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304608073/10000000000 : ℝ)^4185 ≤ (8639433239417/20000000000000 : ℝ)^3161 := by
    have hnat : (5304608073 : ℕ)^4185*20000000000000^3161 ≤ 8639433239417^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304608073 10000000000 8639433239417 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271246767/500000000 : ℝ)^4185 ≤ (8899839640919/20000000000000 : ℝ)^3161 := by
    have hnat : (271246767 : ℕ)^4185*20000000000000^3161 ≤ 8899839640919^3161*500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271246767 500000000 8899839640919 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513602547/2500000000 : ℝ)^4185 ≤ (12303635580673/100000000000000 : ℝ)^3161 := by
    have hnat : (513602547 : ℕ)^4185*100000000000000^3161 ≤ 12303635580673^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513602547 2500000000 12303635580673 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304608073/10000000000 : ℝ), (271246767/500000000 : ℝ), (-513602547/2500000000 : ℝ)] ![(8639433239417/20000000000000 : ℝ), (8899839640919/20000000000000 : ℝ), (12303635580673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304608073/10000000000 : ℝ)|^4185 ≤ (8639433239417/20000000000000 : ℝ)^3161
        have hw : |(5304608073/10000000000 : ℝ)|=(5304608073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271246767/500000000 : ℝ)|^4185 ≤ (8899839640919/20000000000000 : ℝ)^3161
        have hw : |(271246767/500000000 : ℝ)|=(271246767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513602547/2500000000 : ℝ)|^4185 ≤ (12303635580673/100000000000000 : ℝ)^3161
        have hw : |(-513602547/2500000000 : ℝ)|=(513602547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s3_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178877443/5000000000 : ℝ)*x 0 + (4551077777/10000000000 : ℝ)*x 1 + (260787523/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178877443/5000000000 : ℝ)^4185 ≤ (416210156787/1250000000000 : ℝ)^3161 := by
    have hnat : (2178877443 : ℕ)^4185*1250000000000^3161 ≤ 416210156787^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178877443 5000000000 416210156787 1250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551077777/10000000000 : ℝ)^4185 ≤ (4408298840573/12500000000000 : ℝ)^3161 := by
    have hnat : (4551077777 : ℕ)^4185*12500000000000^3161 ≤ 4408298840573^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551077777 10000000000 4408298840573 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260787523/625000000 : ℝ)^4185 ≤ (31436796720789/100000000000000 : ℝ)^3161 := by
    have hnat : (260787523 : ℕ)^4185*100000000000000^3161 ≤ 31436796720789^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260787523 625000000 31436796720789 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178877443/5000000000 : ℝ), (4551077777/10000000000 : ℝ), (260787523/625000000 : ℝ)] ![(416210156787/1250000000000 : ℝ), (4408298840573/12500000000000 : ℝ), (31436796720789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178877443/5000000000 : ℝ)|^4185 ≤ (416210156787/1250000000000 : ℝ)^3161
        have hw : |(2178877443/5000000000 : ℝ)|=(2178877443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551077777/10000000000 : ℝ)|^4185 ≤ (4408298840573/12500000000000 : ℝ)^3161
        have hw : |(4551077777/10000000000 : ℝ)|=(4551077777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260787523/625000000 : ℝ)|^4185 ≤ (31436796720789/100000000000000 : ℝ)^3161
        have hw : |(260787523/625000000 : ℝ)|=(260787523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (671/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (41/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (41/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (41/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (41/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (41/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (41/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4613/50000 : ℝ) ^ (8369/2048 : ℝ) ≤ (2948317731078837/50000000000000000000 : ℝ) := by
    have hpowers : (4613/50000 : ℝ)^8369 ≤ (2948317731078837/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4613 : ℕ)^8369*50000000000000000000^2048 ≤ 2948317731078837^2048*50000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4613 50000 2948317731078837 50000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4613/50000 : ℝ)) (X := (2948317731078837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (41/250 : ℝ) ^ (8369/2048 : ℝ) ≤ (15468837136876337/25000000000000000000 : ℝ) := by
    have hpowers : (41/250 : ℝ)^8369 ≤ (15468837136876337/25000000000000000000 : ℝ)^2048 := by
      have hnat : (41 : ℕ)^8369*25000000000000000000^2048 ≤ 15468837136876337^2048*250^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41 250 15468837136876337 25000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41/250 : ℝ)) (X := (15468837136876337/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002948317731078837/25000000000000000000 : ℝ) ≤ (5000144291691081/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25002948317731078837/25000000000000000000 : ℝ)^2048 ≤ (5000144291691081/5000000000000000 : ℝ)^8369 := by
      have hnat : (25002948317731078837 : ℕ)^2048*5000000000000000^8369 ≤ 5000144291691081^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002948317731078837 25000000000000000000 5000144291691081 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000144291691081/5000000000000000 : ℝ)) (X := (25002948317731078837/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50033885992004831511/50000000000000000000 : ℝ) ≤ (2500414510437599/2500000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50033885992004831511/50000000000000000000 : ℝ)^2048 ≤ (2500414510437599/2500000000000000 : ℝ)^8369 := by
      have hnat : (50033885992004831511 : ℕ)^2048*2500000000000000^8369 ≤ 2500414510437599^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033885992004831511 50000000000000000000 2500414510437599 2500000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500414510437599/2500000000000000 : ℝ)) (X := (50033885992004831511/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515468837136876337/12500000000000000000 : ℝ) ≤ (1000302750011863/1000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (12515468837136876337/12500000000000000000 : ℝ)^2048 ≤ (1000302750011863/1000000000000000 : ℝ)^8369 := by
      have hnat : (12515468837136876337 : ℕ)^2048*1000000000000000^8369 ≤ 1000302750011863^8369*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515468837136876337 12500000000000000000 1000302750011863 1000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000302750011863/1000000000000000 : ℝ)) (X := (12515468837136876337/12500000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2948317731078837/50000000000000000000 : ℝ) ≤ ((210931767798155813/211000000000000000 : ℝ)+2*(40278187301/21100000000000 : ℝ)*(4613/50000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (210931767798155813/211000000000000000 : ℝ)+2*(40278187301/21100000000000 : ℝ)*(4613/50000 : ℝ)=(5000144291691081/5000000000000000 : ℝ) by norm_num, show 1+2*(2948317731078837/50000000000000000000 : ℝ)=(25002948317731078837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15468837136876337/25000000000000000000 : ℝ)+(2948317731078837/50000000000000000000 : ℝ) ≤ ((210931767798155813/211000000000000000 : ℝ)+(40278187301/21100000000000 : ℝ)*((41/250 : ℝ)+(4613/50000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (210931767798155813/211000000000000000 : ℝ)+(40278187301/21100000000000 : ℝ)*((41/250 : ℝ)+(4613/50000 : ℝ))=(2500414510437599/2500000000000000 : ℝ) by norm_num, show 1+(15468837136876337/25000000000000000000 : ℝ)+(2948317731078837/50000000000000000000 : ℝ)=(50033885992004831511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15468837136876337/25000000000000000000 : ℝ) ≤ ((210931767798155813/211000000000000000 : ℝ)+2*(40278187301/21100000000000 : ℝ)*(41/250 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (210931767798155813/211000000000000000 : ℝ)+2*(40278187301/21100000000000 : ℝ)*(41/250 : ℝ)=(1000302750011863/1000000000000000 : ℝ) by norm_num, show 1+2*(15468837136876337/25000000000000000000 : ℝ)=(12515468837136876337/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (210931767798155813/211000000000000000 : ℝ)*(X 1 0+X 2 0)+(40278187301/21100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (4613/50000 : ℝ)) (hi := (41/250 : ℝ)) (c := (210931767798155813/211000000000000000 : ℝ)) (alpha := (40278187301/21100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (210931767798155813/211000000000000000 : ℝ)*(X 0 1+X 2 1)+(40278187301/21100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (4613/50000 : ℝ)) (hi := (41/250 : ℝ)) (c := (210931767798155813/211000000000000000 : ℝ)) (alpha := (40278187301/21100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (210931767798155813/211000000000000000 : ℝ)*(X 0 2+X 1 2)+(40278187301/21100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (4613/50000 : ℝ)) (hi := (41/250 : ℝ)) (c := (210931767798155813/211000000000000000 : ℝ)) (alpha := (40278187301/21100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-536706401/2500000000 : ℝ)*X 0 0+(1085132293/2000000000 : ℝ)*X 0 1+(523527359/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535296289/1000000000 : ℝ)*X 1 0+(-561018201/2500000000 : ℝ)*X 1 1+(5235273393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352962977/10000000000 : ℝ)*X 2 0+(5235273371/10000000000 : ℝ)*X 2 1+(-2244072719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871544467/2000000000 : ℝ)*X 0 0+(4171147967/10000000000 : ℝ)*X 0 1+(2276260919/5000000000 : ℝ)*X 0 2+(871544467/2000000000 : ℝ)*X 1 0+(4171147967/10000000000 : ℝ)*X 1 1+(2276260919/5000000000 : ℝ)*X 1 2+(871544467/2000000000 : ℝ)*X 2 0+(4171147967/10000000000 : ℝ)*X 2 1+(2276260919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2146841991/10000000000 : ℝ)*X 0 0+(261799733/500000000 : ℝ)*X 0 1+(1356234131/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304606933/10000000000 : ℝ)*X 1 0+(-128400643/625000000 : ℝ)*X 1 1+(5424936399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304608073/10000000000 : ℝ)*X 2 0+(271246767/500000000 : ℝ)*X 2 1+(-513602547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178877443/5000000000 : ℝ)*X 0 0+(4551077777/10000000000 : ℝ)*X 0 1+(260787523/625000000 : ℝ)*X 0 2+(2178877443/5000000000 : ℝ)*X 1 0+(4551077777/10000000000 : ℝ)*X 1 1+(260787523/625000000 : ℝ)*X 1 2+(2178877443/5000000000 : ℝ)*X 2 0+(4551077777/10000000000 : ℝ)*X 2 1+(260787523/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19981969323245681887230411/2110000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2158717039/100000000000000 : ℝ)*(base19) + (1039830481/50000000000000 : ℝ)*(base23) + (11001903/12500000000000 : ℝ)*(lower2) + (43825617/20000000000000 : ℝ)*(upper3) + (50536283/25000000000000 : ℝ)*(upper5) + (787464388860617/20000000000000 : ℝ)*(major0) + (787464388860617/20000000000000 : ℝ)*(major1) + (787464388860617/20000000000000 : ℝ)*(major2) + (1313117642635621/25000000000000 : ℝ)*(sp0) + (1313126408506313/25000000000000 : ℝ)*(sp1) + (5252505713081329/100000000000000 : ℝ)*(sp2) + (1311058341080047/50000000000000 : ℝ)*(sp3) + (37222199807/100000000000000 : ℝ)*(sp4) + (9549016429/50000000000000 : ℝ)*(sp7) + (2622135780192953/100000000000000 : ℝ)*(f.failure) + (5252507792742291/100000000000000 : ℝ)*(f.sum) + (102567570031/105500000000000000000000000 : ℝ)*base65 + (24860652422806621/4220000000000000000000000000000 : ℝ)*base67 + (31425125328806621/4220000000000000000000000000000 : ℝ)*base69 + (31534132089726621/4220000000000000000000000000000 : ℝ)*base71 + (431561065001/211000000000000000000000000 : ℝ)*base73 + (22109595143046621/4220000000000000000000000000000 : ℝ)*base75 + (16983326684066621/4220000000000000000000000000000 : ℝ)*base77 + (1305539223426621/4220000000000000000000000000000 : ℝ)*base79 + (23445380551/105500000000000000000000000 : ℝ)*base81 + (2593863/5000000000000000000000 : ℝ)*base90 + (2593863/5000000000000000000000 : ℝ)*base92 + (2593863/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58517035987147612040578197/5275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (295267643/20000000000000 : ℝ)*(base19) + (2755558231/100000000000000 : ℝ)*(base23) + (178865551/100000000000000 : ℝ)*(upper3) + (5452797/20000000000000 : ℝ)*(lower4) + (33293253/25000000000000 : ℝ)*(upper5) + (3967405047241077/100000000000000 : ℝ)*(major0) + (3967405047241077/100000000000000 : ℝ)*(major1) + (3967405047241077/100000000000000 : ℝ)*(major2) + (453868773/2000000000000 : ℝ)*(sp1) + (6522095651/20000000000000 : ℝ)*(sp2) + (165394984989561/3125000000000 : ℝ)*(sp4) + (5292615349889087/100000000000000 : ℝ)*(sp5) + (2646302076814733/50000000000000 : ℝ)*(sp6) + (330271275630037/12500000000000 : ℝ)*(sp7) + (330271275630037/12500000000000 : ℝ)*(f.failure) + (165394984989561/3125000000000 : ℝ)*(f.sum) + (2033675131143/1055000000000000000000000000 : ℝ)*base66 + (101898757468500601/21100000000000000000000000000000 : ℝ)*base67 + (28468467421899399/21100000000000000000000000000000 : ℝ)*base70 + (42546427892000601/21100000000000000000000000000000 : ℝ)*base71 + (3091932108697/1055000000000000000000000000 : ℝ)*base73 + (194812021331600601/21100000000000000000000000000000 : ℝ)*base75 + (100573422221800601/21100000000000000000000000000000 : ℝ)*base77 + (24061707271000601/21100000000000000000000000000000 : ℝ)*base79 + (203230076903/65937500000000000000000000 : ℝ)*base82 + (5074427/625000000000000000000 : ℝ)*base90 + (5074427/625000000000000000000 : ℝ)*base92 + (5074427/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_s4_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107477791/500000000 : ℝ)*x 0 + (1350067287/2500000000 : ℝ)*x 1 + (5258878887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107477791/500000000 : ℝ)^4185 ≤ (130636445283/1000000000000 : ℝ)^3161 := by
    have hnat : (107477791 : ℕ)^4185*1000000000000^3161 ≤ 130636445283^3161*500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107477791 500000000 130636445283 1000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350067287/2500000000 : ℝ)^4185 ≤ (4423152160657/10000000000000 : ℝ)^3161 := by
    have hnat : (1350067287 : ℕ)^4185*10000000000000^3161 ≤ 4423152160657^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350067287 2500000000 4423152160657 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258878887/10000000000 : ℝ)^4185 ≤ (42704833850729/100000000000000 : ℝ)^3161 := by
    have hnat : (5258878887 : ℕ)^4185*100000000000000^3161 ≤ 42704833850729^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258878887 10000000000 42704833850729 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107477791/500000000 : ℝ), (1350067287/2500000000 : ℝ), (5258878887/10000000000 : ℝ)] ![(130636445283/1000000000000 : ℝ), (4423152160657/10000000000000 : ℝ), (42704833850729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107477791/500000000 : ℝ)|^4185 ≤ (130636445283/1000000000000 : ℝ)^3161
        have hw : |(-107477791/500000000 : ℝ)|=(107477791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350067287/2500000000 : ℝ)|^4185 ≤ (4423152160657/10000000000000 : ℝ)^3161
        have hw : |(1350067287/2500000000 : ℝ)|=(1350067287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258878887/10000000000 : ℝ)|^4185 ≤ (42704833850729/100000000000000 : ℝ)^3161
        have hw : |(5258878887/10000000000 : ℝ)|=(5258878887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336649981/2500000000 : ℝ)*x 0 + (-555346283/2500000000 : ℝ)*x 1 + (2629439213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336649981/2500000000 : ℝ)^4185 ≤ (2728154641609/6250000000000 : ℝ)^3161 := by
    have hnat : (1336649981 : ℕ)^4185*6250000000000^3161 ≤ 2728154641609^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336649981 2500000000 2728154641609 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555346283/2500000000 : ℝ)^4185 ≤ (3411174205421/25000000000000 : ℝ)^3161 := by
    have hnat : (555346283 : ℕ)^4185*25000000000000^3161 ≤ 3411174205421^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555346283 2500000000 3411174205421 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629439213/5000000000 : ℝ)^4185 ≤ (42704828894449/100000000000000 : ℝ)^3161 := by
    have hnat : (2629439213 : ℕ)^4185*100000000000000^3161 ≤ 42704828894449^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629439213 5000000000 42704828894449 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336649981/2500000000 : ℝ), (-555346283/2500000000 : ℝ), (2629439213/5000000000 : ℝ)] ![(2728154641609/6250000000000 : ℝ), (3411174205421/25000000000000 : ℝ), (42704828894449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336649981/2500000000 : ℝ)|^4185 ≤ (2728154641609/6250000000000 : ℝ)^3161
        have hw : |(1336649981/2500000000 : ℝ)|=(1336649981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-555346283/2500000000 : ℝ)|^4185 ≤ (3411174205421/25000000000000 : ℝ)^3161
        have hw : |(-555346283/2500000000 : ℝ)|=(555346283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629439213/5000000000 : ℝ)|^4185 ≤ (42704828894449/100000000000000 : ℝ)^3161
        have hw : |(2629439213/5000000000 : ℝ)|=(2629439213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346600419/10000000000 : ℝ)*x 0 + (65735971/125000000 : ℝ)*x 1 + (-2221385461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346600419/10000000000 : ℝ)^4185 ≤ (43650479616159/100000000000000 : ℝ)^3161 := by
    have hnat : (5346600419 : ℕ)^4185*100000000000000^3161 ≤ 43650479616159^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346600419 10000000000 43650479616159 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65735971/125000000 : ℝ)^4185 ≤ (21352410437047/50000000000000 : ℝ)^3161 := by
    have hnat : (65735971 : ℕ)^4185*50000000000000^3161 ≤ 21352410437047^3161*125000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65735971 125000000 21352410437047 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221385461/10000000000 : ℝ)^4185 ≤ (3411174874299/25000000000000 : ℝ)^3161 := by
    have hnat : (2221385461 : ℕ)^4185*25000000000000^3161 ≤ 3411174874299^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221385461 10000000000 3411174874299 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346600419/10000000000 : ℝ), (65735971/125000000 : ℝ), (-2221385461/10000000000 : ℝ)] ![(43650479616159/100000000000000 : ℝ), (21352410437047/50000000000000 : ℝ), (3411174874299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346600419/10000000000 : ℝ)|^4185 ≤ (43650479616159/100000000000000 : ℝ)^3161
        have hw : |(5346600419/10000000000 : ℝ)|=(5346600419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65735971/125000000 : ℝ)|^4185 ≤ (21352410437047/50000000000000 : ℝ)^3161
        have hw : |(65735971/125000000 : ℝ)|=(65735971/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221385461/10000000000 : ℝ)|^4185 ≤ (3411174874299/25000000000000 : ℝ)^3161
        have hw : |(-2221385461/10000000000 : ℝ)|=(2221385461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544919337/1250000000 : ℝ)*x 0 + (1055002819/2500000000 : ℝ)*x 1 + (4503237969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544919337/1250000000 : ℝ)^4185 ≤ (33312997258027/100000000000000 : ℝ)^3161 := by
    have hnat : (544919337 : ℕ)^4185*100000000000000^3161 ≤ 33312997258027^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544919337 1250000000 33312997258027 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055002819/2500000000 : ℝ)^4185 ≤ (31910577295739/100000000000000 : ℝ)^3161 := by
    have hnat : (1055002819 : ℕ)^4185*100000000000000^3161 ≤ 31910577295739^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055002819 2500000000 31910577295739 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503237969/10000000000 : ℝ)^4185 ≤ (3477642543367/10000000000000 : ℝ)^3161 := by
    have hnat : (4503237969 : ℕ)^4185*10000000000000^3161 ≤ 3477642543367^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503237969 10000000000 3477642543367 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544919337/1250000000 : ℝ), (1055002819/2500000000 : ℝ), (4503237969/10000000000 : ℝ)] ![(33312997258027/100000000000000 : ℝ), (31910577295739/100000000000000 : ℝ), (3477642543367/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544919337/1250000000 : ℝ)|^4185 ≤ (33312997258027/100000000000000 : ℝ)^3161
        have hw : |(544919337/1250000000 : ℝ)|=(544919337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055002819/2500000000 : ℝ)|^4185 ≤ (31910577295739/100000000000000 : ℝ)^3161
        have hw : |(1055002819/2500000000 : ℝ)|=(1055002819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503237969/10000000000 : ℝ)|^4185 ≤ (3477642543367/10000000000000 : ℝ)^3161
        have hw : |(4503237969/10000000000 : ℝ)|=(4503237969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149563427/10000000000 : ℝ)*x 0 + (164352393/312500000 : ℝ)*x 1 + (674983651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149563427/10000000000 : ℝ)^4185 ≤ (6531852867591/50000000000000 : ℝ)^3161 := by
    have hnat : (2149563427 : ℕ)^4185*50000000000000^3161 ≤ 6531852867591^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149563427 10000000000 6531852867591 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164352393/312500000 : ℝ)^4185 ≤ (42709109516333/100000000000000 : ℝ)^3161 := by
    have hnat : (164352393 : ℕ)^4185*100000000000000^3161 ≤ 42709109516333^3161*312500000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164352393 312500000 42709109516333 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674983651/1250000000 : ℝ)^4185 ≤ (1382099522809/3125000000000 : ℝ)^3161 := by
    have hnat : (674983651 : ℕ)^4185*3125000000000^3161 ≤ 1382099522809^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674983651 1250000000 1382099522809 3125000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149563427/10000000000 : ℝ), (164352393/312500000 : ℝ), (674983651/1250000000 : ℝ)] ![(6531852867591/50000000000000 : ℝ), (42709109516333/100000000000000 : ℝ), (1382099522809/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149563427/10000000000 : ℝ)|^4185 ≤ (6531852867591/50000000000000 : ℝ)^3161
        have hw : |(-2149563427/10000000000 : ℝ)|=(2149563427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164352393/312500000 : ℝ)|^4185 ≤ (42709109516333/100000000000000 : ℝ)^3161
        have hw : |(164352393/312500000 : ℝ)|=(164352393/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674983651/1250000000 : ℝ)|^4185 ≤ (1382099522809/3125000000000 : ℝ)^3161
        have hw : |(674983651/1250000000 : ℝ)|=(674983651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310688653/10000000000 : ℝ)*x 0 + (-1040196829/5000000000 : ℝ)*x 1 + (5399869321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310688653/10000000000 : ℝ)^4185 ≤ (8652547038653/20000000000000 : ℝ)^3161 := by
    have hnat : (5310688653 : ℕ)^4185*20000000000000^3161 ≤ 8652547038653^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310688653 10000000000 8652547038653 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040196829/5000000000 : ℝ)^4185 ≤ (3127519706741/25000000000000 : ℝ)^3161 := by
    have hnat : (1040196829 : ℕ)^4185*25000000000000^3161 ≤ 3127519706741^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040196829 5000000000 3127519706741 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399869321/10000000000 : ℝ)^4185 ≤ (1769087438209/4000000000000 : ℝ)^3161 := by
    have hnat : (5399869321 : ℕ)^4185*4000000000000^3161 ≤ 1769087438209^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399869321 10000000000 1769087438209 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310688653/10000000000 : ℝ), (-1040196829/5000000000 : ℝ), (5399869321/10000000000 : ℝ)] ![(8652547038653/20000000000000 : ℝ), (3127519706741/25000000000000 : ℝ), (1769087438209/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310688653/10000000000 : ℝ)|^4185 ≤ (8652547038653/20000000000000 : ℝ)^3161
        have hw : |(5310688653/10000000000 : ℝ)|=(5310688653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040196829/5000000000 : ℝ)|^4185 ≤ (3127519706741/25000000000000 : ℝ)^3161
        have hw : |(-1040196829/5000000000 : ℝ)|=(1040196829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399869321/10000000000 : ℝ)|^4185 ≤ (1769087438209/4000000000000 : ℝ)^3161
        have hw : |(5399869321/10000000000 : ℝ)|=(5399869321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310688693/10000000000 : ℝ)*x 0 + (1349967289/2500000000 : ℝ)*x 1 + (-2080393831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310688693/10000000000 : ℝ)^4185 ≤ (43262735624679/100000000000000 : ℝ)^3161 := by
    have hnat : (5310688693 : ℕ)^4185*100000000000000^3161 ≤ 43262735624679^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310688693 10000000000 43262735624679 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349967289/2500000000 : ℝ)^4185 ≤ (345524876297/781250000000 : ℝ)^3161 := by
    have hnat : (1349967289 : ℕ)^4185*781250000000^3161 ≤ 345524876297^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349967289 2500000000 345524876297 781250000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080393831/10000000000 : ℝ)^4185 ≤ (12510080204273/100000000000000 : ℝ)^3161 := by
    have hnat : (2080393831 : ℕ)^4185*100000000000000^3161 ≤ 12510080204273^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080393831 10000000000 12510080204273 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310688693/10000000000 : ℝ), (1349967289/2500000000 : ℝ), (-2080393831/10000000000 : ℝ)] ![(43262735624679/100000000000000 : ℝ), (345524876297/781250000000 : ℝ), (12510080204273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310688693/10000000000 : ℝ)|^4185 ≤ (43262735624679/100000000000000 : ℝ)^3161
        have hw : |(5310688693/10000000000 : ℝ)|=(5310688693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349967289/2500000000 : ℝ)|^4185 ≤ (345524876297/781250000000 : ℝ)^3161
        have hw : |(1349967289/2500000000 : ℝ)|=(1349967289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080393831/10000000000 : ℝ)|^4185 ≤ (12510080204273/100000000000000 : ℝ)^3161
        have hw : |(-2080393831/10000000000 : ℝ)|=(2080393831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s4_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359368303/10000000000 : ℝ)*x 0 + (1125609847/2500000000 : ℝ)*x 1 + (4220813041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359368303/10000000000 : ℝ)^4185 ≤ (33313134923513/100000000000000 : ℝ)^3161 := by
    have hnat : (4359368303 : ℕ)^4185*100000000000000^3161 ≤ 33313134923513^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359368303 10000000000 33313134923513 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125609847/2500000000 : ℝ)^4185 ≤ (17384130392447/50000000000000 : ℝ)^3161 := by
    have hnat : (1125609847 : ℕ)^4185*50000000000000^3161 ≤ 17384130392447^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125609847 2500000000 17384130392447 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4220813041/10000000000 : ℝ)^4185 ≤ (31918604281157/100000000000000 : ℝ)^3161 := by
    have hnat : (4220813041 : ℕ)^4185*100000000000000^3161 ≤ 31918604281157^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220813041 10000000000 31918604281157 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359368303/10000000000 : ℝ), (1125609847/2500000000 : ℝ), (4220813041/10000000000 : ℝ)] ![(33313134923513/100000000000000 : ℝ), (17384130392447/50000000000000 : ℝ), (31918604281157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359368303/10000000000 : ℝ)|^4185 ≤ (33313134923513/100000000000000 : ℝ)^3161
        have hw : |(4359368303/10000000000 : ℝ)|=(4359368303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125609847/2500000000 : ℝ)|^4185 ≤ (17384130392447/50000000000000 : ℝ)^3161
        have hw : |(1125609847/2500000000 : ℝ)|=(1125609847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4220813041/10000000000 : ℝ)|^4185 ≤ (31918604281157/100000000000000 : ℝ)^3161
        have hw : |(4220813041/10000000000 : ℝ)|=(4220813041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (281/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (671/6250 : ℝ) ^ (8369/2048 : ℝ) ≤ (5477467656267807/50000000000000000000 : ℝ) := by
    have hpowers : (671/6250 : ℝ)^8369 ≤ (5477467656267807/50000000000000000000 : ℝ)^2048 := by
      have hnat : (671 : ℕ)^8369*50000000000000000000^2048 ≤ 5477467656267807^2048*6250^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        671 6250 5477467656267807 50000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (671/6250 : ℝ)) (X := (5477467656267807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (8369/2048 : ℝ) ≤ (20147648000628579/50000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^8369 ≤ (20147648000628579/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7383 : ℕ)^8369*50000000000000000000^2048 ≤ 20147648000628579^2048*50000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 20147648000628579 50000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (20147648000628579/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005477467656267807/25000000000000000000 : ℝ) ≤ (5000268058924599/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25005477467656267807/25000000000000000000 : ℝ)^2048 ≤ (5000268058924599/5000000000000000 : ℝ)^8369 := by
      have hnat : (25005477467656267807 : ℕ)^2048*5000000000000000^8369 ≤ 5000268058924599^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005477467656267807 25000000000000000000 5000268058924599 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268058924599/5000000000000000 : ℝ)) (X := (25005477467656267807/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012812557828448193/25000000000000000000 : ℝ) ≤ (2000250783045591/2000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25012812557828448193/25000000000000000000 : ℝ)^2048 ≤ (2000250783045591/2000000000000000 : ℝ)^8369 := by
      have hnat : (25012812557828448193 : ℕ)^2048*2000000000000000^8369 ≤ 2000250783045591^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012812557828448193 25000000000000000000 2000250783045591 2000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000250783045591/2000000000000000 : ℝ)) (X := (25012812557828448193/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020147648000628579/25000000000000000000 : ℝ) ≤ (1250246464075839/1250000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25020147648000628579/25000000000000000000 : ℝ)^2048 ≤ (1250246464075839/1250000000000000 : ℝ)^8369 := by
      have hnat : (25020147648000628579 : ℕ)^2048*1250000000000000^8369 ≤ 1250246464075839^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020147648000628579 25000000000000000000 1250246464075839 1250000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250246464075839/1250000000000000 : ℝ)) (X := (25020147648000628579/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477467656267807/50000000000000000000 : ℝ) ≤ ((10071687002403899409/10075000000000000000 : ℝ)+2*(717797378757/403000000000000 : ℝ)*(671/6250 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (10071687002403899409/10075000000000000000 : ℝ)+2*(717797378757/403000000000000 : ℝ)*(671/6250 : ℝ)=(5000268058924599/5000000000000000 : ℝ) by norm_num, show 1+2*(5477467656267807/50000000000000000000 : ℝ)=(25005477467656267807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20147648000628579/50000000000000000000 : ℝ)+(5477467656267807/50000000000000000000 : ℝ) ≤ ((10071687002403899409/10075000000000000000 : ℝ)+(717797378757/403000000000000 : ℝ)*((7383/50000 : ℝ)+(671/6250 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (10071687002403899409/10075000000000000000 : ℝ)+(717797378757/403000000000000 : ℝ)*((7383/50000 : ℝ)+(671/6250 : ℝ))=(2000250783045591/2000000000000000 : ℝ) by norm_num, show 1+(20147648000628579/50000000000000000000 : ℝ)+(5477467656267807/50000000000000000000 : ℝ)=(25012812557828448193/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20147648000628579/50000000000000000000 : ℝ) ≤ ((10071687002403899409/10075000000000000000 : ℝ)+2*(717797378757/403000000000000 : ℝ)*(7383/50000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (10071687002403899409/10075000000000000000 : ℝ)+2*(717797378757/403000000000000 : ℝ)*(7383/50000 : ℝ)=(1250246464075839/1250000000000000 : ℝ) by norm_num, show 1+2*(20147648000628579/50000000000000000000 : ℝ)=(25020147648000628579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10071687002403899409/10075000000000000000 : ℝ)*(X 1 0+X 2 0)+(717797378757/403000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (10071687002403899409/10075000000000000000 : ℝ)) (alpha := (717797378757/403000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10071687002403899409/10075000000000000000 : ℝ)*(X 0 1+X 2 1)+(717797378757/403000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (10071687002403899409/10075000000000000000 : ℝ)) (alpha := (717797378757/403000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10071687002403899409/10075000000000000000 : ℝ)*(X 0 2+X 1 2)+(717797378757/403000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (10071687002403899409/10075000000000000000 : ℝ)) (alpha := (717797378757/403000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107477791/500000000 : ℝ)*X 0 0+(1350067287/2500000000 : ℝ)*X 0 1+(5258878887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336649981/2500000000 : ℝ)*X 1 0+(-555346283/2500000000 : ℝ)*X 1 1+(2629439213/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346600419/10000000000 : ℝ)*X 2 0+(65735971/125000000 : ℝ)*X 2 1+(-2221385461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544919337/1250000000 : ℝ)*X 0 0+(1055002819/2500000000 : ℝ)*X 0 1+(4503237969/10000000000 : ℝ)*X 0 2+(544919337/1250000000 : ℝ)*X 1 0+(1055002819/2500000000 : ℝ)*X 1 1+(4503237969/10000000000 : ℝ)*X 1 2+(544919337/1250000000 : ℝ)*X 2 0+(1055002819/2500000000 : ℝ)*X 2 1+(4503237969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2149563427/10000000000 : ℝ)*X 0 0+(164352393/312500000 : ℝ)*X 0 1+(674983651/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310688653/10000000000 : ℝ)*X 1 0+(-1040196829/5000000000 : ℝ)*X 1 1+(5399869321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310688693/10000000000 : ℝ)*X 2 0+(1349967289/2500000000 : ℝ)*X 2 1+(-2080393831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359368303/10000000000 : ℝ)*X 0 0+(1125609847/2500000000 : ℝ)*X 0 1+(4220813041/10000000000 : ℝ)*X 0 2+(4359368303/10000000000 : ℝ)*X 1 0+(1125609847/2500000000 : ℝ)*X 1 1+(4220813041/10000000000 : ℝ)*X 1 2+(4359368303/10000000000 : ℝ)*X 2 0+(1125609847/2500000000 : ℝ)*X 2 1+(4220813041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (666750783810117811969122123/62968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259073847/50000000000000 : ℝ)*(base19) + (295067467/100000000000000 : ℝ)*(base23) + (381767513/100000000000000 : ℝ)*(lower2) + (80387017/100000000000000 : ℝ)*(lower3) + (16692639/50000000000000 : ℝ)*(lower4) + (1325420529167049/25000000000000 : ℝ)*(major0) + (1325420529167049/25000000000000 : ℝ)*(major1) + (1325420529167049/25000000000000 : ℝ)*(major2) + (3536303013858239/50000000000000 : ℝ)*(sp0) + (442037844348049/6250000000000 : ℝ)*(sp1) + (176814301085607/2500000000000 : ℝ)*(sp2) + (882686810269231/25000000000000 : ℝ)*(sp3) + (3368922473/10000000000000 : ℝ)*(sp6) + (10611589713/100000000000000 : ℝ)*(sp7) + (882689463166659/25000000000000 : ℝ)*(f.failure) + (3536303013858239/50000000000000 : ℝ)*(f.sum) + (53983065387539/10075000000000000000000000000 : ℝ)*base66 + (909908351091800959/251875000000000000000000000000000 : ℝ)*base68 + (709048910272425959/251875000000000000000000000000000 : ℝ)*base70 + (563339218742425959/251875000000000000000000000000000 : ℝ)*base72 + (11004477341157/5037500000000000000000000000 : ℝ)*base74 + (1153470761018675959/251875000000000000000000000000000 : ℝ)*base76 + (407826252481175959/251875000000000000000000000000000 : ℝ)*base78 + (2387921869528199041/251875000000000000000000000000000 : ℝ)*base79 + (11994905399739/10075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10435389/1250000000000000000000 : ℝ)*base90 + (10435389/1250000000000000000000 : ℝ)*base92 + (10435389/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273743218927076366499234093/503750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85769607/10000000000000 : ℝ)*(base19) + (666889717/50000000000000 : ℝ)*(base23) + (234007737/100000000000000 : ℝ)*(upper2) + (1740449/1250000000000 : ℝ)*(upper5) + (5331776349558159/100000000000000 : ℝ)*(major0) + (5331776349558159/100000000000000 : ℝ)*(major1) + (5331776349558159/100000000000000 : ℝ)*(major2) + (1180649907/50000000000000 : ℝ)*(sp0) + (36046125609/100000000000000 : ℝ)*(sp1) + (16682646711/50000000000000 : ℝ)*(sp2) + (1778187657495453/25000000000000 : ℝ)*(sp4) + (1778179021864987/25000000000000 : ℝ)*(sp5) + (7112718292208771/100000000000000 : ℝ)*(sp6) + (443849961215123/12500000000000 : ℝ)*(sp7) + (443849961215123/12500000000000 : ℝ)*(f.failure) + (7112752991281627/100000000000000 : ℝ)*(f.sum) + (66614379226163/20150000000000000000000000000 : ℝ)*base65 + (7300615935720303031/1007500000000000000000000000000000 : ℝ)*base67 + (7680437838394696969/1007500000000000000000000000000000 : ℝ)*base70 + (6237197735200303031/1007500000000000000000000000000000 : ℝ)*base71 + (25470100835363/20150000000000000000000000000 : ℝ)*base73 + (13863661627604696969/1007500000000000000000000000000000 : ℝ)*base76 + (1076089973507196969/1007500000000000000000000000000000 : ℝ)*base78 + (12206814721669696969/1007500000000000000000000000000000 : ℝ)*base80 + (89348412143213/20150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6355933/625000000000000000000 : ℝ)*base90 + (6355933/625000000000000000000 : ℝ)*base92 + (6355933/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_s5_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150122509/10000000000 : ℝ)*x 0 + (5394009683/10000000000 : ℝ)*x 1 + (5264766003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150122509/10000000000 : ℝ)^4185 ≤ (13068204371613/100000000000000 : ℝ)^3161 := by
    have hnat : (2150122509 : ℕ)^4185*100000000000000^3161 ≤ 13068204371613^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150122509 10000000000 13068204371613 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394009683/10000000000 : ℝ)^4185 ≤ (44163657038271/100000000000000 : ℝ)^3161 := by
    have hnat : (5394009683 : ℕ)^4185*100000000000000^3161 ≤ 44163657038271^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394009683 10000000000 44163657038271 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264766003/10000000000 : ℝ)^4185 ≤ (10692034644721/25000000000000 : ℝ)^3161 := by
    have hnat : (5264766003 : ℕ)^4185*25000000000000^3161 ≤ 10692034644721^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264766003 10000000000 10692034644721 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150122509/10000000000 : ℝ), (5394009683/10000000000 : ℝ), (5264766003/10000000000 : ℝ)] ![(13068204371613/100000000000000 : ℝ), (44163657038271/100000000000000 : ℝ), (10692034644721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150122509/10000000000 : ℝ)|^4185 ≤ (13068204371613/100000000000000 : ℝ)^3161
        have hw : |(-2150122509/10000000000 : ℝ)|=(2150122509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394009683/10000000000 : ℝ)|^4185 ≤ (44163657038271/100000000000000 : ℝ)^3161
        have hw : |(5394009683/10000000000 : ℝ)|=(5394009683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264766003/10000000000 : ℝ)|^4185 ≤ (10692034644721/25000000000000 : ℝ)^3161
        have hw : |(5264766003/10000000000 : ℝ)|=(5264766003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345024841/10000000000 : ℝ)*x 0 + (-2215691141/10000000000 : ℝ)*x 1 + (2632383011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345024841/10000000000 : ℝ)^4185 ≤ (1745338005371/4000000000000 : ℝ)^3161 := by
    have hnat : (5345024841 : ℕ)^4185*4000000000000^3161 ≤ 1745338005371^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345024841 10000000000 1745338005371 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215691141/10000000000 : ℝ)^4185 ≤ (6799205535087/50000000000000 : ℝ)^3161 := by
    have hnat : (2215691141 : ℕ)^4185*50000000000000^3161 ≤ 6799205535087^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215691141 10000000000 6799205535087 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632383011/5000000000 : ℝ)^4185 ≤ (4276813878323/10000000000000 : ℝ)^3161 := by
    have hnat : (2632383011 : ℕ)^4185*10000000000000^3161 ≤ 4276813878323^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632383011 5000000000 4276813878323 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345024841/10000000000 : ℝ), (-2215691141/10000000000 : ℝ), (2632383011/5000000000 : ℝ)] ![(1745338005371/4000000000000 : ℝ), (6799205535087/50000000000000 : ℝ), (4276813878323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345024841/10000000000 : ℝ)|^4185 ≤ (1745338005371/4000000000000 : ℝ)^3161
        have hw : |(5345024841/10000000000 : ℝ)|=(5345024841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2215691141/10000000000 : ℝ)|^4185 ≤ (6799205535087/50000000000000 : ℝ)^3161
        have hw : |(-2215691141/10000000000 : ℝ)|=(2215691141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632383011/5000000000 : ℝ)|^4185 ≤ (4276813878323/10000000000000 : ℝ)^3161
        have hw : |(2632383011/5000000000 : ℝ)|=(2632383011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345024811/10000000000 : ℝ)*x 0 + (1316191523/2500000000 : ℝ)*x 1 + (-138480693/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345024811/10000000000 : ℝ)^4185 ≤ (43633449810039/100000000000000 : ℝ)^3161 := by
    have hnat : (5345024811 : ℕ)^4185*100000000000000^3161 ≤ 43633449810039^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345024811 10000000000 43633449810039 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316191523/2500000000 : ℝ)^4185 ≤ (42768139536083/100000000000000 : ℝ)^3161 := by
    have hnat : (1316191523 : ℕ)^4185*100000000000000^3161 ≤ 42768139536083^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316191523 2500000000 42768139536083 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138480693/625000000 : ℝ)^4185 ≤ (13598410639523/100000000000000 : ℝ)^3161 := by
    have hnat : (138480693 : ℕ)^4185*100000000000000^3161 ≤ 13598410639523^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138480693 625000000 13598410639523 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345024811/10000000000 : ℝ), (1316191523/2500000000 : ℝ), (-138480693/625000000 : ℝ)] ![(43633449810039/100000000000000 : ℝ), (42768139536083/100000000000000 : ℝ), (13598410639523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345024811/10000000000 : ℝ)|^4185 ≤ (43633449810039/100000000000000 : ℝ)^3161
        have hw : |(5345024811/10000000000 : ℝ)|=(5345024811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316191523/2500000000 : ℝ)|^4185 ≤ (42768139536083/100000000000000 : ℝ)^3161
        have hw : |(1316191523/2500000000 : ℝ)|=(1316191523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138480693/625000000 : ℝ)|^4185 ≤ (13598410639523/100000000000000 : ℝ)^3161
        have hw : |(-138480693/625000000 : ℝ)|=(138480693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359685277/10000000000 : ℝ)*x 0 + (4232135231/10000000000 : ℝ)*x 1 + (280689279/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359685277/10000000000 : ℝ)^4185 ≤ (520567841713/1562500000000 : ℝ)^3161 := by
    have hnat : (4359685277 : ℕ)^4185*1562500000000^3161 ≤ 520567841713^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359685277 10000000000 520567841713 1562500000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232135231/10000000000 : ℝ)^4185 ≤ (32032010722759/100000000000000 : ℝ)^3161 := by
    have hnat : (4232135231 : ℕ)^4185*100000000000000^3161 ≤ 32032010722759^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232135231 10000000000 32032010722759 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280689279/625000000 : ℝ)^4185 ≤ (34651647386431/100000000000000 : ℝ)^3161 := by
    have hnat : (280689279 : ℕ)^4185*100000000000000^3161 ≤ 34651647386431^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280689279 625000000 34651647386431 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359685277/10000000000 : ℝ), (4232135231/10000000000 : ℝ), (280689279/625000000 : ℝ)] ![(520567841713/1562500000000 : ℝ), (32032010722759/100000000000000 : ℝ), (34651647386431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359685277/10000000000 : ℝ)|^4185 ≤ (520567841713/1562500000000 : ℝ)^3161
        have hw : |(4359685277/10000000000 : ℝ)|=(4359685277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232135231/10000000000 : ℝ)|^4185 ≤ (32032010722759/100000000000000 : ℝ)^3161
        have hw : |(4232135231/10000000000 : ℝ)|=(4232135231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280689279/625000000 : ℝ)|^4185 ≤ (34651647386431/100000000000000 : ℝ)^3161
        have hw : |(280689279/625000000 : ℝ)|=(280689279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150127419/10000000000 : ℝ)*x 0 + (2632549601/5000000000 : ℝ)*x 1 + (5393675439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150127419/10000000000 : ℝ)^4185 ≤ (13068243881459/100000000000000 : ℝ)^3161 := by
    have hnat : (2150127419 : ℕ)^4185*100000000000000^3161 ≤ 13068243881459^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150127419 10000000000 13068243881459 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632549601/5000000000 : ℝ)^4185 ≤ (2138586109297/5000000000000 : ℝ)^3161 := by
    have hnat : (2632549601 : ℕ)^4185*5000000000000^3161 ≤ 2138586109297^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632549601 5000000000 2138586109297 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393675439/10000000000 : ℝ)^4185 ≤ (44160033911463/100000000000000 : ℝ)^3161 := by
    have hnat : (5393675439 : ℕ)^4185*100000000000000^3161 ≤ 44160033911463^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393675439 10000000000 44160033911463 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150127419/10000000000 : ℝ), (2632549601/5000000000 : ℝ), (5393675439/10000000000 : ℝ)] ![(13068243881459/100000000000000 : ℝ), (2138586109297/5000000000000 : ℝ), (44160033911463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150127419/10000000000 : ℝ)|^4185 ≤ (13068243881459/100000000000000 : ℝ)^3161
        have hw : |(-2150127419/10000000000 : ℝ)|=(2150127419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632549601/5000000000 : ℝ)|^4185 ≤ (2138586109297/5000000000000 : ℝ)^3161
        have hw : |(2632549601/5000000000 : ℝ)|=(2632549601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393675439/10000000000 : ℝ)|^4185 ≤ (44160033911463/100000000000000 : ℝ)^3161
        have hw : |(5393675439/10000000000 : ℝ)|=(5393675439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312197047/10000000000 : ℝ)*x 0 + (-8151491/39062500 : ℝ)*x 1 + (5393675459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312197047/10000000000 : ℝ)^4185 ≤ (1081975112337/2500000000000 : ℝ)^3161 := by
    have hnat : (5312197047 : ℕ)^4185*2500000000000^3161 ≤ 1081975112337^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312197047 10000000000 1081975112337 2500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8151491/39062500 : ℝ)^4185 ≤ (12560961366483/100000000000000 : ℝ)^3161 := by
    have hnat : (8151491 : ℕ)^4185*100000000000000^3161 ≤ 12560961366483^3161*39062500^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8151491 39062500 12560961366483 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393675459/10000000000 : ℝ)^4185 ≤ (345000266627/781250000000 : ℝ)^3161 := by
    have hnat : (5393675459 : ℕ)^4185*781250000000^3161 ≤ 345000266627^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393675459 10000000000 345000266627 781250000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312197047/10000000000 : ℝ), (-8151491/39062500 : ℝ), (5393675459/10000000000 : ℝ)] ![(1081975112337/2500000000000 : ℝ), (12560961366483/100000000000000 : ℝ), (345000266627/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312197047/10000000000 : ℝ)|^4185 ≤ (1081975112337/2500000000000 : ℝ)^3161
        have hw : |(5312197047/10000000000 : ℝ)|=(5312197047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8151491/39062500 : ℝ)|^4185 ≤ (12560961366483/100000000000000 : ℝ)^3161
        have hw : |(-8151491/39062500 : ℝ)|=(8151491/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393675459/10000000000 : ℝ)|^4185 ≤ (345000266627/781250000000 : ℝ)^3161
        have hw : |(5393675459/10000000000 : ℝ)|=(5393675459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166006161/312500000 : ℝ)*x 0 + (337104711/625000000 : ℝ)*x 1 + (-1043390833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166006161/312500000 : ℝ)^4185 ≤ (8655801125209/20000000000000 : ℝ)^3161 := by
    have hnat : (166006161 : ℕ)^4185*20000000000000^3161 ≤ 8655801125209^3161*312500000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166006161 312500000 8655801125209 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337104711/625000000 : ℝ)^4185 ≤ (8832006645713/20000000000000 : ℝ)^3161 := by
    have hnat : (337104711 : ℕ)^4185*20000000000000^3161 ≤ 8832006645713^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337104711 625000000 8832006645713 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043390833/5000000000 : ℝ)^4185 ≤ (6280480563703/50000000000000 : ℝ)^3161 := by
    have hnat : (1043390833 : ℕ)^4185*50000000000000^3161 ≤ 6280480563703^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043390833 5000000000 6280480563703 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166006161/312500000 : ℝ), (337104711/625000000 : ℝ), (-1043390833/5000000000 : ℝ)] ![(8655801125209/20000000000000 : ℝ), (8832006645713/20000000000000 : ℝ), (6280480563703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166006161/312500000 : ℝ)|^4185 ≤ (8655801125209/20000000000000 : ℝ)^3161
        have hw : |(166006161/312500000 : ℝ)|=(166006161/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337104711/625000000 : ℝ)|^4185 ≤ (8832006645713/20000000000000 : ℝ)^3161
        have hw : |(337104711/625000000 : ℝ)|=(337104711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043390833/5000000000 : ℝ)|^4185 ≤ (6280480563703/50000000000000 : ℝ)^3161
        have hw : |(-1043390833/5000000000 : ℝ)|=(1043390833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s5_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871939113/2000000000 : ℝ)*x 0 + (1122590319/2500000000 : ℝ)*x 1 + (1058201239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871939113/2000000000 : ℝ)^4185 ≤ (16658222979247/50000000000000 : ℝ)^3161 := by
    have hnat : (871939113 : ℕ)^4185*50000000000000^3161 ≤ 16658222979247^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871939113 2000000000 16658222979247 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122590319/2500000000 : ℝ)^4185 ≤ (6928966411501/20000000000000 : ℝ)^3161 := by
    have hnat : (1122590319 : ℕ)^4185*20000000000000^3161 ≤ 6928966411501^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122590319 2500000000 6928966411501 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058201239/2500000000 : ℝ)^4185 ≤ (32038721970541/100000000000000 : ℝ)^3161 := by
    have hnat : (1058201239 : ℕ)^4185*100000000000000^3161 ≤ 32038721970541^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058201239 2500000000 32038721970541 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871939113/2000000000 : ℝ), (1122590319/2500000000 : ℝ), (1058201239/2500000000 : ℝ)] ![(16658222979247/50000000000000 : ℝ), (6928966411501/20000000000000 : ℝ), (32038721970541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871939113/2000000000 : ℝ)|^4185 ≤ (16658222979247/50000000000000 : ℝ)^3161
        have hw : |(871939113/2000000000 : ℝ)|=(871939113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122590319/2500000000 : ℝ)|^4185 ≤ (6928966411501/20000000000000 : ℝ)^3161
        have hw : |(1122590319/2500000000 : ℝ)|=(1122590319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058201239/2500000000 : ℝ)|^4185 ≤ (32038721970541/100000000000000 : ℝ)^3161
        have hw : |(1058201239/2500000000 : ℝ)|=(1058201239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (5683/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/2500 : ℝ) ^ (8369/2048 : ℝ) ≤ (6606888630108581/50000000000000000000 : ℝ) := by
    have hpowers : (281/2500 : ℝ)^8369 ≤ (6606888630108581/50000000000000000000 : ℝ)^2048 := by
      have hnat : (281 : ℕ)^8369*50000000000000000000^2048 ≤ 6606888630108581^2048*2500^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2500 6606888630108581 50000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2500 : ℝ)) (X := (6606888630108581/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8369/2048 : ℝ) ≤ (17342171290544019/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8369 ≤ (17342171290544019/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8369*50000000000000000000^2048 ≤ 17342171290544019^2048*50000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17342171290544019 50000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17342171290544019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006606888630108581/25000000000000000000 : ℝ) ≤ (10000646651103439/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25006606888630108581/25000000000000000000 : ℝ)^2048 ≤ (10000646651103439/10000000000000000 : ℝ)^8369 := by
      have hnat : (25006606888630108581 : ℕ)^2048*10000000000000000^8369 ≤ 10000646651103439^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006606888630108581 25000000000000000000 10000646651103439 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646651103439/10000000000000000 : ℝ)) (X := (25006606888630108581/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (250119745299603263/250000000000000000 : ℝ) ≤ (25002929788819/25000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (250119745299603263/250000000000000000 : ℝ)^2048 ≤ (25002929788819/25000000000000 : ℝ)^8369 := by
      have hnat : (250119745299603263 : ℕ)^2048*25000000000000^8369 ≤ 25002929788819^8369*250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250119745299603263 250000000000000000 25002929788819 25000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25002929788819/25000000000000 : ℝ)) (X := (250119745299603263/250000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017342171290544019/25000000000000000000 : ℝ) ≤ (10001697179951761/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25017342171290544019/25000000000000000000 : ℝ)^2048 ≤ (10001697179951761/10000000000000000 : ℝ)^8369 := by
      have hnat : (25017342171290544019 : ℕ)^2048*10000000000000000^8369 ≤ 10001697179951761^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017342171290544019 25000000000000000000 10001697179951761 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001697179951761/10000000000000000 : ℝ)) (X := (25017342171290544019/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6606888630108581/50000000000000000000 : ℝ) ≤ ((4988354688191426181/4990000000000000000 : ℝ)+2*(175088141387/99800000000000 : ℝ)*(281/2500 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (4988354688191426181/4990000000000000000 : ℝ)+2*(175088141387/99800000000000 : ℝ)*(281/2500 : ℝ)=(10000646651103439/10000000000000000 : ℝ) by norm_num, show 1+2*(6606888630108581/50000000000000000000 : ℝ)=(25006606888630108581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17342171290544019/50000000000000000000 : ℝ)+(6606888630108581/50000000000000000000 : ℝ) ≤ ((4988354688191426181/4990000000000000000 : ℝ)+(175088141387/99800000000000 : ℝ)*((7117/50000 : ℝ)+(281/2500 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (4988354688191426181/4990000000000000000 : ℝ)+(175088141387/99800000000000 : ℝ)*((7117/50000 : ℝ)+(281/2500 : ℝ))=(25002929788819/25000000000000 : ℝ) by norm_num, show 1+(17342171290544019/50000000000000000000 : ℝ)+(6606888630108581/50000000000000000000 : ℝ)=(250119745299603263/250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17342171290544019/50000000000000000000 : ℝ) ≤ ((4988354688191426181/4990000000000000000 : ℝ)+2*(175088141387/99800000000000 : ℝ)*(7117/50000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (4988354688191426181/4990000000000000000 : ℝ)+2*(175088141387/99800000000000 : ℝ)*(7117/50000 : ℝ)=(10001697179951761/10000000000000000 : ℝ) by norm_num, show 1+2*(17342171290544019/50000000000000000000 : ℝ)=(25017342171290544019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4988354688191426181/4990000000000000000 : ℝ)*(X 1 0+X 2 0)+(175088141387/99800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (4988354688191426181/4990000000000000000 : ℝ)) (alpha := (175088141387/99800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4988354688191426181/4990000000000000000 : ℝ)*(X 0 1+X 2 1)+(175088141387/99800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (4988354688191426181/4990000000000000000 : ℝ)) (alpha := (175088141387/99800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4988354688191426181/4990000000000000000 : ℝ)*(X 0 2+X 1 2)+(175088141387/99800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (4988354688191426181/4990000000000000000 : ℝ)) (alpha := (175088141387/99800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150122509/10000000000 : ℝ)*X 0 0+(5394009683/10000000000 : ℝ)*X 0 1+(5264766003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345024841/10000000000 : ℝ)*X 1 0+(-2215691141/10000000000 : ℝ)*X 1 1+(2632383011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345024811/10000000000 : ℝ)*X 2 0+(1316191523/2500000000 : ℝ)*X 2 1+(-138480693/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359685277/10000000000 : ℝ)*X 0 0+(4232135231/10000000000 : ℝ)*X 0 1+(280689279/625000000 : ℝ)*X 0 2+(4359685277/10000000000 : ℝ)*X 1 0+(4232135231/10000000000 : ℝ)*X 1 1+(280689279/625000000 : ℝ)*X 1 2+(4359685277/10000000000 : ℝ)*X 2 0+(4232135231/10000000000 : ℝ)*X 2 1+(280689279/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2150127419/10000000000 : ℝ)*X 0 0+(2632549601/5000000000 : ℝ)*X 0 1+(5393675439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312197047/10000000000 : ℝ)*X 1 0+(-8151491/39062500 : ℝ)*X 1 1+(5393675459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166006161/312500000 : ℝ)*X 2 0+(337104711/625000000 : ℝ)*X 2 1+(-1043390833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871939113/2000000000 : ℝ)*X 0 0+(1122590319/2500000000 : ℝ)*X 0 1+(1058201239/2500000000 : ℝ)*X 0 2+(871939113/2000000000 : ℝ)*X 1 0+(1122590319/2500000000 : ℝ)*X 1 1+(1058201239/2500000000 : ℝ)*X 1 2+(871939113/2000000000 : ℝ)*X 2 0+(1122590319/2500000000 : ℝ)*X 2 1+(1058201239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (481796665459296228102195321/249500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (652304097/100000000000000 : ℝ)*(base19) + (321249323/100000000000000 : ℝ)*(base23) + (212331599/100000000000000 : ℝ)*(upper3) + (38434393/25000000000000 : ℝ)*(upper4) + (80506181/100000000000000 : ℝ)*(upper5) + (5799973073446647/100000000000000 : ℝ)*(major0) + (5799973073446647/100000000000000 : ℝ)*(major1) + (5799973073446647/100000000000000 : ℝ)*(major2) + (967166636191363/12500000000000 : ℝ)*(sp0) + (1934335266840819/25000000000000 : ℝ)*(sp1) + (154746827968361/2000000000000 : ℝ)*(sp2) + (1931299154881257/50000000000000 : ℝ)*(sp3) + (863013647/10000000000000 : ℝ)*(sp4) + (1210619021/20000000000000 : ℝ)*(sp7) + (193130218142881/5000000000000 : ℝ)*(f.failure) + (7737341719667373/100000000000000 : ℝ)*(f.sum) + (29833640160759/4990000000000000000000000000 : ℝ)*base65 + (2756896903802084893/499000000000000000000000000000000 : ℝ)*base68 + (3483755688970084893/499000000000000000000000000000000 : ℝ)*base70 + (5017408459430915107/499000000000000000000000000000000 : ℝ)*base71 + (16489780557369/4990000000000000000000000000 : ℝ)*base73 + (1767790012940084893/499000000000000000000000000000000 : ℝ)*base76 + (9358332158135084893/499000000000000000000000000000000 : ℝ)*base78 + (2917271902425915107/499000000000000000000000000000000 : ℝ)*base79 + (31277876704149/4990000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (197951/250000000000000000000 : ℝ)*base90 + (197951/250000000000000000000 : ℝ)*base92 + (197951/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26157259544399455600653/4990000000000000000000000000 : ℝ) := by norm_num
    linear_combination (318627449/50000000000000 : ℝ)*(base19) + (180876649/20000000000000 : ℝ)*(base23) + (18520079/20000000000000 : ℝ)*(upper3) + (44839981/100000000000000 : ℝ)*(lower4) + (106103073/100000000000000 : ℝ)*(upper5) + (5830067212306167/100000000000000 : ℝ)*(major0) + (5830067212306167/100000000000000 : ℝ)*(major1) + (5830067212306167/100000000000000 : ℝ)*(major2) + (1679433833/10000000000000 : ℝ)*(sp1) + (1074282389/5000000000000 : ℝ)*(sp2) + (7777488112590561/100000000000000 : ℝ)*(sp4) + (1944367670249333/25000000000000 : ℝ)*(sp5) + (486091607659971/6250000000000 : ℝ)*(sp6) + (1941323068645287/50000000000000 : ℝ)*(sp7) + (1941323068645287/50000000000000 : ℝ)*(f.failure) + (7777488112590561/100000000000000 : ℝ)*(f.sum) + (8550459098861/4990000000000000000000000000 : ℝ)*base66 + (187554744820991773/499000000000000000000000000000000 : ℝ)*base68 + (598983387956008227/499000000000000000000000000000000 : ℝ)*base69 + (2671374000122991773/499000000000000000000000000000000 : ℝ)*base72 + (8356506351849/4990000000000000000000000000 : ℝ)*base73 + (8842379870825008227/499000000000000000000000000000000 : ℝ)*base75 + (537139482204991773/499000000000000000000000000000000 : ℝ)*base78 + (7326173197153008227/499000000000000000000000000000000 : ℝ)*base79 + (4370542724909/4990000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4257177/2500000000000000000000 : ℝ)*base90 + (4257177/2500000000000000000000 : ℝ)*base92 + (4257177/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1177_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1177_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1177_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1177_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
