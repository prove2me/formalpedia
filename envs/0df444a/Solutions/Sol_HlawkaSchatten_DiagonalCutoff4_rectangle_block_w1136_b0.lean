-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1136_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:14.708658+00:00
-- url     : https://prove2.me/submissions/df8d964e-6213-49a2-8a32-70d45479aec2

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
theorem support_rectangle_w1136_s0_0 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893711431/10000000000 : ℝ)*x 0 + (1513929467/2500000000 : ℝ)*x 1 + (4779712929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893711431/10000000000 : ℝ)^8329 ≤ (1100709630929/10000000000000 : ℝ)^6281 := by
    have hnat : (1893711431 : ℕ)^8329*10000000000000^6281 ≤ 1100709630929^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893711431 10000000000 1100709630929 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1513929467/2500000000 : ℝ)^8329 ≤ (51420697748817/100000000000000 : ℝ)^6281 := by
    have hnat : (1513929467 : ℕ)^8329*100000000000000^6281 ≤ 51420697748817^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513929467 2500000000 51420697748817 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779712929/10000000000 : ℝ)^8329 ≤ (18786102964543/50000000000000 : ℝ)^6281 := by
    have hnat : (4779712929 : ℕ)^8329*50000000000000^6281 ≤ 18786102964543^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779712929 10000000000 18786102964543 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893711431/10000000000 : ℝ), (1513929467/2500000000 : ℝ), (4779712929/10000000000 : ℝ)] ![(1100709630929/10000000000000 : ℝ), (51420697748817/100000000000000 : ℝ), (18786102964543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893711431/10000000000 : ℝ)|^8329 ≤ (1100709630929/10000000000000 : ℝ)^6281
        have hw : |(-1893711431/10000000000 : ℝ)|=(1893711431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1513929467/2500000000 : ℝ)|^8329 ≤ (51420697748817/100000000000000 : ℝ)^6281
        have hw : |(1513929467/2500000000 : ℝ)|=(1513929467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779712929/10000000000 : ℝ)|^8329 ≤ (18786102964543/50000000000000 : ℝ)^6281
        have hw : |(4779712929/10000000000 : ℝ)|=(4779712929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_1 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689641383/1250000000 : ℝ)*x 0 + (-262616053/1000000000 : ℝ)*x 1 + (2389856593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689641383/1250000000 : ℝ)^8329 ≤ (45445996975087/100000000000000 : ℝ)^6281 := by
    have hnat : (689641383 : ℕ)^8329*100000000000000^6281 ≤ 45445996975087^6281*1250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689641383 1250000000 45445996975087 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262616053/1000000000 : ℝ)^8329 ≤ (16981794395937/100000000000000 : ℝ)^6281 := by
    have hnat : (262616053 : ℕ)^8329*100000000000000^6281 ≤ 16981794395937^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262616053 1000000000 16981794395937 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389856593/5000000000 : ℝ)^8329 ≤ (37572208608021/100000000000000 : ℝ)^6281 := by
    have hnat : (2389856593 : ℕ)^8329*100000000000000^6281 ≤ 37572208608021^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389856593 5000000000 37572208608021 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689641383/1250000000 : ℝ), (-262616053/1000000000 : ℝ), (2389856593/5000000000 : ℝ)] ![(45445996975087/100000000000000 : ℝ), (16981794395937/100000000000000 : ℝ), (37572208608021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689641383/1250000000 : ℝ)|^8329 ≤ (45445996975087/100000000000000 : ℝ)^6281
        have hw : |(689641383/1250000000 : ℝ)|=(689641383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262616053/1000000000 : ℝ)|^8329 ≤ (16981794395937/100000000000000 : ℝ)^6281
        have hw : |(-262616053/1000000000 : ℝ)|=(262616053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2389856593/5000000000 : ℝ)|^8329 ≤ (37572208608021/100000000000000 : ℝ)^6281
        have hw : |(2389856593/5000000000 : ℝ)|=(2389856593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_2 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517132637/10000000000 : ℝ)*x 0 + (477971253/1000000000 : ℝ)*x 1 + (-105046373/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517132637/10000000000 : ℝ)^8329 ≤ (45446014157143/100000000000000 : ℝ)^6281 := by
    have hnat : (5517132637 : ℕ)^8329*100000000000000^6281 ≤ 45446014157143^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517132637 10000000000 45446014157143 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477971253/1000000000 : ℝ)^8329 ≤ (18786100884981/50000000000000 : ℝ)^6281 := by
    have hnat : (477971253 : ℕ)^8329*50000000000000^6281 ≤ 18786100884981^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477971253 1000000000 18786100884981 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105046373/400000000 : ℝ)^8329 ≤ (16981784063247/100000000000000 : ℝ)^6281 := by
    have hnat : (105046373 : ℕ)^8329*100000000000000^6281 ≤ 16981784063247^6281*400000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105046373 400000000 16981784063247 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517132637/10000000000 : ℝ), (477971253/1000000000 : ℝ), (-105046373/400000000 : ℝ)] ![(45446014157143/100000000000000 : ℝ), (18786100884981/50000000000000 : ℝ), (16981784063247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517132637/10000000000 : ℝ)|^8329 ≤ (45446014157143/100000000000000 : ℝ)^6281
        have hw : |(5517132637/10000000000 : ℝ)|=(5517132637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(477971253/1000000000 : ℝ)|^8329 ≤ (18786100884981/50000000000000 : ℝ)^6281
        have hw : |(477971253/1000000000 : ℝ)|=(477971253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105046373/400000000 : ℝ)|^8329 ≤ (16981784063247/100000000000000 : ℝ)^6281
        have hw : |(-105046373/400000000 : ℝ)|=(105046373/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_3 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (262592299/625000000 : ℝ)*x 0 + (3121357783/10000000000 : ℝ)*x 1 + (2828474889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262592299/625000000 : ℝ)^8329 ≤ (494797403741/1562500000000 : ℝ)^6281 := by
    have hnat : (262592299 : ℕ)^8329*1562500000000^6281 ≤ 494797403741^6281*625000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262592299 625000000 494797403741 1562500000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121357783/10000000000 : ℝ)^8329 ≤ (21353439108273/100000000000000 : ℝ)^6281 := by
    have hnat : (3121357783 : ℕ)^8329*100000000000000^6281 ≤ 21353439108273^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121357783 10000000000 21353439108273 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2828474889/5000000000 : ℝ)^8329 ≤ (23489763518193/50000000000000 : ℝ)^6281 := by
    have hnat : (2828474889 : ℕ)^8329*50000000000000^6281 ≤ 23489763518193^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2828474889 5000000000 23489763518193 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262592299/625000000 : ℝ), (3121357783/10000000000 : ℝ), (2828474889/5000000000 : ℝ)] ![(494797403741/1562500000000 : ℝ), (21353439108273/100000000000000 : ℝ), (23489763518193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262592299/625000000 : ℝ)|^8329 ≤ (494797403741/1562500000000 : ℝ)^6281
        have hw : |(262592299/625000000 : ℝ)|=(262592299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121357783/10000000000 : ℝ)|^8329 ≤ (21353439108273/100000000000000 : ℝ)^6281
        have hw : |(3121357783/10000000000 : ℝ)|=(3121357783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2828474889/5000000000 : ℝ)|^8329 ≤ (23489763518193/50000000000000 : ℝ)^6281
        have hw : |(2828474889/5000000000 : ℝ)|=(2828474889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_4 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898874417/10000000000 : ℝ)*x 0 + (2406316621/5000000000 : ℝ)*x 1 + (6021640759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898874417/10000000000 : ℝ)^8329 ≤ (11046908571783/100000000000000 : ℝ)^6281 := by
    have hnat : (1898874417 : ℕ)^8329*100000000000000^6281 ≤ 11046908571783^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898874417 10000000000 11046908571783 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406316621/5000000000 : ℝ)^8329 ≤ (7583149538459/20000000000000 : ℝ)^6281 := by
    have hnat : (2406316621 : ℕ)^8329*20000000000000^6281 ≤ 7583149538459^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406316621 5000000000 7583149538459 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6021640759/10000000000 : ℝ)^8329 ≤ (10207468745129/20000000000000 : ℝ)^6281 := by
    have hnat : (6021640759 : ℕ)^8329*20000000000000^6281 ≤ 10207468745129^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021640759 10000000000 10207468745129 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898874417/10000000000 : ℝ), (2406316621/5000000000 : ℝ), (6021640759/10000000000 : ℝ)] ![(11046908571783/100000000000000 : ℝ), (7583149538459/20000000000000 : ℝ), (10207468745129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898874417/10000000000 : ℝ)|^8329 ≤ (11046908571783/100000000000000 : ℝ)^6281
        have hw : |(-1898874417/10000000000 : ℝ)|=(1898874417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406316621/5000000000 : ℝ)|^8329 ≤ (7583149538459/20000000000000 : ℝ)^6281
        have hw : |(2406316621/5000000000 : ℝ)|=(2406316621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6021640759/10000000000 : ℝ)|^8329 ≤ (10207468745129/20000000000000 : ℝ)^6281
        have hw : |(6021640759/10000000000 : ℝ)|=(6021640759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_5 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517044213/1000000000 : ℝ)*x 0 + (-276846467/2000000000 : ℝ)*x 1 + (6021640651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517044213/1000000000 : ℝ)^8329 ≤ (20849216549329/50000000000000 : ℝ)^6281 := by
    have hnat : (517044213 : ℕ)^8329*50000000000000^6281 ≤ 20849216549329^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517044213 1000000000 20849216549329 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276846467/2000000000 : ℝ)^8329 ≤ (7264224368293/100000000000000 : ℝ)^6281 := by
    have hnat : (276846467 : ℕ)^8329*100000000000000^6281 ≤ 7264224368293^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276846467 2000000000 7264224368293 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6021640651/10000000000 : ℝ)^8329 ≤ (51037342511807/100000000000000 : ℝ)^6281 := by
    have hnat : (6021640651 : ℕ)^8329*100000000000000^6281 ≤ 51037342511807^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021640651 10000000000 51037342511807 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517044213/1000000000 : ℝ), (-276846467/2000000000 : ℝ), (6021640651/10000000000 : ℝ)] ![(20849216549329/50000000000000 : ℝ), (7264224368293/100000000000000 : ℝ), (51037342511807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517044213/1000000000 : ℝ)|^8329 ≤ (20849216549329/50000000000000 : ℝ)^6281
        have hw : |(517044213/1000000000 : ℝ)|=(517044213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276846467/2000000000 : ℝ)|^8329 ≤ (7264224368293/100000000000000 : ℝ)^6281
        have hw : |(-276846467/2000000000 : ℝ)|=(276846467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6021640651/10000000000 : ℝ)|^8329 ≤ (51037342511807/100000000000000 : ℝ)^6281
        have hw : |(6021640651/10000000000 : ℝ)|=(6021640651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_6 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034088429/2000000000 : ℝ)*x 0 + (301082033/500000000 : ℝ)*x 1 + (-1384232299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034088429/2000000000 : ℝ)^8329 ≤ (20849216629537/50000000000000 : ℝ)^6281 := by
    have hnat : (1034088429 : ℕ)^8329*50000000000000^6281 ≤ 20849216629537^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034088429 2000000000 20849216629537 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301082033/500000000 : ℝ)^8329 ≤ (318983391331/625000000000 : ℝ)^6281 := by
    have hnat : (301082033 : ℕ)^8329*625000000000^6281 ≤ 318983391331^6281*500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301082033 500000000 318983391331 625000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1384232299/10000000000 : ℝ)^8329 ≤ (726422411777/10000000000000 : ℝ)^6281 := by
    have hnat : (1384232299 : ℕ)^8329*10000000000000^6281 ≤ 726422411777^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384232299 10000000000 726422411777 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034088429/2000000000 : ℝ), (301082033/500000000 : ℝ), (-1384232299/10000000000 : ℝ)] ![(20849216629537/50000000000000 : ℝ), (318983391331/625000000000 : ℝ), (726422411777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034088429/2000000000 : ℝ)|^8329 ≤ (20849216629537/50000000000000 : ℝ)^6281
        have hw : |(1034088429/2000000000 : ℝ)|=(1034088429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301082033/500000000 : ℝ)|^8329 ≤ (318983391331/625000000000 : ℝ)^6281
        have hw : |(301082033/500000000 : ℝ)|=(301082033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1384232299/10000000000 : ℝ)|^8329 ≤ (726422411777/10000000000000 : ℝ)^6281
        have hw : |(-1384232299/10000000000 : ℝ)|=(1384232299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s0_7 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4211736749/10000000000 : ℝ)*x 0 + (5591532721/10000000000 : ℝ)*x 1 + (127562969/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211736749/10000000000 : ℝ)^8329 ≤ (31769619849423/100000000000000 : ℝ)^6281 := by
    have hnat : (4211736749 : ℕ)^8329*100000000000000^6281 ≤ 31769619849423^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211736749 10000000000 31769619849423 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591532721/10000000000 : ℝ)^8329 ≤ (46260476028361/100000000000000 : ℝ)^6281 := by
    have hnat : (5591532721 : ℕ)^8329*100000000000000^6281 ≤ 46260476028361^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591532721 10000000000 46260476028361 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127562969/400000000 : ℝ)^8329 ≤ (21969904113517/100000000000000 : ℝ)^6281 := by
    have hnat : (127562969 : ℕ)^8329*100000000000000^6281 ≤ 21969904113517^6281*400000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127562969 400000000 21969904113517 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211736749/10000000000 : ℝ), (5591532721/10000000000 : ℝ), (127562969/400000000 : ℝ)] ![(31769619849423/100000000000000 : ℝ), (46260476028361/100000000000000 : ℝ), (21969904113517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211736749/10000000000 : ℝ)|^8329 ≤ (31769619849423/100000000000000 : ℝ)^6281
        have hw : |(4211736749/10000000000 : ℝ)|=(4211736749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591532721/10000000000 : ℝ)|^8329 ≤ (46260476028361/100000000000000 : ℝ)^6281
        have hw : |(5591532721/10000000000 : ℝ)|=(5591532721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127562969/400000000 : ℝ)|^8329 ≤ (21969904113517/100000000000000 : ℝ)^6281
        have hw : |(127562969/400000000 : ℝ)|=(127562969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1136_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13919/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1041/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1041 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1041*1^256 ≤ 0^256*1^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1041/256 : ℝ) ≤ (2408874984443498209/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1041 ≤ (2408874984443498209/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1041*100000000000000000000^256 ≤ 2408874984443498209^256*5^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2408874984443498209 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2408874984443498209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1041 := by
      have hnat : (1 : ℕ)^256*1^1041 ≤ 1^1041*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102408874984443498209/100000000000000000000 : ℝ) ≤ (10058707848424869/10000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (102408874984443498209/100000000000000000000 : ℝ)^256 ≤ (10058707848424869/10000000000000000 : ℝ)^1041 := by
      have hnat : (102408874984443498209 : ℕ)^256*10000000000000000^1041 ≤ 10058707848424869^1041*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102408874984443498209 100000000000000000000 10058707848424869 10000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058707848424869/10000000000000000 : ℝ)) (X := (102408874984443498209/100000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52408874984443498209/50000000000000000000 : ℝ) ≤ (5058707848424869/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (52408874984443498209/50000000000000000000 : ℝ)^256 ≤ (5058707848424869/5000000000000000 : ℝ)^1041 := by
      have hnat : (52408874984443498209 : ℕ)^256*5000000000000000^1041 ≤ 5058707848424869^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52408874984443498209 50000000000000000000 5058707848424869 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058707848424869/5000000000000000 : ℝ)) (X := (52408874984443498209/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58707848424869/4000000000000000 : ℝ)*(0 : ℝ))^(1041/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(58707848424869/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2408874984443498209/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58707848424869/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1041/256 : ℝ) := by
    rw [show (1 : ℝ)+(58707848424869/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058707848424869/10000000000000000 : ℝ) by norm_num, show 1+(2408874984443498209/100000000000000000000 : ℝ)+(0 : ℝ)=(102408874984443498209/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2408874984443498209/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58707848424869/4000000000000000 : ℝ)*(2/5 : ℝ))^(1041/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(58707848424869/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058707848424869/5000000000000000 : ℝ) by norm_num, show 1+2*(2408874984443498209/100000000000000000000 : ℝ)=(52408874984443498209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58707848424869/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58707848424869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58707848424869/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58707848424869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58707848424869/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58707848424869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1893711431/10000000000 : ℝ)*X 0 0+(1513929467/2500000000 : ℝ)*X 0 1+(4779712929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689641383/1250000000 : ℝ)*X 1 0+(-262616053/1000000000 : ℝ)*X 1 1+(2389856593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517132637/10000000000 : ℝ)*X 2 0+(477971253/1000000000 : ℝ)*X 2 1+(-105046373/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262592299/625000000 : ℝ)*X 0 0+(3121357783/10000000000 : ℝ)*X 0 1+(2828474889/5000000000 : ℝ)*X 0 2+(262592299/625000000 : ℝ)*X 1 0+(3121357783/10000000000 : ℝ)*X 1 1+(2828474889/5000000000 : ℝ)*X 1 2+(262592299/625000000 : ℝ)*X 2 0+(3121357783/10000000000 : ℝ)*X 2 1+(2828474889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1898874417/10000000000 : ℝ)*X 0 0+(2406316621/5000000000 : ℝ)*X 0 1+(6021640759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517044213/1000000000 : ℝ)*X 1 0+(-276846467/2000000000 : ℝ)*X 1 1+(6021640651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034088429/2000000000 : ℝ)*X 2 0+(301082033/500000000 : ℝ)*X 2 1+(-1384232299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211736749/10000000000 : ℝ)*X 0 0+(5591532721/10000000000 : ℝ)*X 0 1+(127562969/400000000 : ℝ)*X 0 2+(4211736749/10000000000 : ℝ)*X 1 0+(5591532721/10000000000 : ℝ)*X 1 1+(127562969/400000000 : ℝ)*X 1 2+(4211736749/10000000000 : ℝ)*X 2 0+(5591532721/10000000000 : ℝ)*X 2 1+(127562969/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (259804626599773442778393/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12719579/100000000000000 : ℝ)*(base1) + (723387677/100000000000000 : ℝ)*(base19) + (155833917/20000000000000 : ℝ)*(base23) + (20957501/12500000000000 : ℝ)*(base24) + (97477021/50000000000000 : ℝ)*(upper3) + (589043569878999/100000000000000 : ℝ)*(major0) + (589043569878999/100000000000000 : ℝ)*(major1) + (589043569878999/100000000000000 : ℝ)*(major2) + (783698252190393/100000000000000 : ℝ)*(sp0) + (12245298440711/1562500000000 : ℝ)*(sp1) + (783698876763589/100000000000000 : ℝ)*(sp2) + (39438582478603/10000000000000 : ℝ)*(sp3) + (3093989/195312500000 : ℝ)*(sp4) + (1392057661/100000000000000 : ℝ)*(sp7) + (39438722956327/10000000000000 : ℝ)*(f.failure) + (391849911796591/50000000000000 : ℝ)*(f.sum) + (330561118426131/200000000000000000000000000000 : ℝ)*base65 + (1080223427973869/400000000000000000000000000000 : ℝ)*base68 + (3235415917173869/400000000000000000000000000000 : ℝ)*base70 + (294019926426131/400000000000000000000000000000 : ℝ)*base71 + (107192917773869/200000000000000000000000000000 : ℝ)*base74 + (606789148826131/400000000000000000000000000000 : ℝ)*base75 + (867171248373869/400000000000000000000000000000 : ℝ)*base78 + (1692411823973869/400000000000000000000000000000 : ℝ)*base80 + (124239255573869/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (575071/500000000000000000000 : ℝ)*base90 + (575071/500000000000000000000 : ℝ)*base92 + (575071/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13830713303762124264597/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7348323/12500000000000 : ℝ)*(base1) + (217315633/20000000000000 : ℝ)*(base19) + (3400669/312500000000 : ℝ)*(base23) + (58108163/50000000000000 : ℝ)*(upper3) + (2009389/1562500000000 : ℝ)*(upper5) + (9713790565071/1562500000000 : ℝ)*(major0) + (9713790565071/1562500000000 : ℝ)*(major1) + (9713790565071/1562500000000 : ℝ)*(major2) + (218798123/10000000000000 : ℝ)*(sp1) + (2176582411/100000000000000 : ℝ)*(sp2) + (41356239794921/5000000000000 : ℝ)*(sp4) + (413560731276221/50000000000000 : ℝ)*(sp5) + (165424294463069/20000000000000 : ℝ)*(sp6) + (104060062225763/25000000000000 : ℝ)*(sp7) + (83248061537927/20000000000000 : ℝ)*(f.failure) + (206781184277959/25000000000000 : ℝ)*(f.sum) + (2179746625699/3125000000000000000000000000 : ℝ)*base65 + (4848035825699/6250000000000000000000000000 : ℝ)*base67 + (48843797599301/6250000000000000000000000000 : ℝ)*base70 + (51512751649301/6250000000000000000000000000 : ℝ)*base72 + (13491110019449/3125000000000000000000000000 : ℝ)*base73 + (66483283486801/6250000000000000000000000000 : ℝ)*base76 + (4221205724301/6250000000000000000000000000 : ℝ)*base78 + (38157963486801/6250000000000000000000000000 : ℝ)*base80 + (6376932005551/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4591871/1000000000000000000000 : ℝ)*base90 + (4591871/1000000000000000000000 : ℝ)*base92 + (4591871/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1136_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13919/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1136_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1136_s1_0 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-262351241/1250000000 : ℝ)*x 0 + (5703110633/10000000000 : ℝ)*x 1 + (5001014141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262351241/1250000000 : ℝ)^8329 ≤ (3153797615709/25000000000000 : ℝ)^6281 := by
    have hnat : (262351241 : ℕ)^8329*25000000000000^6281 ≤ 3153797615709^6281*1250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262351241 1250000000 3153797615709 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5703110633/10000000000 : ℝ)^8329 ≤ (1484017303837/3125000000000 : ℝ)^6281 := by
    have hnat : (5703110633 : ℕ)^8329*3125000000000^6281 ≤ 1484017303837^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5703110633 10000000000 1484017303837 3125000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5001014141/10000000000 : ℝ)^8329 ≤ (9974063949797/25000000000000 : ℝ)^6281 := by
    have hnat : (5001014141 : ℕ)^8329*25000000000000^6281 ≤ 9974063949797^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001014141 10000000000 9974063949797 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262351241/1250000000 : ℝ), (5703110633/10000000000 : ℝ), (5001014141/10000000000 : ℝ)] ![(3153797615709/25000000000000 : ℝ), (1484017303837/3125000000000 : ℝ), (9974063949797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262351241/1250000000 : ℝ)|^8329 ≤ (3153797615709/25000000000000 : ℝ)^6281
        have hw : |(-262351241/1250000000 : ℝ)|=(262351241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5703110633/10000000000 : ℝ)|^8329 ≤ (1484017303837/3125000000000 : ℝ)^6281
        have hw : |(5703110633/10000000000 : ℝ)|=(5703110633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5001014141/10000000000 : ℝ)|^8329 ≤ (9974063949797/25000000000000 : ℝ)^6281
        have hw : |(5001014141/10000000000 : ℝ)|=(5001014141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_1 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709725773/5000000000 : ℝ)*x 0 + (-495563107/2000000000 : ℝ)*x 1 + (2500506787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709725773/5000000000 : ℝ)^8329 ≤ (44382124681247/100000000000000 : ℝ)^6281 := by
    have hnat : (2709725773 : ℕ)^8329*100000000000000^6281 ≤ 44382124681247^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709725773 5000000000 44382124681247 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495563107/2000000000 : ℝ)^8329 ≤ (7860812749217/50000000000000 : ℝ)^6281 := by
    have hnat : (495563107 : ℕ)^8329*50000000000000^6281 ≤ 7860812749217^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495563107 2000000000 7860812749217 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2500506787/5000000000 : ℝ)^8329 ≤ (7979249960197/20000000000000 : ℝ)^6281 := by
    have hnat : (2500506787 : ℕ)^8329*20000000000000^6281 ≤ 7979249960197^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500506787 5000000000 7979249960197 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709725773/5000000000 : ℝ), (-495563107/2000000000 : ℝ), (2500506787/5000000000 : ℝ)] ![(44382124681247/100000000000000 : ℝ), (7860812749217/50000000000000 : ℝ), (7979249960197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709725773/5000000000 : ℝ)|^8329 ≤ (44382124681247/100000000000000 : ℝ)^6281
        have hw : |(2709725773/5000000000 : ℝ)|=(2709725773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495563107/2000000000 : ℝ)|^8329 ≤ (7860812749217/50000000000000 : ℝ)^6281
        have hw : |(-495563107/2000000000 : ℝ)|=(495563107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2500506787/5000000000 : ℝ)|^8329 ≤ (7979249960197/20000000000000 : ℝ)^6281
        have hw : |(2500506787/5000000000 : ℝ)|=(2500506787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_2 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709726691/5000000000 : ℝ)*x 0 + (156281623/312500000 : ℝ)*x 1 + (-1238907613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709726691/5000000000 : ℝ)^8329 ≤ (44382144619611/100000000000000 : ℝ)^6281 := by
    have hnat : (2709726691 : ℕ)^8329*100000000000000^6281 ≤ 44382144619611^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709726691 5000000000 44382144619611 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156281623/312500000 : ℝ)^8329 ≤ (39896232472843/100000000000000 : ℝ)^6281 := by
    have hnat : (156281623 : ℕ)^8329*100000000000000^6281 ≤ 39896232472843^6281*312500000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156281623 312500000 39896232472843 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1238907613/5000000000 : ℝ)^8329 ≤ (1965202862321/12500000000000 : ℝ)^6281 := by
    have hnat : (1238907613 : ℕ)^8329*12500000000000^6281 ≤ 1965202862321^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238907613 5000000000 1965202862321 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709726691/5000000000 : ℝ), (156281623/312500000 : ℝ), (-1238907613/5000000000 : ℝ)] ![(44382144619611/100000000000000 : ℝ), (39896232472843/100000000000000 : ℝ), (1965202862321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709726691/5000000000 : ℝ)|^8329 ≤ (44382144619611/100000000000000 : ℝ)^6281
        have hw : |(2709726691/5000000000 : ℝ)|=(2709726691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156281623/312500000 : ℝ)|^8329 ≤ (39896232472843/100000000000000 : ℝ)^6281
        have hw : |(156281623/312500000 : ℝ)|=(156281623/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1238907613/5000000000 : ℝ)|^8329 ≤ (1965202862321/12500000000000 : ℝ)^6281
        have hw : |(-1238907613/5000000000 : ℝ)|=(1238907613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_3 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4317947391/10000000000 : ℝ)*x 0 + (1837959219/5000000000 : ℝ)*x 1 + (5071075241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317947391/10000000000 : ℝ)^8329 ≤ (32836350523473/100000000000000 : ℝ)^6281 := by
    have hnat : (4317947391 : ℕ)^8329*100000000000000^6281 ≤ 32836350523473^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317947391 10000000000 32836350523473 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837959219/5000000000 : ℝ)^8329 ≤ (26524540861283/100000000000000 : ℝ)^6281 := by
    have hnat : (1837959219 : ℕ)^8329*100000000000000^6281 ≤ 26524540861283^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837959219 5000000000 26524540861283 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5071075241/10000000000 : ℝ)^8329 ≤ (40639108599427/100000000000000 : ℝ)^6281 := by
    have hnat : (5071075241 : ℕ)^8329*100000000000000^6281 ≤ 40639108599427^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071075241 10000000000 40639108599427 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317947391/10000000000 : ℝ), (1837959219/5000000000 : ℝ), (5071075241/10000000000 : ℝ)] ![(32836350523473/100000000000000 : ℝ), (26524540861283/100000000000000 : ℝ), (40639108599427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317947391/10000000000 : ℝ)|^8329 ≤ (32836350523473/100000000000000 : ℝ)^6281
        have hw : |(4317947391/10000000000 : ℝ)|=(4317947391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837959219/5000000000 : ℝ)|^8329 ≤ (26524540861283/100000000000000 : ℝ)^6281
        have hw : |(1837959219/5000000000 : ℝ)|=(1837959219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5071075241/10000000000 : ℝ)|^8329 ≤ (40639108599427/100000000000000 : ℝ)^6281
        have hw : |(5071075241/10000000000 : ℝ)|=(5071075241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_4 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049812369/5000000000 : ℝ)*x 0 + (5010622371/10000000000 : ℝ)*x 1 + (1423327863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049812369/5000000000 : ℝ)^8329 ≤ (631084265253/5000000000000 : ℝ)^6281 := by
    have hnat : (1049812369 : ℕ)^8329*5000000000000^6281 ≤ 631084265253^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049812369 5000000000 631084265253 5000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010622371/10000000000 : ℝ)^8329 ≤ (19998965784401/50000000000000 : ℝ)^6281 := by
    have hnat : (5010622371 : ℕ)^8329*50000000000000^6281 ≤ 19998965784401^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010622371 10000000000 19998965784401 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1423327863/2500000000 : ℝ)^8329 ≤ (23690191556863/50000000000000 : ℝ)^6281 := by
    have hnat : (1423327863 : ℕ)^8329*50000000000000^6281 ≤ 23690191556863^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423327863 2500000000 23690191556863 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049812369/5000000000 : ℝ), (5010622371/10000000000 : ℝ), (1423327863/2500000000 : ℝ)] ![(631084265253/5000000000000 : ℝ), (19998965784401/50000000000000 : ℝ), (23690191556863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049812369/5000000000 : ℝ)|^8329 ≤ (631084265253/5000000000000 : ℝ)^6281
        have hw : |(-1049812369/5000000000 : ℝ)|=(1049812369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010622371/10000000000 : ℝ)|^8329 ≤ (19998965784401/50000000000000 : ℝ)^6281
        have hw : |(5010622371/10000000000 : ℝ)|=(5010622371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1423327863/2500000000 : ℝ)|^8329 ≤ (23690191556863/50000000000000 : ℝ)^6281
        have hw : |(1423327863/2500000000 : ℝ)|=(1423327863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_5 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239500913/10000000000 : ℝ)*x 0 + (-1785517347/10000000000 : ℝ)*x 1 + (2846655577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239500913/10000000000 : ℝ)^8329 ≤ (42438578227387/100000000000000 : ℝ)^6281 := by
    have hnat : (5239500913 : ℕ)^8329*100000000000000^6281 ≤ 42438578227387^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239500913 10000000000 42438578227387 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1785517347/10000000000 : ℝ)^8329 ≤ (10181041928199/100000000000000 : ℝ)^6281 := by
    have hnat : (1785517347 : ℕ)^8329*100000000000000^6281 ≤ 10181041928199^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785517347 10000000000 10181041928199 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2846655577/5000000000 : ℝ)^8329 ≤ (2961273739069/6250000000000 : ℝ)^6281 := by
    have hnat : (2846655577 : ℕ)^8329*6250000000000^6281 ≤ 2961273739069^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846655577 5000000000 2961273739069 6250000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239500913/10000000000 : ℝ), (-1785517347/10000000000 : ℝ), (2846655577/5000000000 : ℝ)] ![(42438578227387/100000000000000 : ℝ), (10181041928199/100000000000000 : ℝ), (2961273739069/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239500913/10000000000 : ℝ)|^8329 ≤ (42438578227387/100000000000000 : ℝ)^6281
        have hw : |(5239500913/10000000000 : ℝ)|=(5239500913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1785517347/10000000000 : ℝ)|^8329 ≤ (10181041928199/100000000000000 : ℝ)^6281
        have hw : |(-1785517347/10000000000 : ℝ)|=(1785517347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2846655577/5000000000 : ℝ)|^8329 ≤ (2961273739069/6250000000000 : ℝ)^6281
        have hw : |(2846655577/5000000000 : ℝ)|=(2846655577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_6 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239500967/10000000000 : ℝ)*x 0 + (5693311339/10000000000 : ℝ)*x 1 + (-1785517001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239500967/10000000000 : ℝ)^8329 ≤ (10609644701847/25000000000000 : ℝ)^6281 := by
    have hnat : (5239500967 : ℕ)^8329*25000000000000^6281 ≤ 10609644701847^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239500967 10000000000 10609644701847 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5693311339/10000000000 : ℝ)^8329 ≤ (23690190933349/50000000000000 : ℝ)^6281 := by
    have hnat : (5693311339 : ℕ)^8329*50000000000000^6281 ≤ 23690190933349^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693311339 10000000000 23690190933349 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1785517001/10000000000 : ℝ)^8329 ≤ (2036207862403/20000000000000 : ℝ)^6281 := by
    have hnat : (1785517001 : ℕ)^8329*20000000000000^6281 ≤ 2036207862403^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785517001 10000000000 2036207862403 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239500967/10000000000 : ℝ), (5693311339/10000000000 : ℝ), (-1785517001/10000000000 : ℝ)] ![(10609644701847/25000000000000 : ℝ), (23690190933349/50000000000000 : ℝ), (2036207862403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239500967/10000000000 : ℝ)|^8329 ≤ (10609644701847/25000000000000 : ℝ)^6281
        have hw : |(5239500967/10000000000 : ℝ)|=(5239500967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5693311339/10000000000 : ℝ)|^8329 ≤ (23690190933349/50000000000000 : ℝ)^6281
        have hw : |(5693311339/10000000000 : ℝ)|=(5693311339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1785517001/10000000000 : ℝ)|^8329 ≤ (2036207862403/20000000000000 : ℝ)^6281
        have hw : |(-1785517001/10000000000 : ℝ)|=(1785517001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s1_7 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319562969/10000000000 : ℝ)*x 0 + (2525991699/5000000000 : ℝ)*x 1 + (369538949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319562969/10000000000 : ℝ)^8329 ≤ (32852643334639/100000000000000 : ℝ)^6281 := by
    have hnat : (4319562969 : ℕ)^8329*100000000000000^6281 ≤ 32852643334639^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319562969 10000000000 32852643334639 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2525991699/5000000000 : ℝ)^8329 ≤ (40436345384259/100000000000000 : ℝ)^6281 := by
    have hnat : (2525991699 : ℕ)^8329*100000000000000^6281 ≤ 40436345384259^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525991699 5000000000 40436345384259 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369538949/1000000000 : ℝ)^8329 ≤ (13355505636173/50000000000000 : ℝ)^6281 := by
    have hnat : (369538949 : ℕ)^8329*50000000000000^6281 ≤ 13355505636173^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369538949 1000000000 13355505636173 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319562969/10000000000 : ℝ), (2525991699/5000000000 : ℝ), (369538949/1000000000 : ℝ)] ![(32852643334639/100000000000000 : ℝ), (40436345384259/100000000000000 : ℝ), (13355505636173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319562969/10000000000 : ℝ)|^8329 ≤ (32852643334639/100000000000000 : ℝ)^6281
        have hw : |(4319562969/10000000000 : ℝ)|=(4319562969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2525991699/5000000000 : ℝ)|^8329 ≤ (40436345384259/100000000000000 : ℝ)^6281
        have hw : |(2525991699/5000000000 : ℝ)|=(2525991699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(369538949/1000000000 : ℝ)|^8329 ≤ (13355505636173/50000000000000 : ℝ)^6281
        have hw : |(369538949/1000000000 : ℝ)|=(369538949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1136_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13919/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (351/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1279/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13919/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13919/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13919/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13919/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13919/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13919/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (389/100000 : ℝ) ^ (1041/256 : ℝ) ≤ (15840029863/100000000000000000000 : ℝ) := by
    have hpowers : (389/100000 : ℝ)^1041 ≤ (15840029863/100000000000000000000 : ℝ)^256 := by
      have hnat : (389 : ℕ)^1041*100000000000000000000^256 ≤ 15840029863^256*100000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        389 100000 15840029863 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (389/100000 : ℝ)) (X := (15840029863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13919/50000 : ℝ) ^ (1041/256 : ℝ) ≤ (275830712055695657/50000000000000000000 : ℝ) := by
    have hpowers : (13919/50000 : ℝ)^1041 ≤ (275830712055695657/50000000000000000000 : ℝ)^256 := by
      have hnat : (13919 : ℕ)^1041*50000000000000000000^256 ≤ 275830712055695657^256*50000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13919 50000 275830712055695657 50000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13919/50000 : ℝ)) (X := (275830712055695657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000015840029863/50000000000000000000 : ℝ) ≤ (2500000000194767/2500000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50000000015840029863/50000000000000000000 : ℝ)^256 ≤ (2500000000194767/2500000000000000 : ℝ)^1041 := by
      have hnat : (50000000015840029863 : ℕ)^256*2500000000000000^1041 ≤ 2500000000194767^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000015840029863 50000000000000000000 2500000000194767 2500000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000194767/2500000000000000 : ℝ)) (X := (50000000015840029863/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100551661439951421177/100000000000000000000 : ℝ) ≤ (10013538186844613/10000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (100551661439951421177/100000000000000000000 : ℝ)^256 ≤ (10013538186844613/10000000000000000 : ℝ)^1041 := by
      have hnat : (100551661439951421177 : ℕ)^256*10000000000000000^1041 ≤ 10013538186844613^1041*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100551661439951421177 100000000000000000000 10013538186844613 10000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013538186844613/10000000000000000 : ℝ)) (X := (100551661439951421177/100000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25275830712055695657/25000000000000000000 : ℝ) ≤ (5013538186455079/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (25275830712055695657/25000000000000000000 : ℝ)^256 ≤ (5013538186455079/5000000000000000 : ℝ)^1041 := by
      have hnat : (25275830712055695657 : ℕ)^256*5000000000000000^1041 ≤ 5013538186455079^1041*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25275830712055695657 25000000000000000000 5013538186455079 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013538186455079/5000000000000000 : ℝ)) (X := (25275830712055695657/25000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15840029863/100000000000000000000 : ℝ) ≤ ((137239733656312821761/137245000000000000000 : ℝ)+2*(2707637213109/548980000000000 : ℝ)*(389/100000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (137239733656312821761/137245000000000000000 : ℝ)+2*(2707637213109/548980000000000 : ℝ)*(389/100000 : ℝ)=(2500000000194767/2500000000000000 : ℝ) by norm_num, show 1+2*(15840029863/100000000000000000000 : ℝ)=(50000000015840029863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(275830712055695657/50000000000000000000 : ℝ)+(15840029863/100000000000000000000 : ℝ) ≤ ((137239733656312821761/137245000000000000000 : ℝ)+(2707637213109/548980000000000 : ℝ)*((13919/50000 : ℝ)+(389/100000 : ℝ)))^(1041/256 : ℝ) := by
    rw [show (137239733656312821761/137245000000000000000 : ℝ)+(2707637213109/548980000000000 : ℝ)*((13919/50000 : ℝ)+(389/100000 : ℝ))=(10013538186844613/10000000000000000 : ℝ) by norm_num, show 1+(275830712055695657/50000000000000000000 : ℝ)+(15840029863/100000000000000000000 : ℝ)=(100551661439951421177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(275830712055695657/50000000000000000000 : ℝ) ≤ ((137239733656312821761/137245000000000000000 : ℝ)+2*(2707637213109/548980000000000 : ℝ)*(13919/50000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (137239733656312821761/137245000000000000000 : ℝ)+2*(2707637213109/548980000000000 : ℝ)*(13919/50000 : ℝ)=(5013538186455079/5000000000000000 : ℝ) by norm_num, show 1+2*(275830712055695657/50000000000000000000 : ℝ)=(25275830712055695657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137239733656312821761/137245000000000000000 : ℝ)*(X 1 0+X 2 0)+(2707637213109/548980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (389/100000 : ℝ)) (hi := (13919/50000 : ℝ)) (c := (137239733656312821761/137245000000000000000 : ℝ)) (alpha := (2707637213109/548980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137239733656312821761/137245000000000000000 : ℝ)*(X 0 1+X 2 1)+(2707637213109/548980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (389/100000 : ℝ)) (hi := (13919/50000 : ℝ)) (c := (137239733656312821761/137245000000000000000 : ℝ)) (alpha := (2707637213109/548980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137239733656312821761/137245000000000000000 : ℝ)*(X 0 2+X 1 2)+(2707637213109/548980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (389/100000 : ℝ)) (hi := (13919/50000 : ℝ)) (c := (137239733656312821761/137245000000000000000 : ℝ)) (alpha := (2707637213109/548980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-262351241/1250000000 : ℝ)*X 0 0+(5703110633/10000000000 : ℝ)*X 0 1+(5001014141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709725773/5000000000 : ℝ)*X 1 0+(-495563107/2000000000 : ℝ)*X 1 1+(2500506787/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709726691/5000000000 : ℝ)*X 2 0+(156281623/312500000 : ℝ)*X 2 1+(-1238907613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317947391/10000000000 : ℝ)*X 0 0+(1837959219/5000000000 : ℝ)*X 0 1+(5071075241/10000000000 : ℝ)*X 0 2+(4317947391/10000000000 : ℝ)*X 1 0+(1837959219/5000000000 : ℝ)*X 1 1+(5071075241/10000000000 : ℝ)*X 1 2+(4317947391/10000000000 : ℝ)*X 2 0+(1837959219/5000000000 : ℝ)*X 2 1+(5071075241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1049812369/5000000000 : ℝ)*X 0 0+(5010622371/10000000000 : ℝ)*X 0 1+(1423327863/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239500913/10000000000 : ℝ)*X 1 0+(-1785517347/10000000000 : ℝ)*X 1 1+(2846655577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239500967/10000000000 : ℝ)*X 2 0+(5693311339/10000000000 : ℝ)*X 2 1+(-1785517001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319562969/10000000000 : ℝ)*X 0 0+(2525991699/5000000000 : ℝ)*X 0 1+(369538949/1000000000 : ℝ)*X 0 2+(4319562969/10000000000 : ℝ)*X 1 0+(2525991699/5000000000 : ℝ)*X 1 1+(369538949/1000000000 : ℝ)*X 1 2+(4319562969/10000000000 : ℝ)*X 2 0+(2525991699/5000000000 : ℝ)*X 2 1+(369538949/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (702305516156697587660617827/137245000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58037131/12500000000000 : ℝ)*(base1) + (721650271/100000000000000 : ℝ)*(base19) + (1260530727/100000000000000 : ℝ)*(base23) + (56904513/100000000000000 : ℝ)*(upper3) + (27287681/100000000000000 : ℝ)*(upper5) + (21410728388277/2000000000000 : ℝ)*(major0) + (21410728388277/2000000000000 : ℝ)*(major1) + (21410728388277/2000000000000 : ℝ)*(major2) + (284861286816939/20000000000000 : ℝ)*(sp0) + (22254767446869/1562500000000 : ℝ)*(sp1) + (712153137453967/50000000000000 : ℝ)*(sp2) + (358382334259883/50000000000000 : ℝ)*(sp3) + (782825507/50000000000000 : ℝ)*(sp4) + (848594387/50000000000000 : ℝ)*(sp5) + (358382566408407/50000000000000 : ℝ)*(f.failure) + (1424307535438661/100000000000000 : ℝ)*(f.sum) + (8872889644891/6862250000000000000000000000 : ℝ)*base65 + (2916341144361015797/274490000000000000000000000000000 : ℝ)*base67 + (1071643096769935797/274490000000000000000000000000000 : ℝ)*base69 + (937145858328185797/274490000000000000000000000000000 : ℝ)*base71 + (892134685947/171556250000000000000000000 : ℝ)*base73 + (1656666802208005797/274490000000000000000000000000000 : ℝ)*base75 + (2431915247731085797/274490000000000000000000000000000 : ℝ)*base77 + (2468701728324465797/274490000000000000000000000000000 : ℝ)*base79 + (7988632580159/3431125000000000000000000000 : ℝ)*base81 + (16504911/2500000000000000000000 : ℝ)*base90 + (16504911/2500000000000000000000 : ℝ)*base92 + (16504911/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19918317967216394027937401121/6862250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43242067/100000000000000 : ℝ)*(base1) + (664919189/100000000000000 : ℝ)*(base19) + (175816371/25000000000000 : ℝ)*(base23) + (50731349/100000000000000 : ℝ)*(upper3) + (61008577/100000000000000 : ℝ)*(upper5) + (1100968111839413/100000000000000 : ℝ)*(major0) + (1100968111839413/100000000000000 : ℝ)*(major1) + (1100968111839413/100000000000000 : ℝ)*(major2) + (2417438541/100000000000000 : ℝ)*(sp1) + (1547175981/50000000000000 : ℝ)*(sp2) + (1464795853781609/100000000000000 : ℝ)*(sp4) + (366198182045453/25000000000000 : ℝ)*(sp5) + (91549500807631/6250000000000 : ℝ)*(sp6) + (368570136572057/50000000000000 : ℝ)*(sp7) + (36857015819309/5000000000000 : ℝ)*(f.failure) + (732397905269771/50000000000000 : ℝ)*(f.sum) + (14191514272759/27449000000000000000000000000 : ℝ)*base66 + (12734872426941383707/13724500000000000000000000000000000 : ℝ)*base68 + (142927667961642116293/13724500000000000000000000000000000 : ℝ)*base69 + (9579121036182116293/13724500000000000000000000000000000 : ℝ)*base71 + (5330781134583/1372450000000000000000000000 : ℝ)*base74 + (57498140952149116293/13724500000000000000000000000000000 : ℝ)*base75 + (2230448530180883707/13724500000000000000000000000000000 : ℝ)*base78 + (58307393660252116293/13724500000000000000000000000000000 : ℝ)*base79 + (121435001336969/27449000000000000000000000000 : ℝ)*base81 + (2083957/250000000000000000000 : ℝ)*base90 + (2083957/250000000000000000000 : ℝ)*base92 + (2083957/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1136_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13919/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1279/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1136_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1136_s2_0 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-538091863/2500000000 : ℝ)*x 0 + (5511946209/10000000000 : ℝ)*x 1 + (322383007/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538091863/2500000000 : ℝ)^8329 ≤ (13043835774401/100000000000000 : ℝ)^6281 := by
    have hnat : (538091863 : ℕ)^8329*100000000000000^6281 ≤ 13043835774401^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538091863 2500000000 13043835774401 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511946209/10000000000 : ℝ)^8329 ≤ (45389370900109/100000000000000 : ℝ)^6281 := by
    have hnat : (5511946209 : ℕ)^8329*100000000000000^6281 ≤ 45389370900109^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511946209 10000000000 45389370900109 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322383007/625000000 : ℝ)^8329 ≤ (8313358663197/20000000000000 : ℝ)^6281 := by
    have hnat : (322383007 : ℕ)^8329*20000000000000^6281 ≤ 8313358663197^6281*625000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322383007 625000000 8313358663197 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538091863/2500000000 : ℝ), (5511946209/10000000000 : ℝ), (322383007/625000000 : ℝ)] ![(13043835774401/100000000000000 : ℝ), (45389370900109/100000000000000 : ℝ), (8313358663197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538091863/2500000000 : ℝ)|^8329 ≤ (13043835774401/100000000000000 : ℝ)^6281
        have hw : |(-538091863/2500000000 : ℝ)|=(538091863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511946209/10000000000 : ℝ)|^8329 ≤ (45389370900109/100000000000000 : ℝ)^6281
        have hw : |(5511946209/10000000000 : ℝ)|=(5511946209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322383007/625000000 : ℝ)|^8329 ≤ (8313358663197/20000000000000 : ℝ)^6281
        have hw : |(322383007/625000000 : ℝ)|=(322383007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_1 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374120133/10000000000 : ℝ)*x 0 + (-584090149/2500000000 : ℝ)*x 1 + (515812999/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374120133/10000000000 : ℝ)^8329 ≤ (8778102573261/20000000000000 : ℝ)^6281 := by
    have hnat : (5374120133 : ℕ)^8329*20000000000000^6281 ≤ 8778102573261^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374120133 10000000000 8778102573261 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584090149/2500000000 : ℝ)^8329 ≤ (14542673735423/100000000000000 : ℝ)^6281 := by
    have hnat : (584090149 : ℕ)^8329*100000000000000^6281 ≤ 14542673735423^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584090149 2500000000 14542673735423 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515812999/1000000000 : ℝ)^8329 ≤ (41566813384447/100000000000000 : ℝ)^6281 := by
    have hnat : (515812999 : ℕ)^8329*100000000000000^6281 ≤ 41566813384447^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515812999 1000000000 41566813384447 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374120133/10000000000 : ℝ), (-584090149/2500000000 : ℝ), (515812999/1000000000 : ℝ)] ![(8778102573261/20000000000000 : ℝ), (14542673735423/100000000000000 : ℝ), (41566813384447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374120133/10000000000 : ℝ)|^8329 ≤ (8778102573261/20000000000000 : ℝ)^6281
        have hw : |(5374120133/10000000000 : ℝ)|=(5374120133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-584090149/2500000000 : ℝ)|^8329 ≤ (14542673735423/100000000000000 : ℝ)^6281
        have hw : |(-584090149/2500000000 : ℝ)|=(584090149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515812999/1000000000 : ℝ)|^8329 ≤ (41566813384447/100000000000000 : ℝ)^6281
        have hw : |(515812999/1000000000 : ℝ)|=(515812999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_2 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343530021/2500000000 : ℝ)*x 0 + (322383121/625000000 : ℝ)*x 1 + (-233636073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343530021/2500000000 : ℝ)^8329 ≤ (10972628083909/25000000000000 : ℝ)^6281 := by
    have hnat : (1343530021 : ℕ)^8329*25000000000000^6281 ≤ 10972628083909^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343530021 2500000000 10972628083909 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322383121/625000000 : ℝ)^8329 ≤ (20783406403699/50000000000000 : ℝ)^6281 := by
    have hnat : (322383121 : ℕ)^8329*50000000000000^6281 ≤ 20783406403699^6281*625000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322383121 625000000 20783406403699 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233636073/1000000000 : ℝ)^8329 ≤ (14542674841469/100000000000000 : ℝ)^6281 := by
    have hnat : (233636073 : ℕ)^8329*100000000000000^6281 ≤ 14542674841469^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233636073 1000000000 14542674841469 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343530021/2500000000 : ℝ), (322383121/625000000 : ℝ), (-233636073/1000000000 : ℝ)] ![(10972628083909/25000000000000 : ℝ), (20783406403699/50000000000000 : ℝ), (14542674841469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343530021/2500000000 : ℝ)|^8329 ≤ (10972628083909/25000000000000 : ℝ)^6281
        have hw : |(1343530021/2500000000 : ℝ)|=(1343530021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322383121/625000000 : ℝ)|^8329 ≤ (20783406403699/50000000000000 : ℝ)^6281
        have hw : |(322383121/625000000 : ℝ)|=(322383121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233636073/1000000000 : ℝ)|^8329 ≤ (14542674841469/100000000000000 : ℝ)^6281
        have hw : |(-233636073/1000000000 : ℝ)|=(233636073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_3 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354673341/10000000000 : ℝ)*x 0 + (2008607507/5000000000 : ℝ)*x 1 + (590036769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354673341/10000000000 : ℝ)^8329 ≤ (830180376277/2500000000000 : ℝ)^6281 := by
    have hnat : (4354673341 : ℕ)^8329*2500000000000^6281 ≤ 830180376277^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354673341 10000000000 830180376277 2500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008607507/5000000000 : ℝ)^8329 ≤ (5967738748647/20000000000000 : ℝ)^6281 := by
    have hnat : (2008607507 : ℕ)^8329*20000000000000^6281 ≤ 5967738748647^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008607507 5000000000 5967738748647 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590036769/1250000000 : ℝ)^8329 ≤ (36954091194101/100000000000000 : ℝ)^6281 := by
    have hnat : (590036769 : ℕ)^8329*100000000000000^6281 ≤ 36954091194101^6281*1250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590036769 1250000000 36954091194101 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354673341/10000000000 : ℝ), (2008607507/5000000000 : ℝ), (590036769/1250000000 : ℝ)] ![(830180376277/2500000000000 : ℝ), (5967738748647/20000000000000 : ℝ), (36954091194101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354673341/10000000000 : ℝ)|^8329 ≤ (830180376277/2500000000000 : ℝ)^6281
        have hw : |(4354673341/10000000000 : ℝ)|=(4354673341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008607507/5000000000 : ℝ)|^8329 ≤ (5967738748647/20000000000000 : ℝ)^6281
        have hw : |(2008607507/5000000000 : ℝ)|=(2008607507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590036769/1250000000 : ℝ)|^8329 ≤ (36954091194101/100000000000000 : ℝ)^6281
        have hw : |(590036769/1250000000 : ℝ)|=(590036769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_4 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152471751/10000000000 : ℝ)*x 0 + (5160578243/10000000000 : ℝ)*x 1 + (2754735693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152471751/10000000000 : ℝ)^8329 ≤ (6522336976483/50000000000000 : ℝ)^6281 := by
    have hnat : (2152471751 : ℕ)^8329*50000000000000^6281 ≤ 6522336976483^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152471751 10000000000 6522336976483 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5160578243/10000000000 : ℝ)^8329 ≤ (20796488820967/50000000000000 : ℝ)^6281 := by
    have hnat : (5160578243 : ℕ)^8329*50000000000000^6281 ≤ 20796488820967^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160578243 10000000000 20796488820967 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754735693/5000000000 : ℝ)^8329 ≤ (2835146774677/6250000000000 : ℝ)^6281 := by
    have hnat : (2754735693 : ℕ)^8329*6250000000000^6281 ≤ 2835146774677^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754735693 5000000000 2835146774677 6250000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152471751/10000000000 : ℝ), (5160578243/10000000000 : ℝ), (2754735693/5000000000 : ℝ)] ![(6522336976483/50000000000000 : ℝ), (20796488820967/50000000000000 : ℝ), (2835146774677/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152471751/10000000000 : ℝ)|^8329 ≤ (6522336976483/50000000000000 : ℝ)^6281
        have hw : |(-2152471751/10000000000 : ℝ)|=(2152471751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5160578243/10000000000 : ℝ)|^8329 ≤ (20796488820967/50000000000000 : ℝ)^6281
        have hw : |(5160578243/10000000000 : ℝ)|=(5160578243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754735693/5000000000 : ℝ)|^8329 ≤ (2835146774677/6250000000000 : ℝ)^6281
        have hw : |(2754735693/5000000000 : ℝ)|=(2754735693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_5 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056876641/2000000000 : ℝ)*x 0 + (-992508639/5000000000 : ℝ)*x 1 + (5509472009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056876641/2000000000 : ℝ)^8329 ≤ (42921320054853/100000000000000 : ℝ)^6281 := by
    have hnat : (1056876641 : ℕ)^8329*100000000000000^6281 ≤ 42921320054853^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056876641 2000000000 42921320054853 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992508639/5000000000 : ℝ)^8329 ≤ (5858162361301/50000000000000 : ℝ)^6281 := by
    have hnat : (992508639 : ℕ)^8329*50000000000000^6281 ≤ 5858162361301^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992508639 5000000000 5858162361301 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5509472009/10000000000 : ℝ)^8329 ≤ (45362355196849/100000000000000 : ℝ)^6281 := by
    have hnat : (5509472009 : ℕ)^8329*100000000000000^6281 ≤ 45362355196849^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509472009 10000000000 45362355196849 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056876641/2000000000 : ℝ), (-992508639/5000000000 : ℝ), (5509472009/10000000000 : ℝ)] ![(42921320054853/100000000000000 : ℝ), (5858162361301/50000000000000 : ℝ), (45362355196849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056876641/2000000000 : ℝ)|^8329 ≤ (42921320054853/100000000000000 : ℝ)^6281
        have hw : |(1056876641/2000000000 : ℝ)|=(1056876641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992508639/5000000000 : ℝ)|^8329 ≤ (5858162361301/50000000000000 : ℝ)^6281
        have hw : |(-992508639/5000000000 : ℝ)|=(992508639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5509472009/10000000000 : ℝ)|^8329 ≤ (45362355196849/100000000000000 : ℝ)^6281
        have hw : |(5509472009/10000000000 : ℝ)|=(5509472009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_6 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284381809/10000000000 : ℝ)*x 0 + (5509471837/10000000000 : ℝ)*x 1 + (-1985019441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284381809/10000000000 : ℝ)^8329 ≤ (8584261003799/20000000000000 : ℝ)^6281 := by
    have hnat : (5284381809 : ℕ)^8329*20000000000000^6281 ≤ 8584261003799^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284381809 10000000000 8584261003799 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509471837/10000000000 : ℝ)^8329 ≤ (1814494132757/4000000000000 : ℝ)^6281 := by
    have hnat : (5509471837 : ℕ)^8329*4000000000000^6281 ≤ 1814494132757^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509471837 10000000000 1814494132757 4000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985019441/10000000000 : ℝ)^8329 ≤ (2929085413061/25000000000000 : ℝ)^6281 := by
    have hnat : (1985019441 : ℕ)^8329*25000000000000^6281 ≤ 2929085413061^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985019441 10000000000 2929085413061 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284381809/10000000000 : ℝ), (5509471837/10000000000 : ℝ), (-1985019441/10000000000 : ℝ)] ![(8584261003799/20000000000000 : ℝ), (1814494132757/4000000000000 : ℝ), (2929085413061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284381809/10000000000 : ℝ)|^8329 ≤ (8584261003799/20000000000000 : ℝ)^6281
        have hw : |(5284381809/10000000000 : ℝ)|=(5284381809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509471837/10000000000 : ℝ)|^8329 ≤ (1814494132757/4000000000000 : ℝ)^6281
        have hw : |(5509471837/10000000000 : ℝ)|=(5509471837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1985019441/10000000000 : ℝ)|^8329 ≤ (2929085413061/25000000000000 : ℝ)^6281
        have hw : |(-1985019441/10000000000 : ℝ)|=(1985019441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s2_7 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354879889/10000000000 : ℝ)*x 0 + (4715427/10000000 : ℝ)*x 1 + (4022131073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354879889/10000000000 : ℝ)^8329 ≤ (16604651849633/50000000000000 : ℝ)^6281 := by
    have hnat : (4354879889 : ℕ)^8329*50000000000000^6281 ≤ 16604651849633^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354879889 10000000000 16604651849633 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4715427/10000000 : ℝ)^8329 ≤ (36903571651299/100000000000000 : ℝ)^6281 := by
    have hnat : (4715427 : ℕ)^8329*100000000000000^6281 ≤ 36903571651299^6281*10000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715427 10000000 36903571651299 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022131073/10000000000 : ℝ)^8329 ≤ (3735890579827/12500000000000 : ℝ)^6281 := by
    have hnat : (4022131073 : ℕ)^8329*12500000000000^6281 ≤ 3735890579827^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022131073 10000000000 3735890579827 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354879889/10000000000 : ℝ), (4715427/10000000 : ℝ), (4022131073/10000000000 : ℝ)] ![(16604651849633/50000000000000 : ℝ), (36903571651299/100000000000000 : ℝ), (3735890579827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354879889/10000000000 : ℝ)|^8329 ≤ (16604651849633/50000000000000 : ℝ)^6281
        have hw : |(4354879889/10000000000 : ℝ)|=(4354879889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4715427/10000000 : ℝ)|^8329 ≤ (36903571651299/100000000000000 : ℝ)^6281
        have hw : |(4715427/10000000 : ℝ)|=(4715427/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022131073/10000000000 : ℝ)|^8329 ≤ (3735890579827/12500000000000 : ℝ)^6281
        have hw : |(4022131073/10000000000 : ℝ)|=(4022131073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1136_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1279/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9043/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (413/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1279/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1279/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1279/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1279/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1279/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1279/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/6250 : ℝ) ^ (1041/256 : ℝ) ≤ (821603990200283/100000000000000000000 : ℝ) := by
    have hpowers : (351/6250 : ℝ)^1041 ≤ (821603990200283/100000000000000000000 : ℝ)^256 := by
      have hnat : (351 : ℕ)^1041*100000000000000000000^256 ≤ 821603990200283^256*6250^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 6250 821603990200283 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/6250 : ℝ)) (X := (821603990200283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1279/6250 : ℝ) ^ (1041/256 : ℝ) ≤ (157836547716069719/100000000000000000000 : ℝ) := by
    have hpowers : (1279/6250 : ℝ)^1041 ≤ (157836547716069719/100000000000000000000 : ℝ)^256 := by
      have hnat : (1279 : ℕ)^1041*100000000000000000000^256 ≤ 157836547716069719^256*6250^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1279 6250 157836547716069719 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1279/6250 : ℝ)) (X := (157836547716069719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000821603990200283/50000000000000000000 : ℝ) ≤ (10000040409090949/10000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50000821603990200283/50000000000000000000 : ℝ)^256 ≤ (10000040409090949/10000000000000000 : ℝ)^1041 := by
      have hnat : (50000821603990200283 : ℕ)^256*10000000000000000^1041 ≤ 10000040409090949^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000821603990200283 50000000000000000000 10000040409090949 10000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000040409090949/10000000000000000 : ℝ)) (X := (50000821603990200283/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50079329075853135001/50000000000000000000 : ℝ) ≤ (5001949673981481/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50079329075853135001/50000000000000000000 : ℝ)^256 ≤ (5001949673981481/5000000000000000 : ℝ)^1041 := by
      have hnat : (50079329075853135001 : ℕ)^256*5000000000000000^1041 ≤ 5001949673981481^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50079329075853135001 50000000000000000000 5001949673981481 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001949673981481/5000000000000000 : ℝ)) (X := (50079329075853135001/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50157836547716069719/50000000000000000000 : ℝ) ≤ (400310331473399/400000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50157836547716069719/50000000000000000000 : ℝ)^256 ≤ (400310331473399/400000000000000 : ℝ)^1041 := by
      have hnat : (50157836547716069719 : ℕ)^256*400000000000000^1041 ≤ 400310331473399^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50157836547716069719 50000000000000000000 400310331473399 400000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400310331473399/400000000000000 : ℝ)) (X := (50157836547716069719/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(821603990200283/100000000000000000000 : ℝ) ≤ ((4638664262274123773/4640000000000000000 : ℝ)+2*(3858938872013/1484800000000000 : ℝ)*(351/6250 : ℝ))^(1041/256 : ℝ) := by
    rw [show (4638664262274123773/4640000000000000000 : ℝ)+2*(3858938872013/1484800000000000 : ℝ)*(351/6250 : ℝ)=(10000040409090949/10000000000000000 : ℝ) by norm_num, show 1+2*(821603990200283/100000000000000000000 : ℝ)=(50000821603990200283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(157836547716069719/100000000000000000000 : ℝ)+(821603990200283/100000000000000000000 : ℝ) ≤ ((4638664262274123773/4640000000000000000 : ℝ)+(3858938872013/1484800000000000 : ℝ)*((1279/6250 : ℝ)+(351/6250 : ℝ)))^(1041/256 : ℝ) := by
    rw [show (4638664262274123773/4640000000000000000 : ℝ)+(3858938872013/1484800000000000 : ℝ)*((1279/6250 : ℝ)+(351/6250 : ℝ))=(5001949673981481/5000000000000000 : ℝ) by norm_num, show 1+(157836547716069719/100000000000000000000 : ℝ)+(821603990200283/100000000000000000000 : ℝ)=(50079329075853135001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(157836547716069719/100000000000000000000 : ℝ) ≤ ((4638664262274123773/4640000000000000000 : ℝ)+2*(3858938872013/1484800000000000 : ℝ)*(1279/6250 : ℝ))^(1041/256 : ℝ) := by
    rw [show (4638664262274123773/4640000000000000000 : ℝ)+2*(3858938872013/1484800000000000 : ℝ)*(1279/6250 : ℝ)=(400310331473399/400000000000000 : ℝ) by norm_num, show 1+2*(157836547716069719/100000000000000000000 : ℝ)=(50157836547716069719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4638664262274123773/4640000000000000000 : ℝ)*(X 1 0+X 2 0)+(3858938872013/1484800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (351/6250 : ℝ)) (hi := (1279/6250 : ℝ)) (c := (4638664262274123773/4640000000000000000 : ℝ)) (alpha := (3858938872013/1484800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4638664262274123773/4640000000000000000 : ℝ)*(X 0 1+X 2 1)+(3858938872013/1484800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (351/6250 : ℝ)) (hi := (1279/6250 : ℝ)) (c := (4638664262274123773/4640000000000000000 : ℝ)) (alpha := (3858938872013/1484800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4638664262274123773/4640000000000000000 : ℝ)*(X 0 2+X 1 2)+(3858938872013/1484800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (351/6250 : ℝ)) (hi := (1279/6250 : ℝ)) (c := (4638664262274123773/4640000000000000000 : ℝ)) (alpha := (3858938872013/1484800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-538091863/2500000000 : ℝ)*X 0 0+(5511946209/10000000000 : ℝ)*X 0 1+(322383007/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374120133/10000000000 : ℝ)*X 1 0+(-584090149/2500000000 : ℝ)*X 1 1+(515812999/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343530021/2500000000 : ℝ)*X 2 0+(322383121/625000000 : ℝ)*X 2 1+(-233636073/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354673341/10000000000 : ℝ)*X 0 0+(2008607507/5000000000 : ℝ)*X 0 1+(590036769/1250000000 : ℝ)*X 0 2+(4354673341/10000000000 : ℝ)*X 1 0+(2008607507/5000000000 : ℝ)*X 1 1+(590036769/1250000000 : ℝ)*X 1 2+(4354673341/10000000000 : ℝ)*X 2 0+(2008607507/5000000000 : ℝ)*X 2 1+(590036769/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2152471751/10000000000 : ℝ)*X 0 0+(5160578243/10000000000 : ℝ)*X 0 1+(2754735693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1056876641/2000000000 : ℝ)*X 1 0+(-992508639/5000000000 : ℝ)*X 1 1+(5509472009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284381809/10000000000 : ℝ)*X 2 0+(5509471837/10000000000 : ℝ)*X 2 1+(-1985019441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354879889/10000000000 : ℝ)*X 0 0+(4715427/10000000 : ℝ)*X 0 1+(4022131073/10000000000 : ℝ)*X 0 2+(4354879889/10000000000 : ℝ)*X 1 0+(4715427/10000000 : ℝ)*X 1 1+(4022131073/10000000000 : ℝ)*X 1 2+(4354879889/10000000000 : ℝ)*X 2 0+(4715427/10000000 : ℝ)*X 2 1+(4022131073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7008431455380230096082939/800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (438801539/50000000000000 : ℝ)*(base19) + (574366517/100000000000000 : ℝ)*(base23) + (13423479/100000000000000 : ℝ)*(upper2) + (302115953/100000000000000 : ℝ)*(upper3) + (10158583/6250000000000 : ℝ)*(upper4) + (212433943130287/10000000000000 : ℝ)*(major0) + (212433943130287/10000000000000 : ℝ)*(major1) + (212433943130287/10000000000000 : ℝ)*(major2) + (1413166679677663/50000000000000 : ℝ)*(sp0) + (1413175542277293/50000000000000 : ℝ)*(sp1) + (2826351387791147/100000000000000 : ℝ)*(sp2) + (711159687791267/50000000000000 : ℝ)*(sp3) + (18602802337/100000000000000 : ℝ)*(sp4) + (180821189/2500000000000 : ℝ)*(sp7) + (711163304215047/50000000000000 : ℝ)*(f.failure) + (88323498817427/3125000000000 : ℝ)*(f.sum) + (424972038719/256000000000000000000000000 : ℝ)*base65 + (3418817512922797/800000000000000000000000000000 : ℝ)*base67 + (813044999877203/800000000000000000000000000000 : ℝ)*base70 + (5490085183877203/800000000000000000000000000000 : ℝ)*base72 + (486315597119/256000000000000000000000000 : ℝ)*base73 + (5201589436677203/800000000000000000000000000000 : ℝ)*base76 + (5114098311877203/800000000000000000000000000000 : ℝ)*base78 + (2401233340677203/800000000000000000000000000000 : ℝ)*base80 + (522765623489/256000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8186369/2500000000000000000000 : ℝ)*base89 + (8186369/2500000000000000000000 : ℝ)*base91 + (8186369/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71904813867659970109941/14848000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44081863/6250000000000 : ℝ)*(base19) + (143068779/50000000000000 : ℝ)*(base23) + (77370101/25000000000000 : ℝ)*(upper2) + (40549243/50000000000000 : ℝ)*(upper3) + (53568241/50000000000000 : ℝ)*(upper5) + (430858813173437/20000000000000 : ℝ)*(major0) + (430858813173437/20000000000000 : ℝ)*(major1) + (430858813173437/20000000000000 : ℝ)*(major2) + (2794427337/100000000000000 : ℝ)*(sp0) + (729158147/5000000000000 : ℝ)*(sp1) + (286620279239207/10000000000000 : ℝ)*(sp4) + (1433095149173329/50000000000000 : ℝ)*(sp5) + (358275662585231/12500000000000 : ℝ)*(sp6) + (721191191745359/50000000000000 : ℝ)*(sp7) + (721191191745359/50000000000000 : ℝ)*(f.failure) + (1433102793409703/50000000000000 : ℝ)*(f.sum) + (27876790500697/14848000000000000000000000000 : ℝ)*base65 + (316102930205352037/46400000000000000000000000000000 : ℝ)*base68 + (321111937109352037/46400000000000000000000000000000 : ℝ)*base70 + (159803869886952037/46400000000000000000000000000000 : ℝ)*base72 + (43134648337753/14848000000000000000000000000 : ℝ)*base73 + (188315530119447963/46400000000000000000000000000000 : ℝ)*base75 + (54046625252247963/46400000000000000000000000000000 : ℝ)*base77 + (167279911943447963/46400000000000000000000000000000 : ℝ)*base79 + (6748048207527/14848000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4865607/2500000000000000000000 : ℝ)*base90 + (4865607/2500000000000000000000 : ℝ)*base92 + (4865607/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1136_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1279/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (413/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1136_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1136_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (413/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1136_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1136_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1136_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (413/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1136_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
