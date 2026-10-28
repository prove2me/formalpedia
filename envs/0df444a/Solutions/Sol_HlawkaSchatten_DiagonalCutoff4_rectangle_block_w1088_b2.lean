-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1088_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:55:16.546082+00:00
-- url     : https://prove2.me/submissions/17c4452e-7882-4dea-bc00-c775991a9aa7

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
theorem support_rectangle_w1088_s6_0 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096469397/5000000000 : ℝ)*x 0 + (5394470177/10000000000 : ℝ)*x 1 + (1052875757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096469397/5000000000 : ℝ)^8281 ≤ (13320028046989/100000000000000 : ℝ)^6233 := by
    have hnat : (1096469397 : ℕ)^8281*100000000000000^6233 ≤ 13320028046989^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096469397 5000000000 13320028046989 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394470177/10000000000 : ℝ)^8281 ≤ (22021364201167/50000000000000 : ℝ)^6233 := by
    have hnat : (5394470177 : ℕ)^8281*50000000000000^6233 ≤ 22021364201167^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394470177 10000000000 22021364201167 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052875757/2000000000 : ℝ)^8281 ≤ (21318621768921/50000000000000 : ℝ)^6233 := by
    have hnat : (1052875757 : ℕ)^8281*50000000000000^6233 ≤ 21318621768921^6233*2000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052875757 2000000000 21318621768921 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096469397/5000000000 : ℝ), (5394470177/10000000000 : ℝ), (1052875757/2000000000 : ℝ)] ![(13320028046989/100000000000000 : ℝ), (22021364201167/50000000000000 : ℝ), (21318621768921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096469397/5000000000 : ℝ)|^8281 ≤ (13320028046989/100000000000000 : ℝ)^6233
        have hw : |(-1096469397/5000000000 : ℝ)|=(1096469397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394470177/10000000000 : ℝ)|^8281 ≤ (22021364201167/50000000000000 : ℝ)^6233
        have hw : |(5394470177/10000000000 : ℝ)|=(5394470177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052875757/2000000000 : ℝ)|^8281 ≤ (21318621768921/50000000000000 : ℝ)^6233
        have hw : |(1052875757/2000000000 : ℝ)|=(1052875757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_1 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345048551/10000000000 : ℝ)*x 0 + (-1129472159/5000000000 : ℝ)*x 1 + (1052875757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345048551/10000000000 : ℝ)^8281 ≤ (4350745877473/10000000000000 : ℝ)^6233 := by
    have hnat : (5345048551 : ℕ)^8281*10000000000000^6233 ≤ 4350745877473^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345048551 10000000000 4350745877473 10000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129472159/5000000000 : ℝ)^8281 ≤ (1731912208847/12500000000000 : ℝ)^6233 := by
    have hnat : (1129472159 : ℕ)^8281*12500000000000^6233 ≤ 1731912208847^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129472159 5000000000 1731912208847 12500000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052875757/2000000000 : ℝ)^8281 ≤ (21318621768921/50000000000000 : ℝ)^6233 := by
    have hnat : (1052875757 : ℕ)^8281*50000000000000^6233 ≤ 21318621768921^6233*2000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052875757 2000000000 21318621768921 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345048551/10000000000 : ℝ), (-1129472159/5000000000 : ℝ), (1052875757/2000000000 : ℝ)] ![(4350745877473/10000000000000 : ℝ), (1731912208847/12500000000000 : ℝ), (21318621768921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345048551/10000000000 : ℝ)|^8281 ≤ (4350745877473/10000000000000 : ℝ)^6233
        have hw : |(5345048551/10000000000 : ℝ)|=(5345048551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129472159/5000000000 : ℝ)|^8281 ≤ (1731912208847/12500000000000 : ℝ)^6233
        have hw : |(-1129472159/5000000000 : ℝ)|=(1129472159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052875757/2000000000 : ℝ)|^8281 ≤ (21318621768921/50000000000000 : ℝ)^6233
        have hw : |(1052875757/2000000000 : ℝ)|=(1052875757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_2 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345048551/10000000000 : ℝ)*x 0 + (1052875757/2000000000 : ℝ)*x 1 + (-1129472159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345048551/10000000000 : ℝ)^8281 ≤ (4350745877473/10000000000000 : ℝ)^6233 := by
    have hnat : (5345048551 : ℕ)^8281*10000000000000^6233 ≤ 4350745877473^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345048551 10000000000 4350745877473 10000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052875757/2000000000 : ℝ)^8281 ≤ (21318621768921/50000000000000 : ℝ)^6233 := by
    have hnat : (1052875757 : ℕ)^8281*50000000000000^6233 ≤ 21318621768921^6233*2000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052875757 2000000000 21318621768921 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129472159/5000000000 : ℝ)^8281 ≤ (1731912208847/12500000000000 : ℝ)^6233 := by
    have hnat : (1129472159 : ℕ)^8281*12500000000000^6233 ≤ 1731912208847^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129472159 5000000000 1731912208847 12500000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345048551/10000000000 : ℝ), (1052875757/2000000000 : ℝ), (-1129472159/5000000000 : ℝ)] ![(4350745877473/10000000000000 : ℝ), (21318621768921/50000000000000 : ℝ), (1731912208847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345048551/10000000000 : ℝ)|^8281 ≤ (4350745877473/10000000000000 : ℝ)^6233
        have hw : |(5345048551/10000000000 : ℝ)|=(5345048551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052875757/2000000000 : ℝ)|^8281 ≤ (21318621768921/50000000000000 : ℝ)^6233
        have hw : |(1052875757/2000000000 : ℝ)|=(1052875757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129472159/5000000000 : ℝ)|^8281 ≤ (1731912208847/12500000000000 : ℝ)^6233
        have hw : |(-1129472159/5000000000 : ℝ)|=(1129472159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_3 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109307823/250000000 : ℝ)*x 0 + (2123082379/5000000000 : ℝ)*x 1 + (4502239779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109307823/250000000 : ℝ)^8281 ≤ (33316424757073/100000000000000 : ℝ)^6233 := by
    have hnat : (109307823 : ℕ)^8281*100000000000000^6233 ≤ 33316424757073^6233*250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109307823 250000000 33316424757073 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123082379/5000000000 : ℝ)^8281 ≤ (1602272518711/5000000000000 : ℝ)^6233 := by
    have hnat : (2123082379 : ℕ)^8281*5000000000000^6233 ≤ 1602272518711^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123082379 5000000000 1602272518711 5000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502239779/10000000000 : ℝ)^8281 ≤ (1731906242763/5000000000000 : ℝ)^6233 := by
    have hnat : (4502239779 : ℕ)^8281*5000000000000^6233 ≤ 1731906242763^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502239779 10000000000 1731906242763 5000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109307823/250000000 : ℝ), (2123082379/5000000000 : ℝ), (4502239779/10000000000 : ℝ)] ![(33316424757073/100000000000000 : ℝ), (1602272518711/5000000000000 : ℝ), (1731906242763/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109307823/250000000 : ℝ)|^8281 ≤ (33316424757073/100000000000000 : ℝ)^6233
        have hw : |(109307823/250000000 : ℝ)|=(109307823/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123082379/5000000000 : ℝ)|^8281 ≤ (1602272518711/5000000000000 : ℝ)^6233
        have hw : |(2123082379/5000000000 : ℝ)|=(2123082379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502239779/10000000000 : ℝ)|^8281 ≤ (1731906242763/5000000000000 : ℝ)^6233
        have hw : |(4502239779/10000000000 : ℝ)|=(4502239779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_4 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192943969/10000000000 : ℝ)*x 0 + (658088411/1250000000 : ℝ)*x 1 + (5394140441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192943969/10000000000 : ℝ)^8281 ≤ (6660034904183/50000000000000 : ℝ)^6233 := by
    have hnat : (2192943969 : ℕ)^8281*50000000000000^6233 ≤ 6660034904183^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192943969 10000000000 6660034904183 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658088411/1250000000 : ℝ)^8281 ≤ (10660194597877/25000000000000 : ℝ)^6233 := by
    have hnat : (658088411 : ℕ)^8281*25000000000000^6233 ≤ 10660194597877^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658088411 1250000000 10660194597877 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394140441/10000000000 : ℝ)^8281 ≤ (4403915178003/10000000000000 : ℝ)^6233 := by
    have hnat : (5394140441 : ℕ)^8281*10000000000000^6233 ≤ 4403915178003^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394140441 10000000000 4403915178003 10000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192943969/10000000000 : ℝ), (658088411/1250000000 : ℝ), (5394140441/10000000000 : ℝ)] ![(6660034904183/50000000000000 : ℝ), (10660194597877/25000000000000 : ℝ), (4403915178003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192943969/10000000000 : ℝ)|^8281 ≤ (6660034904183/50000000000000 : ℝ)^6233
        have hw : |(-2192943969/10000000000 : ℝ)|=(2192943969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658088411/1250000000 : ℝ)|^8281 ≤ (10660194597877/25000000000000 : ℝ)^6233
        have hw : |(658088411/1250000000 : ℝ)|=(658088411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394140441/10000000000 : ℝ)|^8281 ≤ (4403915178003/10000000000000 : ℝ)^6233
        have hw : |(5394140441/10000000000 : ℝ)|=(5394140441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_5 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312224423/10000000000 : ℝ)*x 0 + (-266147827/1250000000 : ℝ)*x 1 + (2697070217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312224423/10000000000 : ℝ)^8281 ≤ (43152847992339/100000000000000 : ℝ)^6233 := by
    have hnat : (5312224423 : ℕ)^8281*100000000000000^6233 ≤ 43152847992339^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312224423 10000000000 43152847992339 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266147827/1250000000 : ℝ)^8281 ≤ (3202000071771/25000000000000 : ℝ)^6233 := by
    have hnat : (266147827 : ℕ)^8281*25000000000000^6233 ≤ 3202000071771^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266147827 1250000000 3202000071771 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697070217/5000000000 : ℝ)^8281 ≤ (44039151704103/100000000000000 : ℝ)^6233 := by
    have hnat : (2697070217 : ℕ)^8281*100000000000000^6233 ≤ 44039151704103^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697070217 5000000000 44039151704103 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312224423/10000000000 : ℝ), (-266147827/1250000000 : ℝ), (2697070217/5000000000 : ℝ)] ![(43152847992339/100000000000000 : ℝ), (3202000071771/25000000000000 : ℝ), (44039151704103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312224423/10000000000 : ℝ)|^8281 ≤ (43152847992339/100000000000000 : ℝ)^6233
        have hw : |(5312224423/10000000000 : ℝ)|=(5312224423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266147827/1250000000 : ℝ)|^8281 ≤ (3202000071771/25000000000000 : ℝ)^6233
        have hw : |(-266147827/1250000000 : ℝ)|=(266147827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697070217/5000000000 : ℝ)|^8281 ≤ (44039151704103/100000000000000 : ℝ)^6233
        have hw : |(2697070217/5000000000 : ℝ)|=(2697070217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_6 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664028051/1250000000 : ℝ)*x 0 + (5394140433/10000000000 : ℝ)*x 1 + (-1064591319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664028051/1250000000 : ℝ)^8281 ≤ (43152847830453/100000000000000 : ℝ)^6233 := by
    have hnat : (664028051 : ℕ)^8281*100000000000000^6233 ≤ 43152847830453^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664028051 1250000000 43152847830453 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394140433/10000000000 : ℝ)^8281 ≤ (5504893961657/12500000000000 : ℝ)^6233 := by
    have hnat : (5394140433 : ℕ)^8281*12500000000000^6233 ≤ 5504893961657^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394140433 10000000000 5504893961657 12500000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064591319/5000000000 : ℝ)^8281 ≤ (12808000462907/100000000000000 : ℝ)^6233 := by
    have hnat : (1064591319 : ℕ)^8281*100000000000000^6233 ≤ 12808000462907^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064591319 5000000000 12808000462907 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664028051/1250000000 : ℝ), (5394140433/10000000000 : ℝ), (-1064591319/5000000000 : ℝ)] ![(43152847830453/100000000000000 : ℝ), (5504893961657/12500000000000 : ℝ), (12808000462907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664028051/1250000000 : ℝ)|^8281 ≤ (43152847830453/100000000000000 : ℝ)^6233
        have hw : |(664028051/1250000000 : ℝ)|=(664028051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394140433/10000000000 : ℝ)|^8281 ≤ (5504893961657/12500000000000 : ℝ)^6233
        have hw : |(5394140433/10000000000 : ℝ)|=(5394140433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064591319/5000000000 : ℝ)|^8281 ≤ (12808000462907/100000000000000 : ℝ)^6233
        have hw : |(-1064591319/5000000000 : ℝ)|=(1064591319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s6_7 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186161517/5000000000 : ℝ)*x 0 + (4501593063/10000000000 : ℝ)*x 1 + (2123406897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186161517/5000000000 : ℝ)^8281 ≤ (8329131786673/25000000000000 : ℝ)^6233 := by
    have hnat : (2186161517 : ℕ)^8281*25000000000000^6233 ≤ 8329131786673^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186161517 5000000000 8329131786673 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501593063/10000000000 : ℝ)^8281 ≤ (432893933159/1250000000000 : ℝ)^6233 := by
    have hnat : (4501593063 : ℕ)^8281*1250000000000^6233 ≤ 432893933159^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501593063 10000000000 432893933159 1250000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123406897/5000000000 : ℝ)^8281 ≤ (32051958184561/100000000000000 : ℝ)^6233 := by
    have hnat : (2123406897 : ℕ)^8281*100000000000000^6233 ≤ 32051958184561^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123406897 5000000000 32051958184561 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186161517/5000000000 : ℝ), (4501593063/10000000000 : ℝ), (2123406897/5000000000 : ℝ)] ![(8329131786673/25000000000000 : ℝ), (432893933159/1250000000000 : ℝ), (32051958184561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186161517/5000000000 : ℝ)|^8281 ≤ (8329131786673/25000000000000 : ℝ)^6233
        have hw : |(2186161517/5000000000 : ℝ)|=(2186161517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501593063/10000000000 : ℝ)|^8281 ≤ (432893933159/1250000000000 : ℝ)^6233
        have hw : |(4501593063/10000000000 : ℝ)|=(4501593063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123406897/5000000000 : ℝ)|^8281 ≤ (32051958184561/100000000000000 : ℝ)^6233
        have hw : |(2123406897/5000000000 : ℝ)|=(2123406897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1088_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1409/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11233/100000 : ℝ) ^ (1035/256 : ℝ) ≤ (14493858769754843/100000000000000000000 : ℝ) := by
    have hpowers : (11233/100000 : ℝ)^1035 ≤ (14493858769754843/100000000000000000000 : ℝ)^256 := by
      have hnat : (11233 : ℕ)^1035*100000000000000000000^256 ≤ 14493858769754843^256*100000^1035 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11233 100000 14493858769754843 100000000000000000000 1035 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11233/100000 : ℝ)) (X := (14493858769754843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14067/100000 : ℝ) ^ (1035/256 : ℝ) ≤ (35991938038061783/100000000000000000000 : ℝ) := by
    have hpowers : (14067/100000 : ℝ)^1035 ≤ (35991938038061783/100000000000000000000 : ℝ)^256 := by
      have hnat : (14067 : ℕ)^1035*100000000000000000000^256 ≤ 35991938038061783^256*100000^1035 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14067 100000 35991938038061783 100000000000000000000 1035 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14067/100000 : ℝ)) (X := (35991938038061783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014493858769754843/50000000000000000000 : ℝ) ≤ (625044807042833/625000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50014493858769754843/50000000000000000000 : ℝ)^256 ≤ (625044807042833/625000000000000 : ℝ)^1035 := by
      have hnat : (50014493858769754843 : ℕ)^256*625000000000000^1035 ≤ 625044807042833^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014493858769754843 50000000000000000000 625044807042833 625000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625044807042833/625000000000000 : ℝ)) (X := (50014493858769754843/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025242898403908313/50000000000000000000 : ℝ) ≤ (156269507713127/156250000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50025242898403908313/50000000000000000000 : ℝ)^256 ≤ (156269507713127/156250000000000 : ℝ)^1035 := by
      have hnat : (50025242898403908313 : ℕ)^256*156250000000000^1035 ≤ 156269507713127^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025242898403908313 50000000000000000000 156269507713127 156250000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156269507713127/156250000000000 : ℝ)) (X := (50025242898403908313/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035991938038061783/50000000000000000000 : ℝ) ≤ (625111254662183/625000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50035991938038061783/50000000000000000000 : ℝ)^256 ≤ (625111254662183/625000000000000 : ℝ)^1035 := by
      have hnat : (50035991938038061783 : ℕ)^256*625000000000000^1035 ≤ 625111254662183^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035991938038061783 50000000000000000000 625111254662183 625000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625111254662183/625000000000000 : ℝ)) (X := (50035991938038061783/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14493858769754843/100000000000000000000 : ℝ) ≤ ((442657644262807543/442812500000000000 : ℝ)+2*(1328952387/708500000000 : ℝ)*(11233/100000 : ℝ))^(1035/256 : ℝ) := by
    rw [show (442657644262807543/442812500000000000 : ℝ)+2*(1328952387/708500000000 : ℝ)*(11233/100000 : ℝ)=(625044807042833/625000000000000 : ℝ) by norm_num, show 1+2*(14493858769754843/100000000000000000000 : ℝ)=(50014493858769754843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35991938038061783/100000000000000000000 : ℝ)+(14493858769754843/100000000000000000000 : ℝ) ≤ ((442657644262807543/442812500000000000 : ℝ)+(1328952387/708500000000 : ℝ)*((14067/100000 : ℝ)+(11233/100000 : ℝ)))^(1035/256 : ℝ) := by
    rw [show (442657644262807543/442812500000000000 : ℝ)+(1328952387/708500000000 : ℝ)*((14067/100000 : ℝ)+(11233/100000 : ℝ))=(156269507713127/156250000000000 : ℝ) by norm_num, show 1+(35991938038061783/100000000000000000000 : ℝ)+(14493858769754843/100000000000000000000 : ℝ)=(50025242898403908313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35991938038061783/100000000000000000000 : ℝ) ≤ ((442657644262807543/442812500000000000 : ℝ)+2*(1328952387/708500000000 : ℝ)*(14067/100000 : ℝ))^(1035/256 : ℝ) := by
    rw [show (442657644262807543/442812500000000000 : ℝ)+2*(1328952387/708500000000 : ℝ)*(14067/100000 : ℝ)=(625111254662183/625000000000000 : ℝ) by norm_num, show 1+2*(35991938038061783/100000000000000000000 : ℝ)=(50035991938038061783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (442657644262807543/442812500000000000 : ℝ)*(X 1 0+X 2 0)+(1328952387/708500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (442657644262807543/442812500000000000 : ℝ)) (alpha := (1328952387/708500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (442657644262807543/442812500000000000 : ℝ)*(X 0 1+X 2 1)+(1328952387/708500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (442657644262807543/442812500000000000 : ℝ)) (alpha := (1328952387/708500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (442657644262807543/442812500000000000 : ℝ)*(X 0 2+X 1 2)+(1328952387/708500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (442657644262807543/442812500000000000 : ℝ)) (alpha := (1328952387/708500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1096469397/5000000000 : ℝ)*X 0 0+(5394470177/10000000000 : ℝ)*X 0 1+(1052875757/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345048551/10000000000 : ℝ)*X 1 0+(-1129472159/5000000000 : ℝ)*X 1 1+(1052875757/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345048551/10000000000 : ℝ)*X 2 0+(1052875757/2000000000 : ℝ)*X 2 1+(-1129472159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109307823/250000000 : ℝ)*X 0 0+(2123082379/5000000000 : ℝ)*X 0 1+(4502239779/10000000000 : ℝ)*X 0 2+(109307823/250000000 : ℝ)*X 1 0+(2123082379/5000000000 : ℝ)*X 1 1+(4502239779/10000000000 : ℝ)*X 1 2+(109307823/250000000 : ℝ)*X 2 0+(2123082379/5000000000 : ℝ)*X 2 1+(4502239779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2192943969/10000000000 : ℝ)*X 0 0+(658088411/1250000000 : ℝ)*X 0 1+(5394140441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312224423/10000000000 : ℝ)*X 1 0+(-266147827/1250000000 : ℝ)*X 1 1+(2697070217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664028051/1250000000 : ℝ)*X 2 0+(5394140433/10000000000 : ℝ)*X 2 1+(-1064591319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186161517/5000000000 : ℝ)*X 0 0+(4501593063/10000000000 : ℝ)*X 0 1+(2123406897/5000000000 : ℝ)*X 0 2+(2186161517/5000000000 : ℝ)*X 1 0+(4501593063/10000000000 : ℝ)*X 1 1+(2123406897/5000000000 : ℝ)*X 1 2+(2186161517/5000000000 : ℝ)*X 2 0+(4501593063/10000000000 : ℝ)*X 2 1+(2123406897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3377128262269327069137/1417000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481523739/100000000000000 : ℝ)*(base19) + (112095669/25000000000000 : ℝ)*(base23) + (885703/5000000000000 : ℝ)*(lower2) + (12208867/20000000000000 : ℝ)*(upper3) + (3638453/10000000000000 : ℝ)*(upper5) + (5796024581506793/100000000000000 : ℝ)*(major0) + (5796024581506793/100000000000000 : ℝ)*(major1) + (5796024581506793/100000000000000 : ℝ)*(major2) + (7686917173565121/100000000000000 : ℝ)*(sp0) + (7686929560794093/100000000000000 : ℝ)*(sp1) + (1921732398483789/25000000000000 : ℝ)*(sp2) + (1952555985146053/50000000000000 : ℝ)*(sp3) + (1608594089/12500000000000 : ℝ)*(sp4) + (7070960493/100000000000000 : ℝ)*(sp7) + (3905119041252599/100000000000000 : ℝ)*(f.failure) + (960866255289729/12500000000000 : ℝ)*(f.sum) + (54697040503/35425000000000000000000000 : ℝ)*base66 + (81867876560735401/44281250000000000000000000000000 : ℝ)*base68 + (29761297216733349/44281250000000000000000000000000 : ℝ)*base69 + (396020878997141651/44281250000000000000000000000000 : ℝ)*base72 + (4627444866721/1417000000000000000000000000 : ℝ)*base74 + (683456118429391651/44281250000000000000000000000000 : ℝ)*base76 + (12838985274077099/44281250000000000000000000000000 : ℝ)*base77 + (291245759389920849/44281250000000000000000000000000 : ℝ)*base79 + (1028211005063/177125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (12048601/10000000000000000000000 : ℝ)*base90 + (12048601/10000000000000000000000 : ℝ)*base92 + (12048601/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28007964560294112817414089/5535156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1248891627/100000000000000 : ℝ)*(base19) + (1232657341/100000000000000 : ℝ)*(base23) + (29893189/25000000000000 : ℝ)*(upper3) + (4394199/50000000000000 : ℝ)*(lower4) + (69300997/50000000000000 : ℝ)*(upper5) + (1456370225395747/25000000000000 : ℝ)*(major0) + (1456370225395747/25000000000000 : ℝ)*(major1) + (1456370225395747/25000000000000 : ℝ)*(major2) + (34697539041/100000000000000 : ℝ)*(sp1) + (8230848909/25000000000000 : ℝ)*(sp2) + (309039846251869/4000000000000 : ℝ)*(sp4) + (7725960209866057/100000000000000 : ℝ)*(sp5) + (7725962000243747/100000000000000 : ℝ)*(sp6) + (1962482739101063/50000000000000 : ℝ)*(sp7) + (1962482739101063/50000000000000 : ℝ)*(f.failure) + (309039846251869/4000000000000 : ℝ)*(f.sum) + (2051907162737/1417000000000000000000000000 : ℝ)*base65 + (16472949760373969/691894531250000000000000000000 : ℝ)*base68 + (332354414362076383/22140625000000000000000000000000 : ℝ)*base70 + (12998887212230251/2767578125000000000000000000000 : ℝ)*base72 + (1844946290339/354250000000000000000000000 : ℝ)*base74 + (1036850021027170133/22140625000000000000000000000000 : ℝ)*base76 + (107869746447905379/11070312500000000000000000000000 : ℝ)*base78 + (143438975377076383/22140625000000000000000000000000 : ℝ)*base80 + (208889589167/141700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (30836663/5000000000000000000000 : ℝ)*base89 + (30836663/5000000000000000000000 : ℝ)*base91 + (30836663/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1088_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1088_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1088_s7_0 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548243237/2500000000 : ℝ)*x 0 + (5394050019/10000000000 : ℝ)*x 1 + (2632388351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548243237/2500000000 : ℝ)^8281 ≤ (2664060732921/20000000000000 : ℝ)^6233 := by
    have hnat : (548243237 : ℕ)^8281*20000000000000^6233 ≤ 2664060732921^6233*2500000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548243237 2500000000 2664060732921 20000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394050019/10000000000 : ℝ)^8281 ≤ (44038170991753/100000000000000 : ℝ)^6233 := by
    have hnat : (5394050019 : ℕ)^8281*100000000000000^6233 ≤ 44038170991753^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394050019 10000000000 44038170991753 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632388351/5000000000 : ℝ)^8281 ≤ (10660381332381/25000000000000 : ℝ)^6233 := by
    have hnat : (2632388351 : ℕ)^8281*25000000000000^6233 ≤ 10660381332381^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632388351 5000000000 10660381332381 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548243237/2500000000 : ℝ), (5394050019/10000000000 : ℝ), (2632388351/5000000000 : ℝ)] ![(2664060732921/20000000000000 : ℝ), (44038170991753/100000000000000 : ℝ), (10660381332381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548243237/2500000000 : ℝ)|^8281 ≤ (2664060732921/20000000000000 : ℝ)^6233
        have hw : |(-548243237/2500000000 : ℝ)|=(548243237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394050019/10000000000 : ℝ)|^8281 ≤ (44038170991753/100000000000000 : ℝ)^6233
        have hw : |(5394050019/10000000000 : ℝ)|=(5394050019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632388351/5000000000 : ℝ)|^8281 ≤ (10660381332381/25000000000000 : ℝ)^6233
        have hw : |(2632388351/5000000000 : ℝ)|=(2632388351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_1 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668118041/1250000000 : ℝ)*x 0 + (-2258557227/10000000000 : ℝ)*x 1 + (5264776661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668118041/1250000000 : ℝ)^8281 ≤ (10876582920337/25000000000000 : ℝ)^6233 := by
    have hnat : (668118041 : ℕ)^8281*25000000000000^6233 ≤ 10876582920337^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668118041 1250000000 10876582920337 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258557227/10000000000 : ℝ)^8281 ≤ (1385214341549/10000000000000 : ℝ)^6233 := by
    have hnat : (2258557227 : ℕ)^8281*10000000000000^6233 ≤ 1385214341549^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258557227 10000000000 1385214341549 10000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264776661/10000000000 : ℝ)^8281 ≤ (21320762444169/50000000000000 : ℝ)^6233 := by
    have hnat : (5264776661 : ℕ)^8281*50000000000000^6233 ≤ 21320762444169^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264776661 10000000000 21320762444169 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668118041/1250000000 : ℝ), (-2258557227/10000000000 : ℝ), (5264776661/10000000000 : ℝ)] ![(10876582920337/25000000000000 : ℝ), (1385214341549/10000000000000 : ℝ), (21320762444169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668118041/1250000000 : ℝ)|^8281 ≤ (10876582920337/25000000000000 : ℝ)^6233
        have hw : |(668118041/1250000000 : ℝ)|=(668118041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258557227/10000000000 : ℝ)|^8281 ≤ (1385214341549/10000000000000 : ℝ)^6233
        have hw : |(-2258557227/10000000000 : ℝ)|=(2258557227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264776661/10000000000 : ℝ)|^8281 ≤ (21320762444169/50000000000000 : ℝ)^6233
        have hw : |(5264776661/10000000000 : ℝ)|=(5264776661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_2 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344943971/10000000000 : ℝ)*x 0 + (5264776829/10000000000 : ℝ)*x 1 + (-1129278739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344943971/10000000000 : ℝ)^8281 ≤ (21753163910337/50000000000000 : ℝ)^6233 := by
    have hnat : (5344943971 : ℕ)^8281*50000000000000^6233 ≤ 21753163910337^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344943971 10000000000 21753163910337 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264776829/10000000000 : ℝ)^8281 ≤ (42641526696127/100000000000000 : ℝ)^6233 := by
    have hnat : (5264776829 : ℕ)^8281*100000000000000^6233 ≤ 42641526696127^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264776829 10000000000 42641526696127 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129278739/5000000000 : ℝ)^8281 ≤ (2770429092147/20000000000000 : ℝ)^6233 := by
    have hnat : (1129278739 : ℕ)^8281*20000000000000^6233 ≤ 2770429092147^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129278739 5000000000 2770429092147 20000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344943971/10000000000 : ℝ), (5264776829/10000000000 : ℝ), (-1129278739/5000000000 : ℝ)] ![(21753163910337/50000000000000 : ℝ), (42641526696127/100000000000000 : ℝ), (2770429092147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344943971/10000000000 : ℝ)|^8281 ≤ (21753163910337/50000000000000 : ℝ)^6233
        have hw : |(5344943971/10000000000 : ℝ)|=(5344943971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264776829/10000000000 : ℝ)|^8281 ≤ (42641526696127/100000000000000 : ℝ)^6233
        have hw : |(5264776829/10000000000 : ℝ)|=(5264776829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129278739/5000000000 : ℝ)|^8281 ≤ (2770429092147/20000000000000 : ℝ)^6233
        have hw : |(-1129278739/5000000000 : ℝ)|=(1129278739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_3 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186166857/5000000000 : ℝ)*x 0 + (1061741773/2500000000 : ℝ)*x 1 + (1125358023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186166857/5000000000 : ℝ)^8281 ≤ (16658317633163/50000000000000 : ℝ)^6233 := by
    have hnat : (2186166857 : ℕ)^8281*50000000000000^6233 ≤ 16658317633163^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186166857 5000000000 16658317633163 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061741773/2500000000 : ℝ)^8281 ≤ (32053495333927/100000000000000 : ℝ)^6233 := by
    have hnat : (1061741773 : ℕ)^8281*100000000000000^6233 ≤ 32053495333927^6233*2500000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061741773 2500000000 32053495333927 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125358023/2500000000 : ℝ)^8281 ≤ (17314934693589/50000000000000 : ℝ)^6233 := by
    have hnat : (1125358023 : ℕ)^8281*50000000000000^6233 ≤ 17314934693589^6233*2500000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125358023 2500000000 17314934693589 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186166857/5000000000 : ℝ), (1061741773/2500000000 : ℝ), (1125358023/2500000000 : ℝ)] ![(16658317633163/50000000000000 : ℝ), (32053495333927/100000000000000 : ℝ), (17314934693589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186166857/5000000000 : ℝ)|^8281 ≤ (16658317633163/50000000000000 : ℝ)^6233
        have hw : |(2186166857/5000000000 : ℝ)|=(2186166857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061741773/2500000000 : ℝ)|^8281 ≤ (32053495333927/100000000000000 : ℝ)^6233
        have hw : |(1061741773/2500000000 : ℝ)|=(1061741773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125358023/2500000000 : ℝ)|^8281 ≤ (17314934693589/50000000000000 : ℝ)^6233
        have hw : |(1125358023/2500000000 : ℝ)|=(1125358023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_4 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192977799/10000000000 : ℝ)*x 0 + (658137641/1250000000 : ℝ)*x 1 + (5393724553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192977799/10000000000 : ℝ)^8281 ≤ (3330085702889/25000000000000 : ℝ)^6233 := by
    have hnat : (2192977799 : ℕ)^8281*25000000000000^6233 ≤ 3330085702889^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192977799 10000000000 3330085702889 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658137641/1250000000 : ℝ)^8281 ≤ (1066125409973/2500000000000 : ℝ)^6233 := by
    have hnat : (658137641 : ℕ)^8281*2500000000000^6233 ≤ 1066125409973^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658137641 1250000000 1066125409973 2500000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393724553/10000000000 : ℝ)^8281 ≤ (44034640775719/100000000000000 : ℝ)^6233 := by
    have hnat : (5393724553 : ℕ)^8281*100000000000000^6233 ≤ 44034640775719^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724553 10000000000 44034640775719 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192977799/10000000000 : ℝ), (658137641/1250000000 : ℝ), (5393724553/10000000000 : ℝ)] ![(3330085702889/25000000000000 : ℝ), (1066125409973/2500000000000 : ℝ), (44034640775719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192977799/10000000000 : ℝ)|^8281 ≤ (3330085702889/25000000000000 : ℝ)^6233
        have hw : |(-2192977799/10000000000 : ℝ)|=(2192977799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658137641/1250000000 : ℝ)|^8281 ≤ (1066125409973/2500000000000 : ℝ)^6233
        have hw : |(658137641/1250000000 : ℝ)|=(658137641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393724553/10000000000 : ℝ)|^8281 ≤ (44034640775719/100000000000000 : ℝ)^6233
        have hw : |(5393724553/10000000000 : ℝ)|=(5393724553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_5 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656163151/5000000000 : ℝ)*x 0 + (-2129609457/10000000000 : ℝ)*x 1 + (674215569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656163151/5000000000 : ℝ)^8281 ≤ (43153947516429/100000000000000 : ℝ)^6233 := by
    have hnat : (2656163151 : ℕ)^8281*100000000000000^6233 ≤ 43153947516429^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656163151 5000000000 43153947516429 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129609457/10000000000 : ℝ)^8281 ≤ (12811411701701/100000000000000 : ℝ)^6233 := by
    have hnat : (2129609457 : ℕ)^8281*100000000000000^6233 ≤ 12811411701701^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129609457 10000000000 12811411701701 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674215569/1250000000 : ℝ)^8281 ≤ (5504330095609/12500000000000 : ℝ)^6233 := by
    have hnat : (674215569 : ℕ)^8281*12500000000000^6233 ≤ 5504330095609^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674215569 1250000000 5504330095609 12500000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656163151/5000000000 : ℝ), (-2129609457/10000000000 : ℝ), (674215569/1250000000 : ℝ)] ![(43153947516429/100000000000000 : ℝ), (12811411701701/100000000000000 : ℝ), (5504330095609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656163151/5000000000 : ℝ)|^8281 ≤ (43153947516429/100000000000000 : ℝ)^6233
        have hw : |(2656163151/5000000000 : ℝ)|=(2656163151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2129609457/10000000000 : ℝ)|^8281 ≤ (12811411701701/100000000000000 : ℝ)^6233
        have hw : |(-2129609457/10000000000 : ℝ)|=(2129609457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674215569/1250000000 : ℝ)|^8281 ≤ (5504330095609/12500000000000 : ℝ)^6233
        have hw : |(674215569/1250000000 : ℝ)|=(674215569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_6 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166010197/312500000 : ℝ)*x 0 + (5393724551/10000000000 : ℝ)*x 1 + (-133100591/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166010197/312500000 : ℝ)^8281 ≤ (21576973769007/50000000000000 : ℝ)^6233 := by
    have hnat : (166010197 : ℕ)^8281*50000000000000^6233 ≤ 21576973769007^6233*312500000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166010197 312500000 21576973769007 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393724551/10000000000 : ℝ)^8281 ≤ (22017320377013/50000000000000 : ℝ)^6233 := by
    have hnat : (5393724551 : ℕ)^8281*50000000000000^6233 ≤ 22017320377013^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724551 10000000000 22017320377013 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133100591/625000000 : ℝ)^8281 ≤ (12811411693709/100000000000000 : ℝ)^6233 := by
    have hnat : (133100591 : ℕ)^8281*100000000000000^6233 ≤ 12811411693709^6233*625000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133100591 625000000 12811411693709 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166010197/312500000 : ℝ), (5393724551/10000000000 : ℝ), (-133100591/625000000 : ℝ)] ![(21576973769007/50000000000000 : ℝ), (22017320377013/50000000000000 : ℝ), (12811411693709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166010197/312500000 : ℝ)|^8281 ≤ (21576973769007/50000000000000 : ℝ)^6233
        have hw : |(166010197/312500000 : ℝ)|=(166010197/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393724551/10000000000 : ℝ)|^8281 ≤ (22017320377013/50000000000000 : ℝ)^6233
        have hw : |(5393724551/10000000000 : ℝ)|=(5393724551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133100591/625000000 : ℝ)|^8281 ≤ (12811411693709/100000000000000 : ℝ)^6233
        have hw : |(-133100591/625000000 : ℝ)|=(133100591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s7_7 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546542967/1250000000 : ℝ)*x 0 + (2250396701/5000000000 : ℝ)*x 1 + (2123803981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546542967/1250000000 : ℝ)^8281 ≤ (130143502831/390625000000 : ℝ)^6233 := by
    have hnat : (546542967 : ℕ)^8281*390625000000^6233 ≤ 130143502831^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546542967 1250000000 130143502831 390625000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250396701/5000000000 : ℝ)^8281 ≤ (34623341602793/100000000000000 : ℝ)^6233 := by
    have hnat : (2250396701 : ℕ)^8281*100000000000000^6233 ≤ 34623341602793^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250396701 5000000000 34623341602793 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123803981/5000000000 : ℝ)^8281 ≤ (2003745103849/6250000000000 : ℝ)^6233 := by
    have hnat : (2123803981 : ℕ)^8281*6250000000000^6233 ≤ 2003745103849^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123803981 5000000000 2003745103849 6250000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546542967/1250000000 : ℝ), (2250396701/5000000000 : ℝ), (2123803981/5000000000 : ℝ)] ![(130143502831/390625000000 : ℝ), (34623341602793/100000000000000 : ℝ), (2003745103849/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546542967/1250000000 : ℝ)|^8281 ≤ (130143502831/390625000000 : ℝ)^6233
        have hw : |(546542967/1250000000 : ℝ)|=(546542967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250396701/5000000000 : ℝ)|^8281 ≤ (34623341602793/100000000000000 : ℝ)^6233
        have hw : |(2250396701/5000000000 : ℝ)|=(2250396701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123803981/5000000000 : ℝ)|^8281 ≤ (2003745103849/6250000000000 : ℝ)^6233
        have hw : |(2123803981/5000000000 : ℝ)|=(2123803981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1088_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (141/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7009/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (1035/256 : ℝ) ≤ (14698383940581083/100000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^1035 ≤ (14698383940581083/100000000000000000000 : ℝ)^256 := by
      have hnat : (1409 : ℕ)^1035*100000000000000000000^256 ≤ 14698383940581083^256*12500^1035 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 14698383940581083 100000000000000000000 1035 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (14698383940581083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14027/100000 : ℝ) ^ (1035/256 : ℝ) ≤ (35579949847551919/100000000000000000000 : ℝ) := by
    have hpowers : (14027/100000 : ℝ)^1035 ≤ (35579949847551919/100000000000000000000 : ℝ)^256 := by
      have hnat : (14027 : ℕ)^1035*100000000000000000000^256 ≤ 35579949847551919^256*100000^1035 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14027 100000 35579949847551919 100000000000000000000 1035 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14027/100000 : ℝ)) (X := (35579949847551919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014698383940581083/50000000000000000000 : ℝ) ≤ (2500181757009139/2500000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50014698383940581083/50000000000000000000 : ℝ)^256 ≤ (2500181757009139/2500000000000000 : ℝ)^1035 := by
      have hnat : (50014698383940581083 : ℕ)^256*2500000000000000^1035 ≤ 2500181757009139^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014698383940581083 50000000000000000000 2500181757009139 2500000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500181757009139/2500000000000000 : ℝ)) (X := (50014698383940581083/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025139166894066501/50000000000000000000 : ℝ) ≤ (10001243364132669/10000000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50025139166894066501/50000000000000000000 : ℝ)^256 ≤ (10001243364132669/10000000000000000 : ℝ)^1035 := by
      have hnat : (50025139166894066501 : ℕ)^256*10000000000000000^1035 ≤ 10001243364132669^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025139166894066501 50000000000000000000 10001243364132669 10000000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001243364132669/10000000000000000 : ℝ)) (X := (50025139166894066501/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035579949847551919/50000000000000000000 : ℝ) ≤ (5000879850114391/5000000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50035579949847551919/50000000000000000000 : ℝ)^256 ≤ (5000879850114391/5000000000000000 : ℝ)^1035 := by
      have hnat : (50035579949847551919 : ℕ)^256*5000000000000000^1035 ≤ 5000879850114391^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035579949847551919 50000000000000000000 5000879850114391 5000000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000879850114391/5000000000000000 : ℝ)) (X := (50035579949847551919/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14698383940581083/100000000000000000000 : ℝ) ≤ ((6885090670322485077/6887500000000000000 : ℝ)+2*(516336096113/275500000000000 : ℝ)*(1409/12500 : ℝ))^(1035/256 : ℝ) := by
    rw [show (6885090670322485077/6887500000000000000 : ℝ)+2*(516336096113/275500000000000 : ℝ)*(1409/12500 : ℝ)=(2500181757009139/2500000000000000 : ℝ) by norm_num, show 1+2*(14698383940581083/100000000000000000000 : ℝ)=(50014698383940581083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35579949847551919/100000000000000000000 : ℝ)+(14698383940581083/100000000000000000000 : ℝ) ≤ ((6885090670322485077/6887500000000000000 : ℝ)+(516336096113/275500000000000 : ℝ)*((14027/100000 : ℝ)+(1409/12500 : ℝ)))^(1035/256 : ℝ) := by
    rw [show (6885090670322485077/6887500000000000000 : ℝ)+(516336096113/275500000000000 : ℝ)*((14027/100000 : ℝ)+(1409/12500 : ℝ))=(10001243364132669/10000000000000000 : ℝ) by norm_num, show 1+(35579949847551919/100000000000000000000 : ℝ)+(14698383940581083/100000000000000000000 : ℝ)=(50025139166894066501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35579949847551919/100000000000000000000 : ℝ) ≤ ((6885090670322485077/6887500000000000000 : ℝ)+2*(516336096113/275500000000000 : ℝ)*(14027/100000 : ℝ))^(1035/256 : ℝ) := by
    rw [show (6885090670322485077/6887500000000000000 : ℝ)+2*(516336096113/275500000000000 : ℝ)*(14027/100000 : ℝ)=(5000879850114391/5000000000000000 : ℝ) by norm_num, show 1+2*(35579949847551919/100000000000000000000 : ℝ)=(50035579949847551919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6885090670322485077/6887500000000000000 : ℝ)*(X 1 0+X 2 0)+(516336096113/275500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (6885090670322485077/6887500000000000000 : ℝ)) (alpha := (516336096113/275500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6885090670322485077/6887500000000000000 : ℝ)*(X 0 1+X 2 1)+(516336096113/275500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (6885090670322485077/6887500000000000000 : ℝ)) (alpha := (516336096113/275500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6885090670322485077/6887500000000000000 : ℝ)*(X 0 2+X 1 2)+(516336096113/275500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (6885090670322485077/6887500000000000000 : ℝ)) (alpha := (516336096113/275500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548243237/2500000000 : ℝ)*X 0 0+(5394050019/10000000000 : ℝ)*X 0 1+(2632388351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668118041/1250000000 : ℝ)*X 1 0+(-2258557227/10000000000 : ℝ)*X 1 1+(5264776661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344943971/10000000000 : ℝ)*X 2 0+(5264776829/10000000000 : ℝ)*X 2 1+(-1129278739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186166857/5000000000 : ℝ)*X 0 0+(1061741773/2500000000 : ℝ)*X 0 1+(1125358023/2500000000 : ℝ)*X 0 2+(2186166857/5000000000 : ℝ)*X 1 0+(1061741773/2500000000 : ℝ)*X 1 1+(1125358023/2500000000 : ℝ)*X 1 2+(2186166857/5000000000 : ℝ)*X 2 0+(1061741773/2500000000 : ℝ)*X 2 1+(1125358023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2192977799/10000000000 : ℝ)*X 0 0+(658137641/1250000000 : ℝ)*X 0 1+(5393724553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656163151/5000000000 : ℝ)*X 1 0+(-2129609457/10000000000 : ℝ)*X 1 1+(674215569/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166010197/312500000 : ℝ)*X 2 0+(5393724551/10000000000 : ℝ)*X 2 1+(-133100591/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546542967/1250000000 : ℝ)*X 0 0+(2250396701/5000000000 : ℝ)*X 0 1+(2123803981/5000000000 : ℝ)*X 0 2+(546542967/1250000000 : ℝ)*X 1 0+(2250396701/5000000000 : ℝ)*X 1 1+(2123803981/5000000000 : ℝ)*X 1 2+(546542967/1250000000 : ℝ)*X 2 0+(2250396701/5000000000 : ℝ)*X 2 1+(2123803981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (234858350531868894011626773/34437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724470577/50000000000000 : ℝ)*(base19) + (278758241/25000000000000 : ℝ)*(base23) + (57949159/50000000000000 : ℝ)*(upper2) + (11320291/3125000000000 : ℝ)*(upper3) + (18208811/100000000000000 : ℝ)*(upper4) + (1166547399872183/20000000000000 : ℝ)*(major0) + (1166547399872183/20000000000000 : ℝ)*(major1) + (1166547399872183/20000000000000 : ℝ)*(major2) + (966949597769173/12500000000000 : ℝ)*(sp0) + (773561798893257/10000000000000 : ℝ)*(sp1) + (193390458071019/2500000000000 : ℝ)*(sp2) + (982458013759429/25000000000000 : ℝ)*(sp3) + (1132786017/5000000000000 : ℝ)*(sp4) + (891139291/4000000000000 : ℝ)*(sp7) + (392985433351999/10000000000000 : ℝ)*(f.failure) + (1933904859468431/25000000000000 : ℝ)*(f.sum) + (391617317019/2755000000000000000000000000 : ℝ)*base65 + (2299616263692611909/137750000000000000000000000000000 : ℝ)*base68 + (661172825785611909/137750000000000000000000000000000 : ℝ)*base70 + (1955322776145888091/137750000000000000000000000000000 : ℝ)*base71 + (13260397003481/2755000000000000000000000000 : ℝ)*base74 + (882341633606111909/137750000000000000000000000000000 : ℝ)*base76 + (105292560104111909/137750000000000000000000000000000 : ℝ)*base78 + (1899051967548611909/137750000000000000000000000000000 : ℝ)*base80 + (14257277526531/2755000000000000000000000000 : ℝ)*base82 + (2669201/1000000000000000000000 : ℝ)*base90 + (2669201/1000000000000000000000 : ℝ)*base92 + (2669201/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83568160755935348661000159/21523437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (352660993/50000000000000 : ℝ)*(base19) + (387805431/50000000000000 : ℝ)*(base23) + (15297307/20000000000000 : ℝ)*(upper3) + (30371941/100000000000000 : ℝ)*(lower4) + (4861761/6250000000000 : ℝ)*(upper5) + (1465538368574003/25000000000000 : ℝ)*(major0) + (1465538368574003/25000000000000 : ℝ)*(major1) + (1465538368574003/25000000000000 : ℝ)*(major2) + (19203628207/100000000000000 : ℝ)*(sp1) + (20863331179/100000000000000 : ℝ)*(sp2) + (194365822367269/2500000000000 : ℝ)*(sp4) + (3887306492870283/50000000000000 : ℝ)*(sp5) + (7774611255748719/100000000000000 : ℝ)*(sp6) + (3949673924479301/100000000000000 : ℝ)*(sp7) + (3949673924479301/100000000000000 : ℝ)*(f.failure) + (194365822367269/2500000000000 : ℝ)*(f.sum) + (5110806249739/3443750000000000000000000000 : ℝ)*base65 + (534857342748246769/172187500000000000000000000000000 : ℝ)*base68 + (765067821985746769/172187500000000000000000000000000 : ℝ)*base70 + (2817303571242621769/172187500000000000000000000000000 : ℝ)*base72 + (19826572591331/13775000000000000000000000000 : ℝ)*base73 + (1095189653682309269/172187500000000000000000000000000 : ℝ)*base76 + (696225489411440731/172187500000000000000000000000000 : ℝ)*base77 + (1709584914085746769/172187500000000000000000000000000 : ℝ)*base80 + (1191014636761/3443750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (45939499/10000000000000000000000 : ℝ)*base90 + (45939499/10000000000000000000000 : ℝ)*base92 + (45939499/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1088_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1088_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1088_s8_0 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192982591/10000000000 : ℝ)*x 0 + (1348489939/2500000000 : ℝ)*x 1 + (1052972091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192982591/10000000000 : ℝ)^8281 ≤ (3330095370603/25000000000000 : ℝ)^6233 := by
    have hnat : (2192982591 : ℕ)^8281*25000000000000^6233 ≤ 3330095370603^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192982591 10000000000 3330095370603 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348489939/2500000000 : ℝ)^8281 ≤ (22018595966751/50000000000000 : ℝ)^6233 := by
    have hnat : (1348489939 : ℕ)^8281*50000000000000^6233 ≤ 22018595966751^6233*2500000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348489939 2500000000 22018595966751 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052972091/2000000000 : ℝ)^8281 ≤ (42642426568449/100000000000000 : ℝ)^6233 := by
    have hnat : (1052972091 : ℕ)^8281*100000000000000^6233 ≤ 42642426568449^6233*2000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052972091 2000000000 42642426568449 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192982591/10000000000 : ℝ), (1348489939/2500000000 : ℝ), (1052972091/2000000000 : ℝ)] ![(3330095370603/25000000000000 : ℝ), (22018595966751/50000000000000 : ℝ), (42642426568449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192982591/10000000000 : ℝ)|^8281 ≤ (3330095370603/25000000000000 : ℝ)^6233
        have hw : |(-2192982591/10000000000 : ℝ)|=(2192982591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348489939/2500000000 : ℝ)|^8281 ≤ (22018595966751/50000000000000 : ℝ)^6233
        have hw : |(1348489939/2500000000 : ℝ)|=(1348489939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052972091/2000000000 : ℝ)|^8281 ≤ (42642426568449/100000000000000 : ℝ)^6233
        have hw : |(1052972091/2000000000 : ℝ)|=(1052972091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_1 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672460511/5000000000 : ℝ)*x 0 + (-282309691/1250000000 : ℝ)*x 1 + (5264860433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672460511/5000000000 : ℝ)^8281 ≤ (4350607964547/10000000000000 : ℝ)^6233 := by
    have hnat : (2672460511 : ℕ)^8281*10000000000000^6233 ≤ 4350607964547^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672460511 5000000000 4350607964547 10000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282309691/1250000000 : ℝ)^8281 ≤ (13851494001123/100000000000000 : ℝ)^6233 := by
    have hnat : (282309691 : ℕ)^8281*100000000000000^6233 ≤ 13851494001123^6233*1250000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282309691 1250000000 13851494001123 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264860433/10000000000 : ℝ)^8281 ≤ (42642426331713/100000000000000 : ℝ)^6233 := by
    have hnat : (5264860433 : ℕ)^8281*100000000000000^6233 ≤ 42642426331713^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264860433 10000000000 42642426331713 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672460511/5000000000 : ℝ), (-282309691/1250000000 : ℝ), (5264860433/10000000000 : ℝ)] ![(4350607964547/10000000000000 : ℝ), (13851494001123/100000000000000 : ℝ), (42642426331713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672460511/5000000000 : ℝ)|^8281 ≤ (4350607964547/10000000000000 : ℝ)^6233
        have hw : |(2672460511/5000000000 : ℝ)|=(2672460511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282309691/1250000000 : ℝ)|^8281 ≤ (13851494001123/100000000000000 : ℝ)^6233
        have hw : |(-282309691/1250000000 : ℝ)|=(282309691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264860433/10000000000 : ℝ)|^8281 ≤ (42642426331713/100000000000000 : ℝ)^6233
        have hw : |(5264860433/10000000000 : ℝ)|=(5264860433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_2 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213796841/400000000 : ℝ)*x 0 + (5264860447/10000000000 : ℝ)*x 1 + (-1129238753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213796841/400000000 : ℝ)^8281 ≤ (5438259959739/12500000000000 : ℝ)^6233 := by
    have hnat : (213796841 : ℕ)^8281*12500000000000^6233 ≤ 5438259959739^6233*400000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213796841 400000000 5438259959739 12500000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264860447/10000000000 : ℝ)^8281 ≤ (42642426482363/100000000000000 : ℝ)^6233 := by
    have hnat : (5264860447 : ℕ)^8281*100000000000000^6233 ≤ 42642426482363^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264860447 10000000000 42642426482363 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129238753/5000000000 : ℝ)^8281 ≤ (13851493821861/100000000000000 : ℝ)^6233 := by
    have hnat : (1129238753 : ℕ)^8281*100000000000000^6233 ≤ 13851493821861^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129238753 5000000000 13851493821861 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213796841/400000000 : ℝ), (5264860447/10000000000 : ℝ), (-1129238753/5000000000 : ℝ)] ![(5438259959739/12500000000000 : ℝ), (42642426482363/100000000000000 : ℝ), (13851493821861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213796841/400000000 : ℝ)|^8281 ≤ (5438259959739/12500000000000 : ℝ)^6233
        have hw : |(213796841/400000000 : ℝ)|=(213796841/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264860447/10000000000 : ℝ)|^8281 ≤ (42642426482363/100000000000000 : ℝ)^6233
        have hw : |(5264860447/10000000000 : ℝ)|=(5264860447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129238753/5000000000 : ℝ)|^8281 ≤ (13851493821861/100000000000000 : ℝ)^6233
        have hw : |(-1129238753/5000000000 : ℝ)|=(1129238753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_3 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372338261/10000000000 : ℝ)*x 0 + (4247137881/10000000000 : ℝ)*x 1 + (4501260031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372338261/10000000000 : ℝ)^8281 ≤ (16658340649093/50000000000000 : ℝ)^6233 := by
    have hnat : (4372338261 : ℕ)^8281*50000000000000^6233 ≤ 16658340649093^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372338261 10000000000 16658340649093 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247137881/10000000000 : ℝ)^8281 ≤ (32055207890479/100000000000000 : ℝ)^6233 := by
    have hnat : (4247137881 : ℕ)^8281*100000000000000^6233 ≤ 32055207890479^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247137881 10000000000 32055207890479 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501260031/10000000000 : ℝ)^8281 ≤ (17314055396717/50000000000000 : ℝ)^6233 := by
    have hnat : (4501260031 : ℕ)^8281*50000000000000^6233 ≤ 17314055396717^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501260031 10000000000 17314055396717 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372338261/10000000000 : ℝ), (4247137881/10000000000 : ℝ), (4501260031/10000000000 : ℝ)] ![(16658340649093/50000000000000 : ℝ), (32055207890479/100000000000000 : ℝ), (17314055396717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372338261/10000000000 : ℝ)|^8281 ≤ (16658340649093/50000000000000 : ℝ)^6233
        have hw : |(4372338261/10000000000 : ℝ)|=(4372338261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247137881/10000000000 : ℝ)|^8281 ≤ (32055207890479/100000000000000 : ℝ)^6233
        have hw : |(4247137881/10000000000 : ℝ)|=(4247137881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501260031/10000000000 : ℝ)|^8281 ≤ (17314055396717/50000000000000 : ℝ)^6233
        have hw : |(4501260031/10000000000 : ℝ)|=(4501260031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_4 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-438597521/2000000000 : ℝ)*x 0 + (2632592061/5000000000 : ℝ)*x 1 + (5393634919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438597521/2000000000 : ℝ)^8281 ≤ (13320421944811/100000000000000 : ℝ)^6233 := by
    have hnat : (438597521 : ℕ)^8281*100000000000000^6233 ≤ 13320421944811^6233*2000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438597521 2000000000 13320421944811 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632592061/5000000000 : ℝ)^8281 ≤ (42645909488551/100000000000000 : ℝ)^6233 := by
    have hnat : (2632592061 : ℕ)^8281*100000000000000^6233 ≤ 42645909488551^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632592061 5000000000 42645909488551 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393634919/10000000000 : ℝ)^8281 ≤ (44033668559317/100000000000000 : ℝ)^6233 := by
    have hnat : (5393634919 : ℕ)^8281*100000000000000^6233 ≤ 44033668559317^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393634919 10000000000 44033668559317 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438597521/2000000000 : ℝ), (2632592061/5000000000 : ℝ), (5393634919/10000000000 : ℝ)] ![(13320421944811/100000000000000 : ℝ), (42645909488551/100000000000000 : ℝ), (44033668559317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438597521/2000000000 : ℝ)|^8281 ≤ (13320421944811/100000000000000 : ℝ)^6233
        have hw : |(-438597521/2000000000 : ℝ)|=(438597521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632592061/5000000000 : ℝ)|^8281 ≤ (42645909488551/100000000000000 : ℝ)^6233
        have hw : |(2632592061/5000000000 : ℝ)|=(2632592061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393634919/10000000000 : ℝ)|^8281 ≤ (44033668559317/100000000000000 : ℝ)^6233
        have hw : |(5393634919/10000000000 : ℝ)|=(5393634919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_5 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312347201/10000000000 : ℝ)*x 0 + (-2129702877/10000000000 : ℝ)*x 1 + (2696817459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312347201/10000000000 : ℝ)^8281 ≤ (21577086534357/50000000000000 : ℝ)^6233 := by
    have hnat : (5312347201 : ℕ)^8281*50000000000000^6233 ≤ 21577086534357^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312347201 10000000000 21577086534357 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129702877/10000000000 : ℝ)^8281 ≤ (1281215836649/10000000000000 : ℝ)^6233 := by
    have hnat : (2129702877 : ℕ)^8281*10000000000000^6233 ≤ 1281215836649^6233*10000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129702877 10000000000 1281215836649 10000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696817459/5000000000 : ℝ)^8281 ≤ (44033668548471/100000000000000 : ℝ)^6233 := by
    have hnat : (2696817459 : ℕ)^8281*100000000000000^6233 ≤ 44033668548471^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696817459 5000000000 44033668548471 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312347201/10000000000 : ℝ), (-2129702877/10000000000 : ℝ), (2696817459/5000000000 : ℝ)] ![(21577086534357/50000000000000 : ℝ), (1281215836649/10000000000000 : ℝ), (44033668548471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312347201/10000000000 : ℝ)|^8281 ≤ (21577086534357/50000000000000 : ℝ)^6233
        have hw : |(5312347201/10000000000 : ℝ)|=(5312347201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2129702877/10000000000 : ℝ)|^8281 ≤ (1281215836649/10000000000000 : ℝ)^6233
        have hw : |(-2129702877/10000000000 : ℝ)|=(2129702877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696817459/5000000000 : ℝ)|^8281 ≤ (44033668548471/100000000000000 : ℝ)^6233
        have hw : |(2696817459/5000000000 : ℝ)|=(2696817459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_6 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656173507/5000000000 : ℝ)*x 0 + (168551097/312500000 : ℝ)*x 1 + (-1064851439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656173507/5000000000 : ℝ)^8281 ≤ (10788542762629/25000000000000 : ℝ)^6233 := by
    have hnat : (2656173507 : ℕ)^8281*25000000000000^6233 ≤ 10788542762629^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656173507 5000000000 10788542762629 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168551097/312500000 : ℝ)^8281 ≤ (44033670565917/100000000000000 : ℝ)^6233 := by
    have hnat : (168551097 : ℕ)^8281*100000000000000^6233 ≤ 44033670565917^6233*312500000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168551097 312500000 44033670565917 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064851439/5000000000 : ℝ)^8281 ≤ (12812158374483/100000000000000 : ℝ)^6233 := by
    have hnat : (1064851439 : ℕ)^8281*100000000000000^6233 ≤ 12812158374483^6233*5000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064851439 5000000000 12812158374483 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656173507/5000000000 : ℝ), (168551097/312500000 : ℝ), (-1064851439/5000000000 : ℝ)] ![(10788542762629/25000000000000 : ℝ), (44033670565917/100000000000000 : ℝ), (12812158374483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656173507/5000000000 : ℝ)|^8281 ≤ (10788542762629/25000000000000 : ℝ)^6233
        have hw : |(2656173507/5000000000 : ℝ)|=(2656173507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168551097/312500000 : ℝ)|^8281 ≤ (44033670565917/100000000000000 : ℝ)^6233
        have hw : |(168551097/312500000 : ℝ)|=(168551097/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064851439/5000000000 : ℝ)|^8281 ≤ (12812158374483/100000000000000 : ℝ)^6233
        have hw : |(-1064851439/5000000000 : ℝ)|=(1064851439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1088_s8_7 (p : ℝ) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34158969/78125000 : ℝ)*x 0 + (7200997/16000000 : ℝ)*x 1 + (424777717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34158969/78125000 : ℝ)^8281 ≤ (33316780215613/100000000000000 : ℝ)^6233 := by
    have hnat : (34158969 : ℕ)^8281*100000000000000^6233 ≤ 33316780215613^6233*78125000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34158969 78125000 33316780215613 100000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7200997/16000000 : ℝ)^8281 ≤ (8655400330977/25000000000000 : ℝ)^6233 := by
    have hnat : (7200997 : ℕ)^8281*25000000000000^6233 ≤ 8655400330977^6233*16000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7200997 16000000 8655400330977 25000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424777717/1000000000 : ℝ)^8281 ≤ (16030809224477/50000000000000 : ℝ)^6233 := by
    have hnat : (424777717 : ℕ)^8281*50000000000000^6233 ≤ 16030809224477^6233*1000000000^8281 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424777717 1000000000 16030809224477 50000000000000 8281 6233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8281/2048 : ℝ)) 8281 6233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34158969/78125000 : ℝ), (7200997/16000000 : ℝ), (424777717/1000000000 : ℝ)] ![(33316780215613/100000000000000 : ℝ), (8655400330977/25000000000000 : ℝ), (16030809224477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34158969/78125000 : ℝ)|^8281 ≤ (33316780215613/100000000000000 : ℝ)^6233
        have hw : |(34158969/78125000 : ℝ)|=(34158969/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7200997/16000000 : ℝ)|^8281 ≤ (8655400330977/25000000000000 : ℝ)^6233
        have hw : |(7200997/16000000 : ℝ)|=(7200997/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424777717/1000000000 : ℝ)|^8281 ≤ (16030809224477/50000000000000 : ℝ)^6233
        have hw : |(424777717/1000000000 : ℝ)|=(424777717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1088_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (5641/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (438/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (141/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (141/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (141/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (141/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (141/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (141/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (141/1250 : ℝ) ^ (1035/256 : ℝ) ≤ (2948120976497311/20000000000000000000 : ℝ) := by
    have hpowers : (141/1250 : ℝ)^1035 ≤ (2948120976497311/20000000000000000000 : ℝ)^256 := by
      have hnat : (141 : ℕ)^1035*20000000000000000000^256 ≤ 2948120976497311^256*1250^1035 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1250 2948120976497311 20000000000000000000 1035 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1250 : ℝ)) (X := (2948120976497311/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7009/50000 : ℝ) ^ (1035/256 : ℝ) ≤ (35487743792338777/100000000000000000000 : ℝ) := by
    have hpowers : (7009/50000 : ℝ)^1035 ≤ (35487743792338777/100000000000000000000 : ℝ)^256 := by
      have hnat : (7009 : ℕ)^1035*100000000000000000000^256 ≤ 35487743792338777^256*50000^1035 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7009 50000 35487743792338777 100000000000000000000 1035 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7009/50000 : ℝ)) (X := (35487743792338777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002948120976497311/10000000000000000000 : ℝ) ≤ (10000729116184739/10000000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (10002948120976497311/10000000000000000000 : ℝ)^256 ≤ (10000729116184739/10000000000000000 : ℝ)^1035 := by
      have hnat : (10002948120976497311 : ℕ)^256*10000000000000000^1035 ≤ 10000729116184739^1035*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002948120976497311 10000000000000000000 10000729116184739 10000000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729116184739/10000000000000000 : ℝ)) (X := (10002948120976497311/10000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012557087168706333/25000000000000000000 : ℝ) ≤ (10001242128253329/10000000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (25012557087168706333/25000000000000000000 : ℝ)^256 ≤ (10001242128253329/10000000000000000 : ℝ)^1035 := by
      have hnat : (25012557087168706333 : ℕ)^256*10000000000000000^1035 ≤ 10001242128253329^1035*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012557087168706333 25000000000000000000 10001242128253329 10000000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001242128253329/10000000000000000 : ℝ)) (X := (25012557087168706333/25000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035487743792338777/50000000000000000000 : ℝ) ≤ (10001755140321919/10000000000000000 : ℝ) ^ (1035/256 : ℝ) := by
    have hpowers : (50035487743792338777/50000000000000000000 : ℝ)^256 ≤ (10001755140321919/10000000000000000 : ℝ)^1035 := by
      have hnat : (50035487743792338777 : ℕ)^256*10000000000000000^1035 ≤ 10001755140321919^1035*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035487743792338777 50000000000000000000 10001755140321919 10000000000000000 256 1035 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001755140321919/10000000000000000 : ℝ)) (X := (50035487743792338777/50000000000000000000 : ℝ)) (by norm_num) 1035 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2948120976497311/20000000000000000000 : ℝ) ≤ ((13685211383923212491/13690000000000000000 : ℝ)+2*(51301206859/27380000000000 : ℝ)*(141/1250 : ℝ))^(1035/256 : ℝ) := by
    rw [show (13685211383923212491/13690000000000000000 : ℝ)+2*(51301206859/27380000000000 : ℝ)*(141/1250 : ℝ)=(10000729116184739/10000000000000000 : ℝ) by norm_num, show 1+2*(2948120976497311/20000000000000000000 : ℝ)=(10002948120976497311/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35487743792338777/100000000000000000000 : ℝ)+(2948120976497311/20000000000000000000 : ℝ) ≤ ((13685211383923212491/13690000000000000000 : ℝ)+(51301206859/27380000000000 : ℝ)*((7009/50000 : ℝ)+(141/1250 : ℝ)))^(1035/256 : ℝ) := by
    rw [show (13685211383923212491/13690000000000000000 : ℝ)+(51301206859/27380000000000 : ℝ)*((7009/50000 : ℝ)+(141/1250 : ℝ))=(10001242128253329/10000000000000000 : ℝ) by norm_num, show 1+(35487743792338777/100000000000000000000 : ℝ)+(2948120976497311/20000000000000000000 : ℝ)=(25012557087168706333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35487743792338777/100000000000000000000 : ℝ) ≤ ((13685211383923212491/13690000000000000000 : ℝ)+2*(51301206859/27380000000000 : ℝ)*(7009/50000 : ℝ))^(1035/256 : ℝ) := by
    rw [show (13685211383923212491/13690000000000000000 : ℝ)+2*(51301206859/27380000000000 : ℝ)*(7009/50000 : ℝ)=(10001755140321919/10000000000000000 : ℝ) by norm_num, show 1+2*(35487743792338777/100000000000000000000 : ℝ)=(50035487743792338777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13685211383923212491/13690000000000000000 : ℝ)*(X 1 0+X 2 0)+(51301206859/27380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (13685211383923212491/13690000000000000000 : ℝ)) (alpha := (51301206859/27380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13685211383923212491/13690000000000000000 : ℝ)*(X 0 1+X 2 1)+(51301206859/27380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (13685211383923212491/13690000000000000000 : ℝ)) (alpha := (51301206859/27380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13685211383923212491/13690000000000000000 : ℝ)*(X 0 2+X 1 2)+(51301206859/27380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1035/256 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (13685211383923212491/13690000000000000000 : ℝ)) (alpha := (51301206859/27380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2192982591/10000000000 : ℝ)*X 0 0+(1348489939/2500000000 : ℝ)*X 0 1+(1052972091/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672460511/5000000000 : ℝ)*X 1 0+(-282309691/1250000000 : ℝ)*X 1 1+(5264860433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213796841/400000000 : ℝ)*X 2 0+(5264860447/10000000000 : ℝ)*X 2 1+(-1129238753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372338261/10000000000 : ℝ)*X 0 0+(4247137881/10000000000 : ℝ)*X 0 1+(4501260031/10000000000 : ℝ)*X 0 2+(4372338261/10000000000 : ℝ)*X 1 0+(4247137881/10000000000 : ℝ)*X 1 1+(4501260031/10000000000 : ℝ)*X 1 2+(4372338261/10000000000 : ℝ)*X 2 0+(4247137881/10000000000 : ℝ)*X 2 1+(4501260031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438597521/2000000000 : ℝ)*X 0 0+(2632592061/5000000000 : ℝ)*X 0 1+(5393634919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312347201/10000000000 : ℝ)*X 1 0+(-2129702877/10000000000 : ℝ)*X 1 1+(2696817459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656173507/5000000000 : ℝ)*X 2 0+(168551097/312500000 : ℝ)*X 2 1+(-1064851439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34158969/78125000 : ℝ)*X 0 0+(7200997/16000000 : ℝ)*X 0 1+(424777717/1000000000 : ℝ)*X 0 2+(34158969/78125000 : ℝ)*X 1 0+(7200997/16000000 : ℝ)*X 1 1+(424777717/1000000000 : ℝ)*X 1 2+(34158969/78125000 : ℝ)*X 2 0+(7200997/16000000 : ℝ)*X 2 1+(424777717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1088_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1668347795676941694507385041/342250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483119001/50000000000000 : ℝ)*(base19) + (433349909/50000000000000 : ℝ)*(base23) + (55526183/100000000000000 : ℝ)*(lower2) + (102106121/100000000000000 : ℝ)*(upper3) + (60860113/100000000000000 : ℝ)*(upper5) + (5840585212223983/100000000000000 : ℝ)*(major0) + (5840585212223983/100000000000000 : ℝ)*(major1) + (5840585212223983/100000000000000 : ℝ)*(major2) + (484125115862491/6250000000000 : ℝ)*(sp0) + (1936506791123703/25000000000000 : ℝ)*(sp1) + (1936506816008249/25000000000000 : ℝ)*(sp2) + (1967564026698363/50000000000000 : ℝ)*(sp3) + (13138466479/50000000000000 : ℝ)*(sp4) + (14077830189/100000000000000 : ℝ)*(sp7) + (1967571065613457/50000000000000 : ℝ)*(f.failure) + (1549205626146563/20000000000000 : ℝ)*(f.sum) + (1186771483463/273800000000000000000000000 : ℝ)*base66 + (6618657739026871653/1369000000000000000000000000000000 : ℝ)*base67 + (23722790034551871653/1369000000000000000000000000000000 : ℝ)*base69 + (18096752360168128347/1369000000000000000000000000000000 : ℝ)*base72 + (2753319837629/684500000000000000000000000 : ℝ)*base74 + (12356368115085871653/1369000000000000000000000000000000 : ℝ)*base75 + (3881990883547871653/1369000000000000000000000000000000 : ℝ)*base77 + (17460287316226871653/1369000000000000000000000000000000 : ℝ)*base79 + (6075243099143/1369000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (60298143/5000000000000000000000 : ℝ)*base90 + (60298143/5000000000000000000000 : ℝ)*base92 + (60298143/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (886214708349686924353408647/342250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765719253/100000000000000 : ℝ)*(base19) + (489896243/100000000000000 : ℝ)*(base23) + (77216177/25000000000000 : ℝ)*(lower1) + (107771/100000000000000 : ℝ)*(upper2) + (38908053/100000000000000 : ℝ)*(upper3) + (5870010546896439/100000000000000 : ℝ)*(major0) + (5870010546896439/100000000000000 : ℝ)*(major1) + (5870010546896439/100000000000000 : ℝ)*(major2) + (323587289/100000000000000 : ℝ)*(sp1) + (329825881/20000000000000 : ℝ)*(sp3) + (243282916124169/3125000000000 : ℝ)*(sp4) + (1946263056666717/25000000000000 : ℝ)*(sp5) + (1557010565215433/20000000000000 : ℝ)*(sp6) + (988741510594361/25000000000000 : ℝ)*(sp7) + (123592740359589/3125000000000 : ℝ)*(f.failure) + (243282916124169/3125000000000 : ℝ)*(f.sum) + (2252598591959/342250000000000000000000000 : ℝ)*base66 + (9595217861570280451/1369000000000000000000000000000000 : ℝ)*base68 + (14934027504884280451/1369000000000000000000000000000000 : ℝ)*base70 + (27041301623372280451/1369000000000000000000000000000000 : ℝ)*base72 + (646381869489/171125000000000000000000000 : ℝ)*base74 + (2081991048205280451/1369000000000000000000000000000000 : ℝ)*base76 + (52889119393031719549/1369000000000000000000000000000000 : ℝ)*base77 + (5462169055266280451/1369000000000000000000000000000000 : ℝ)*base80 + (94459779587/42781250000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (628611/312500000000000000000 : ℝ)*base90 + (628611/312500000000000000000 : ℝ)*base92 + (628611/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1088_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1088_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1088_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1088_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1088_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1088_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1035/256 : ℝ) ≤ p) (hpb : p ≤ (8281/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148421201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1088_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
