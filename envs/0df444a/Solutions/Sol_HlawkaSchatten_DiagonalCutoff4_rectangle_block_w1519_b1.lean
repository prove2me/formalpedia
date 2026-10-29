-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1519_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:08.539136+00:00
-- url     : https://prove2.me/submissions/c07ad9de-b2f7-41c1-b4bd-cf515bbea66e

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
theorem support_rectangle_w1519_s3_0 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-185726793/1000000000 : ℝ)*x 0 + (5435345197/10000000000 : ℝ)*x 1 + (5215263839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185726793/1000000000 : ℝ)^4535 ≤ (568340127747/5000000000000 : ℝ)^3511 := by
    have hnat : (185726793 : ℕ)^4535*5000000000000^3511 ≤ 568340127747^3511*1000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185726793 1000000000 568340127747 5000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435345197/10000000000 : ℝ)^4535 ≤ (2843707154671/6250000000000 : ℝ)^3511 := by
    have hnat : (5435345197 : ℕ)^4535*6250000000000^3511 ≤ 2843707154671^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435345197 10000000000 2843707154671 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215263839/10000000000 : ℝ)^4535 ≤ (1347933842597/3125000000000 : ℝ)^3511 := by
    have hnat : (5215263839 : ℕ)^4535*3125000000000^3511 ≤ 1347933842597^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215263839 10000000000 1347933842597 3125000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185726793/1000000000 : ℝ), (5435345197/10000000000 : ℝ), (5215263839/10000000000 : ℝ)] ![(568340127747/5000000000000 : ℝ), (2843707154671/6250000000000 : ℝ), (1347933842597/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185726793/1000000000 : ℝ)|^4535 ≤ (568340127747/5000000000000 : ℝ)^3511
        have hw : |(-185726793/1000000000 : ℝ)|=(185726793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435345197/10000000000 : ℝ)|^4535 ≤ (2843707154671/6250000000000 : ℝ)^3511
        have hw : |(5435345197/10000000000 : ℝ)|=(5435345197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215263839/10000000000 : ℝ)|^4535 ≤ (1347933842597/3125000000000 : ℝ)^3511
        have hw : |(5215263839/10000000000 : ℝ)|=(5215263839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_1 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351990037/10000000000 : ℝ)*x 0 + (-394007607/2000000000 : ℝ)*x 1 + (1043052821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351990037/10000000000 : ℝ)^4535 ≤ (4460006375769/10000000000000 : ℝ)^3511 := by
    have hnat : (5351990037 : ℕ)^4535*10000000000000^3511 ≤ 4460006375769^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351990037 10000000000 4460006375769 10000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394007607/2000000000 : ℝ)^4535 ≤ (95828518877/781250000000 : ℝ)^3511 := by
    have hnat : (394007607 : ℕ)^4535*781250000000^3511 ≤ 95828518877^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394007607 2000000000 95828518877 781250000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043052821/2000000000 : ℝ)^4535 ≤ (2695867862797/6250000000000 : ℝ)^3511 := by
    have hnat : (1043052821 : ℕ)^4535*6250000000000^3511 ≤ 2695867862797^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043052821 2000000000 2695867862797 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351990037/10000000000 : ℝ), (-394007607/2000000000 : ℝ), (1043052821/2000000000 : ℝ)] ![(4460006375769/10000000000000 : ℝ), (95828518877/781250000000 : ℝ), (2695867862797/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351990037/10000000000 : ℝ)|^4535 ≤ (4460006375769/10000000000000 : ℝ)^3511
        have hw : |(5351990037/10000000000 : ℝ)|=(5351990037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-394007607/2000000000 : ℝ)|^4535 ≤ (95828518877/781250000000 : ℝ)^3511
        have hw : |(-394007607/2000000000 : ℝ)|=(394007607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043052821/2000000000 : ℝ)|^4535 ≤ (2695867862797/6250000000000 : ℝ)^3511
        have hw : |(1043052821/2000000000 : ℝ)|=(1043052821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_2 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668998763/1250000000 : ℝ)*x 0 + (5215264021/10000000000 : ℝ)*x 1 + (-1970038057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668998763/1250000000 : ℝ)^4535 ≤ (22300032239433/50000000000000 : ℝ)^3511 := by
    have hnat : (668998763 : ℕ)^4535*50000000000000^3511 ≤ 22300032239433^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668998763 1250000000 22300032239433 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215264021/10000000000 : ℝ)^4535 ≤ (43133884907389/100000000000000 : ℝ)^3511 := by
    have hnat : (5215264021 : ℕ)^4535*100000000000000^3511 ≤ 43133884907389^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215264021 10000000000 43133884907389 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970038057/10000000000 : ℝ)^4535 ≤ (2453210118637/20000000000000 : ℝ)^3511 := by
    have hnat : (1970038057 : ℕ)^4535*20000000000000^3511 ≤ 2453210118637^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970038057 10000000000 2453210118637 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668998763/1250000000 : ℝ), (5215264021/10000000000 : ℝ), (-1970038057/10000000000 : ℝ)] ![(22300032239433/50000000000000 : ℝ), (43133884907389/100000000000000 : ℝ), (2453210118637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668998763/1250000000 : ℝ)|^4535 ≤ (22300032239433/50000000000000 : ℝ)^3511
        have hw : |(668998763/1250000000 : ℝ)|=(668998763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215264021/10000000000 : ℝ)|^4535 ≤ (43133884907389/100000000000000 : ℝ)^3511
        have hw : |(5215264021/10000000000 : ℝ)|=(5215264021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970038057/10000000000 : ℝ)|^4535 ≤ (2453210118637/20000000000000 : ℝ)^3511
        have hw : |(-1970038057/10000000000 : ℝ)|=(1970038057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_3 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266236571/10000000000 : ℝ)*x 0 + (4021698171/10000000000 : ℝ)*x 1 + (904642853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266236571/10000000000 : ℝ)^4535 ≤ (4159640297009/12500000000000 : ℝ)^3511 := by
    have hnat : (4266236571 : ℕ)^4535*12500000000000^3511 ≤ 4159640297009^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266236571 10000000000 4159640297009 12500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021698171/10000000000 : ℝ)^4535 ≤ (30834264824587/100000000000000 : ℝ)^3511 := by
    have hnat : (4021698171 : ℕ)^4535*100000000000000^3511 ≤ 30834264824587^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021698171 10000000000 30834264824587 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904642853/2000000000 : ℝ)^4535 ≤ (35888612780061/100000000000000 : ℝ)^3511 := by
    have hnat : (904642853 : ℕ)^4535*100000000000000^3511 ≤ 35888612780061^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904642853 2000000000 35888612780061 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266236571/10000000000 : ℝ), (4021698171/10000000000 : ℝ), (904642853/2000000000 : ℝ)] ![(4159640297009/12500000000000 : ℝ), (30834264824587/100000000000000 : ℝ), (35888612780061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266236571/10000000000 : ℝ)|^4535 ≤ (4159640297009/12500000000000 : ℝ)^3511
        have hw : |(4266236571/10000000000 : ℝ)|=(4266236571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021698171/10000000000 : ℝ)|^4535 ≤ (30834264824587/100000000000000 : ℝ)^3511
        have hw : |(4021698171/10000000000 : ℝ)|=(4021698171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904642853/2000000000 : ℝ)|^4535 ≤ (35888612780061/100000000000000 : ℝ)^3511
        have hw : |(904642853/2000000000 : ℝ)|=(904642853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_4 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1857298823/10000000000 : ℝ)*x 0 + (5216428569/10000000000 : ℝ)*x 1 + (2717085881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1857298823/10000000000 : ℝ)^4535 ≤ (11367046769389/100000000000000 : ℝ)^3511 := by
    have hnat : (1857298823 : ℕ)^4535*100000000000000^3511 ≤ 11367046769389^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857298823 10000000000 11367046769389 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216428569/10000000000 : ℝ)^4535 ≤ (21573163025059/50000000000000 : ℝ)^3511 := by
    have hnat : (5216428569 : ℕ)^4535*50000000000000^3511 ≤ 21573163025059^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216428569 10000000000 21573163025059 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717085881/5000000000 : ℝ)^4535 ≤ (45486627164833/100000000000000 : ℝ)^3511 := by
    have hnat : (2717085881 : ℕ)^4535*100000000000000^3511 ≤ 45486627164833^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717085881 5000000000 45486627164833 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1857298823/10000000000 : ℝ), (5216428569/10000000000 : ℝ), (2717085881/5000000000 : ℝ)] ![(11367046769389/100000000000000 : ℝ), (21573163025059/50000000000000 : ℝ), (45486627164833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1857298823/10000000000 : ℝ)|^4535 ≤ (11367046769389/100000000000000 : ℝ)^3511
        have hw : |(-1857298823/10000000000 : ℝ)|=(1857298823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216428569/10000000000 : ℝ)|^4535 ≤ (21573163025059/50000000000000 : ℝ)^3511
        have hw : |(5216428569/10000000000 : ℝ)|=(5216428569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717085881/5000000000 : ℝ)|^4535 ≤ (45486627164833/100000000000000 : ℝ)^3511
        have hw : |(2717085881/5000000000 : ℝ)|=(2717085881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_5 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661769359/1250000000 : ℝ)*x 0 + (-1751129767/10000000000 : ℝ)*x 1 + (5434171753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661769359/1250000000 : ℝ)^4535 ≤ (1759140786623/4000000000000 : ℝ)^3511 := by
    have hnat : (661769359 : ℕ)^4535*4000000000000^3511 ≤ 1759140786623^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661769359 1250000000 1759140786623 4000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1751129767/10000000000 : ℝ)^4535 ≤ (526742662383/5000000000000 : ℝ)^3511 := by
    have hnat : (1751129767 : ℕ)^4535*5000000000000^3511 ≤ 526742662383^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751129767 10000000000 526742662383 5000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434171753/10000000000 : ℝ)^4535 ≤ (45486627067527/100000000000000 : ℝ)^3511 := by
    have hnat : (5434171753 : ℕ)^4535*100000000000000^3511 ≤ 45486627067527^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434171753 10000000000 45486627067527 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661769359/1250000000 : ℝ), (-1751129767/10000000000 : ℝ), (5434171753/10000000000 : ℝ)] ![(1759140786623/4000000000000 : ℝ), (526742662383/5000000000000 : ℝ), (45486627067527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661769359/1250000000 : ℝ)|^4535 ≤ (1759140786623/4000000000000 : ℝ)^3511
        have hw : |(661769359/1250000000 : ℝ)|=(661769359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1751129767/10000000000 : ℝ)|^4535 ≤ (526742662383/5000000000000 : ℝ)^3511
        have hw : |(-1751129767/10000000000 : ℝ)|=(1751129767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434171753/10000000000 : ℝ)|^4535 ≤ (45486627067527/100000000000000 : ℝ)^3511
        have hw : |(5434171753/10000000000 : ℝ)|=(5434171753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_6 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323538707/2500000000 : ℝ)*x 0 + (5434171691/10000000000 : ℝ)*x 1 + (-437782479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323538707/2500000000 : ℝ)^4535 ≤ (8795703838693/20000000000000 : ℝ)^3511 := by
    have hnat : (1323538707 : ℕ)^4535*20000000000000^3511 ≤ 8795703838693^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323538707 2500000000 8795703838693 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434171691/10000000000 : ℝ)^4535 ≤ (45486626397197/100000000000000 : ℝ)^3511 := by
    have hnat : (5434171691 : ℕ)^4535*100000000000000^3511 ≤ 45486626397197^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434171691 10000000000 45486626397197 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437782479/2500000000 : ℝ)^4535 ≤ (2106970881097/20000000000000 : ℝ)^3511 := by
    have hnat : (437782479 : ℕ)^4535*20000000000000^3511 ≤ 2106970881097^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437782479 2500000000 2106970881097 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323538707/2500000000 : ℝ), (5434171691/10000000000 : ℝ), (-437782479/2500000000 : ℝ)] ![(8795703838693/20000000000000 : ℝ), (45486626397197/100000000000000 : ℝ), (2106970881097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323538707/2500000000 : ℝ)|^4535 ≤ (8795703838693/20000000000000 : ℝ)^3511
        have hw : |(1323538707/2500000000 : ℝ)|=(1323538707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434171691/10000000000 : ℝ)|^4535 ≤ (45486626397197/100000000000000 : ℝ)^3511
        have hw : |(5434171691/10000000000 : ℝ)|=(5434171691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437782479/2500000000 : ℝ)|^4535 ≤ (2106970881097/20000000000000 : ℝ)^3511
        have hw : |(-437782479/2500000000 : ℝ)|=(437782479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s3_7 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853261489/2000000000 : ℝ)*x 0 + (226028011/500000000 : ℝ)*x 1 + (4024372161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853261489/2000000000 : ℝ)^4535 ≤ (33277836437029/100000000000000 : ℝ)^3511 := by
    have hnat : (853261489 : ℕ)^4535*100000000000000^3511 ≤ 33277836437029^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853261489 2000000000 33277836437029 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226028011/500000000 : ℝ)^4535 ≤ (896535384973/2500000000000 : ℝ)^3511 := by
    have hnat : (226028011 : ℕ)^4535*2500000000000^3511 ≤ 896535384973^3511*500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226028011 500000000 896535384973 2500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024372161/10000000000 : ℝ)^4535 ≤ (15430374073429/50000000000000 : ℝ)^3511 := by
    have hnat : (4024372161 : ℕ)^4535*50000000000000^3511 ≤ 15430374073429^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024372161 10000000000 15430374073429 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853261489/2000000000 : ℝ), (226028011/500000000 : ℝ), (4024372161/10000000000 : ℝ)] ![(33277836437029/100000000000000 : ℝ), (896535384973/2500000000000 : ℝ), (15430374073429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853261489/2000000000 : ℝ)|^4535 ≤ (33277836437029/100000000000000 : ℝ)^3511
        have hw : |(853261489/2000000000 : ℝ)|=(853261489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226028011/500000000 : ℝ)|^4535 ≤ (896535384973/2500000000000 : ℝ)^3511
        have hw : |(226028011/500000000 : ℝ)|=(226028011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024372161/10000000000 : ℝ)|^4535 ≤ (15430374073429/50000000000000 : ℝ)^3511
        have hw : |(4024372161/10000000000 : ℝ)|=(4024372161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1519_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1597/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2721/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7773/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1597/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5247/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1597/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5247/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1597/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5247/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1597/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5247/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1597/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5247/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1597/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5247/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5247/50000 : ℝ) ^ (4533/1024 : ℝ) ≤ (4633862979782713/100000000000000000000 : ℝ) := by
    have hpowers : (5247/50000 : ℝ)^4533 ≤ (4633862979782713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5247 : ℕ)^4533*100000000000000000000^1024 ≤ 4633862979782713^1024*50000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5247 50000 4633862979782713 100000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5247/50000 : ℝ)) (X := (4633862979782713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1597/10000 : ℝ) ^ (4533/1024 : ℝ) ≤ (29731978722823539/100000000000000000000 : ℝ) := by
    have hpowers : (1597/10000 : ℝ)^4533 ≤ (29731978722823539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1597 : ℕ)^4533*100000000000000000000^1024 ≤ 29731978722823539^1024*10000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1597 10000 29731978722823539 100000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1597/10000 : ℝ)) (X := (29731978722823539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004633862979782713/50000000000000000000 : ℝ) ≤ (80001674795673/80000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (50004633862979782713/50000000000000000000 : ℝ)^1024 ≤ (80001674795673/80000000000000 : ℝ)^4533 := by
      have hnat : (50004633862979782713 : ℕ)^1024*80000000000000^4533 ≤ 80001674795673^4533*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004633862979782713 50000000000000000000 80001674795673 80000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80001674795673/80000000000000 : ℝ)) (X := (50004633862979782713/50000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008591460425651563/25000000000000000000 : ℝ) ≤ (5000388108780481/5000000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (25008591460425651563/25000000000000000000 : ℝ)^1024 ≤ (5000388108780481/5000000000000000 : ℝ)^4533 := by
      have hnat : (25008591460425651563 : ℕ)^1024*5000000000000000^4533 ≤ 5000388108780481^4533*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008591460425651563 25000000000000000000 5000388108780481 5000000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000388108780481/5000000000000000 : ℝ)) (X := (25008591460425651563/25000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029731978722823539/50000000000000000000 : ℝ) ≤ (10001343085662799/10000000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (50029731978722823539/50000000000000000000 : ℝ)^1024 ≤ (10001343085662799/10000000000000000 : ℝ)^4533 := by
      have hnat : (50029731978722823539 : ℕ)^1024*10000000000000000^4533 ≤ 10001343085662799^4533*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029731978722823539 50000000000000000000 10001343085662799 10000000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001343085662799/10000000000000000 : ℝ)) (X := (50029731978722823539/50000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4633862979782713/100000000000000000000 : ℝ) ≤ ((6843656121239601693/6845000000000000000 : ℝ)+2*(566868101837/547600000000000 : ℝ)*(5247/50000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (6843656121239601693/6845000000000000000 : ℝ)+2*(566868101837/547600000000000 : ℝ)*(5247/50000 : ℝ)=(80001674795673/80000000000000 : ℝ) by norm_num, show 1+2*(4633862979782713/100000000000000000000 : ℝ)=(50004633862979782713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29731978722823539/100000000000000000000 : ℝ)+(4633862979782713/100000000000000000000 : ℝ) ≤ ((6843656121239601693/6845000000000000000 : ℝ)+(566868101837/547600000000000 : ℝ)*((1597/10000 : ℝ)+(5247/50000 : ℝ)))^(4533/1024 : ℝ) := by
    rw [show (6843656121239601693/6845000000000000000 : ℝ)+(566868101837/547600000000000 : ℝ)*((1597/10000 : ℝ)+(5247/50000 : ℝ))=(5000388108780481/5000000000000000 : ℝ) by norm_num, show 1+(29731978722823539/100000000000000000000 : ℝ)+(4633862979782713/100000000000000000000 : ℝ)=(25008591460425651563/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29731978722823539/100000000000000000000 : ℝ) ≤ ((6843656121239601693/6845000000000000000 : ℝ)+2*(566868101837/547600000000000 : ℝ)*(1597/10000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (6843656121239601693/6845000000000000000 : ℝ)+2*(566868101837/547600000000000 : ℝ)*(1597/10000 : ℝ)=(10001343085662799/10000000000000000 : ℝ) by norm_num, show 1+2*(29731978722823539/100000000000000000000 : ℝ)=(50029731978722823539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6843656121239601693/6845000000000000000 : ℝ)*(X 1 0+X 2 0)+(566868101837/547600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (5247/50000 : ℝ)) (hi := (1597/10000 : ℝ)) (c := (6843656121239601693/6845000000000000000 : ℝ)) (alpha := (566868101837/547600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6843656121239601693/6845000000000000000 : ℝ)*(X 0 1+X 2 1)+(566868101837/547600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (5247/50000 : ℝ)) (hi := (1597/10000 : ℝ)) (c := (6843656121239601693/6845000000000000000 : ℝ)) (alpha := (566868101837/547600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6843656121239601693/6845000000000000000 : ℝ)*(X 0 2+X 1 2)+(566868101837/547600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (5247/50000 : ℝ)) (hi := (1597/10000 : ℝ)) (c := (6843656121239601693/6845000000000000000 : ℝ)) (alpha := (566868101837/547600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-185726793/1000000000 : ℝ)*X 0 0+(5435345197/10000000000 : ℝ)*X 0 1+(5215263839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351990037/10000000000 : ℝ)*X 1 0+(-394007607/2000000000 : ℝ)*X 1 1+(1043052821/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668998763/1250000000 : ℝ)*X 2 0+(5215264021/10000000000 : ℝ)*X 2 1+(-1970038057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266236571/10000000000 : ℝ)*X 0 0+(4021698171/10000000000 : ℝ)*X 0 1+(904642853/2000000000 : ℝ)*X 0 2+(4266236571/10000000000 : ℝ)*X 1 0+(4021698171/10000000000 : ℝ)*X 1 1+(904642853/2000000000 : ℝ)*X 1 2+(4266236571/10000000000 : ℝ)*X 2 0+(4021698171/10000000000 : ℝ)*X 2 1+(904642853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1857298823/10000000000 : ℝ)*X 0 0+(5216428569/10000000000 : ℝ)*X 0 1+(2717085881/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661769359/1250000000 : ℝ)*X 1 0+(-1751129767/10000000000 : ℝ)*X 1 1+(5434171753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323538707/2500000000 : ℝ)*X 2 0+(5434171691/10000000000 : ℝ)*X 2 1+(-437782479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853261489/2000000000 : ℝ)*X 0 0+(226028011/500000000 : ℝ)*X 0 1+(4024372161/10000000000 : ℝ)*X 0 2+(853261489/2000000000 : ℝ)*X 1 0+(226028011/500000000 : ℝ)*X 1 1+(4024372161/10000000000 : ℝ)*X 1 2+(853261489/2000000000 : ℝ)*X 2 0+(226028011/500000000 : ℝ)*X 2 1+(4024372161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (414339875137024448345581251/34225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1926615247/100000000000000 : ℝ)*(base19) + (231851237/12500000000000 : ℝ)*(base23) + (3443693/5000000000000 : ℝ)*(lower2) + (348173483/100000000000000 : ℝ)*(upper3) + (15108461/6250000000000 : ℝ)*(upper5) + (326891141639731/10000000000000 : ℝ)*(major0) + (326891141639731/10000000000000 : ℝ)*(major1) + (326891141639731/10000000000000 : ℝ)*(major2) + (4543807147206351/100000000000000 : ℝ)*(sp0) + (908767389499747/20000000000000 : ℝ)*(sp1) + (2271918509652043/50000000000000 : ℝ)*(sp2) + (1993967852054497/100000000000000 : ℝ)*(sp3) + (31726907631/100000000000000 : ℝ)*(sp4) + (15703081091/100000000000000 : ℝ)*(sp7) + (498495888783897/25000000000000 : ℝ)*(f.failure) + (2271919437056991/50000000000000 : ℝ)*(f.sum) + (3667907441987/547600000000000000000000000 : ℝ)*base66 + (263802551755902083/68450000000000000000000000000000 : ℝ)*base67 + (44111797039397917/68450000000000000000000000000000 : ℝ)*base70 + (182945696016102083/68450000000000000000000000000000 : ℝ)*base71 + (16296575068269/2738000000000000000000000000 : ℝ)*base74 + (915937109769802083/68450000000000000000000000000000 : ℝ)*base75 + (53115200702947917/68450000000000000000000000000000 : ℝ)*base78 + (405779240466902083/68450000000000000000000000000000 : ℝ)*base79 + (1800764437041/547600000000000000000000000 : ℝ)*base82 + (2510059/500000000000000000000 : ℝ)*base89 + (2510059/500000000000000000000 : ℝ)*base91 + (2510059/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1354329036276565294020311133/171125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28895459/1562500000000 : ℝ)*(base19) + (1048303313/50000000000000 : ℝ)*(base23) + (109356561/50000000000000 : ℝ)*(upper3) + (5549483/4000000000000 : ℝ)*(lower4) + (20041191/12500000000000 : ℝ)*(upper5) + (1651981639347991/50000000000000 : ℝ)*(major0) + (1651981639347991/50000000000000 : ℝ)*(major1) + (1651981639347991/50000000000000 : ℝ)*(major2) + (1774482519/6250000000000 : ℝ)*(sp1) + (15267253523/50000000000000 : ℝ)*(sp2) + (4592561664414719/100000000000000 : ℝ)*(sp4) + (4592531423385039/100000000000000 : ℝ)*(sp5) + (4592529033301047/100000000000000 : ℝ)*(sp6) + (1007682314584159/50000000000000 : ℝ)*(sp7) + (1007682314584159/50000000000000 : ℝ)*(f.failure) + (4592561664414719/100000000000000 : ℝ)*(f.sum) + (14447419587097/13690000000000000000000000000 : ℝ)*base65 + (3037705829503336263/342250000000000000000000000000000 : ℝ)*base67 + (3372582736042086263/342250000000000000000000000000000 : ℝ)*base69 + (1861364619389586263/342250000000000000000000000000000 : ℝ)*base71 + (18293766997637/13690000000000000000000000000 : ℝ)*base73 + (4405997572561836263/342250000000000000000000000000000 : ℝ)*base75 + (1104853013930586263/342250000000000000000000000000000 : ℝ)*base77 + (6115510339626336263/342250000000000000000000000000000 : ℝ)*base79 + (2222636315907/13690000000000000000000000000 : ℝ)*base81 + (4500227/1000000000000000000000 : ℝ)*base90 + (4500227/1000000000000000000000 : ℝ)*base92 + (4500227/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1519_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1597/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7773/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1519_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1519_s4_0 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1857672059/10000000000 : ℝ)*x 0 + (2716341589/5000000000 : ℝ)*x 1 + (1304414683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1857672059/10000000000 : ℝ)^4535 ≤ (11369997357431/100000000000000 : ℝ)^3511 := by
    have hnat : (1857672059 : ℕ)^4535*100000000000000^3511 ≤ 11369997357431^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857672059 10000000000 11369997357431 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716341589/5000000000 : ℝ)^4535 ≤ (45470533578567/100000000000000 : ℝ)^3511 := by
    have hnat : (2716341589 : ℕ)^4535*100000000000000^3511 ≤ 45470533578567^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716341589 5000000000 45470533578567 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304414683/2500000000 : ℝ)^4535 ≤ (21579734526647/50000000000000 : ℝ)^3511 := by
    have hnat : (1304414683 : ℕ)^4535*50000000000000^3511 ≤ 21579734526647^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304414683 2500000000 21579734526647 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1857672059/10000000000 : ℝ), (2716341589/5000000000 : ℝ), (1304414683/2500000000 : ℝ)] ![(11369997357431/100000000000000 : ℝ), (45470533578567/100000000000000 : ℝ), (21579734526647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1857672059/10000000000 : ℝ)|^4535 ≤ (11369997357431/100000000000000 : ℝ)^3511
        have hw : |(-1857672059/10000000000 : ℝ)|=(1857672059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716341589/5000000000 : ℝ)|^4535 ≤ (45470533578567/100000000000000 : ℝ)^3511
        have hw : |(2716341589/5000000000 : ℝ)|=(2716341589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304414683/2500000000 : ℝ)|^4535 ≤ (21579734526647/50000000000000 : ℝ)^3511
        have hw : |(1304414683/2500000000 : ℝ)|=(1304414683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_1 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133782303/250000000 : ℝ)*x 0 + (-122986879/625000000 : ℝ)*x 1 + (5217659159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133782303/250000000 : ℝ)^4535 ≤ (22296275821903/50000000000000 : ℝ)^3511 := by
    have hnat : (133782303 : ℕ)^4535*50000000000000^3511 ≤ 22296275821903^3511*250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133782303 250000000 22296275821903 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122986879/625000000 : ℝ)^4535 ≤ (12247974721109/100000000000000 : ℝ)^3511 := by
    have hnat : (122986879 : ℕ)^4535*100000000000000^3511 ≤ 12247974721109^3511*625000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122986879 625000000 12247974721109 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217659159/10000000000 : ℝ)^4535 ≤ (43159473615499/100000000000000 : ℝ)^3511 := by
    have hnat : (5217659159 : ℕ)^4535*100000000000000^3511 ≤ 43159473615499^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217659159 10000000000 43159473615499 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133782303/250000000 : ℝ), (-122986879/625000000 : ℝ), (5217659159/10000000000 : ℝ)] ![(22296275821903/50000000000000 : ℝ), (12247974721109/100000000000000 : ℝ), (43159473615499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133782303/250000000 : ℝ)|^4535 ≤ (22296275821903/50000000000000 : ℝ)^3511
        have hw : |(133782303/250000000 : ℝ)|=(133782303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122986879/625000000 : ℝ)|^4535 ≤ (12247974721109/100000000000000 : ℝ)^3511
        have hw : |(-122986879/625000000 : ℝ)|=(122986879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217659159/10000000000 : ℝ)|^4535 ≤ (43159473615499/100000000000000 : ℝ)^3511
        have hw : |(5217659159/10000000000 : ℝ)|=(5217659159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_2 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668911551/1250000000 : ℝ)*x 0 + (5217658889/10000000000 : ℝ)*x 1 + (-983895019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668911551/1250000000 : ℝ)^4535 ≤ (4459255474367/10000000000000 : ℝ)^3511 := by
    have hnat : (668911551 : ℕ)^4535*10000000000000^3511 ≤ 4459255474367^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668911551 1250000000 4459255474367 10000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217658889/10000000000 : ℝ)^4535 ≤ (43159470730733/100000000000000 : ℝ)^3511 := by
    have hnat : (5217658889 : ℕ)^4535*100000000000000^3511 ≤ 43159470730733^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217658889 10000000000 43159470730733 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983895019/5000000000 : ℝ)^4535 ≤ (12247974512081/100000000000000 : ℝ)^3511 := by
    have hnat : (983895019 : ℕ)^4535*100000000000000^3511 ≤ 12247974512081^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983895019 5000000000 12247974512081 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668911551/1250000000 : ℝ), (5217658889/10000000000 : ℝ), (-983895019/5000000000 : ℝ)] ![(4459255474367/10000000000000 : ℝ), (43159470730733/100000000000000 : ℝ), (12247974512081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668911551/1250000000 : ℝ)|^4535 ≤ (4459255474367/10000000000000 : ℝ)^3511
        have hw : |(668911551/1250000000 : ℝ)|=(668911551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217658889/10000000000 : ℝ)|^4535 ≤ (43159470730733/100000000000000 : ℝ)^3511
        have hw : |(5217658889/10000000000 : ℝ)|=(5217658889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983895019/5000000000 : ℝ)|^4535 ≤ (12247974512081/100000000000000 : ℝ)^3511
        have hw : |(-983895019/5000000000 : ℝ)|=(983895019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_3 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266489403/10000000000 : ℝ)*x 0 + (4027431537/10000000000 : ℝ)*x 1 + (451742329/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266489403/10000000000 : ℝ)^4535 ≤ (6655933938721/20000000000000 : ℝ)^3511 := by
    have hnat : (4266489403 : ℕ)^4535*20000000000000^3511 ≤ 6655933938721^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266489403 10000000000 6655933938721 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027431537/10000000000 : ℝ)^4535 ≤ (3861381830701/12500000000000 : ℝ)^3511 := by
    have hnat : (4027431537 : ℕ)^4535*12500000000000^3511 ≤ 3861381830701^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027431537 10000000000 3861381830701 12500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451742329/1000000000 : ℝ)^4535 ≤ (35829275648499/100000000000000 : ℝ)^3511 := by
    have hnat : (451742329 : ℕ)^4535*100000000000000^3511 ≤ 35829275648499^3511*1000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451742329 1000000000 35829275648499 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266489403/10000000000 : ℝ), (4027431537/10000000000 : ℝ), (451742329/1000000000 : ℝ)] ![(6655933938721/20000000000000 : ℝ), (3861381830701/12500000000000 : ℝ), (35829275648499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266489403/10000000000 : ℝ)|^4535 ≤ (6655933938721/20000000000000 : ℝ)^3511
        have hw : |(4266489403/10000000000 : ℝ)|=(4266489403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027431537/10000000000 : ℝ)|^4535 ≤ (3861381830701/12500000000000 : ℝ)^3511
        have hw : |(4027431537/10000000000 : ℝ)|=(4027431537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451742329/1000000000 : ℝ)|^4535 ≤ (35829275648499/100000000000000 : ℝ)^3511
        have hw : |(451742329/1000000000 : ℝ)|=(451742329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_4 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464425223/2500000000 : ℝ)*x 0 + (5218770669/10000000000 : ℝ)*x 1 + (1357890777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464425223/2500000000 : ℝ)^4535 ≤ (2274045060331/20000000000000 : ℝ)^3511 := by
    have hnat : (464425223 : ℕ)^4535*20000000000000^3511 ≤ 2274045060331^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464425223 2500000000 2274045060331 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218770669/10000000000 : ℝ)^4535 ≤ (43171349713167/100000000000000 : ℝ)^3511 := by
    have hnat : (5218770669 : ℕ)^4535*100000000000000^3511 ≤ 43171349713167^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218770669 10000000000 43171349713167 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357890777/2500000000 : ℝ)^4535 ≤ (45458424969979/100000000000000 : ℝ)^3511 := by
    have hnat : (1357890777 : ℕ)^4535*100000000000000^3511 ≤ 45458424969979^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357890777 2500000000 45458424969979 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464425223/2500000000 : ℝ), (5218770669/10000000000 : ℝ), (1357890777/2500000000 : ℝ)] ![(2274045060331/20000000000000 : ℝ), (43171349713167/100000000000000 : ℝ), (45458424969979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464425223/2500000000 : ℝ)|^4535 ≤ (2274045060331/20000000000000 : ℝ)^3511
        have hw : |(-464425223/2500000000 : ℝ)|=(464425223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218770669/10000000000 : ℝ)|^4535 ≤ (43171349713167/100000000000000 : ℝ)^3511
        have hw : |(5218770669/10000000000 : ℝ)|=(5218770669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357890777/2500000000 : ℝ)|^4535 ≤ (45458424969979/100000000000000 : ℝ)^3511
        have hw : |(1357890777/2500000000 : ℝ)|=(1357890777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_5 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529478707/1000000000 : ℝ)*x 0 + (-1753885493/10000000000 : ℝ)*x 1 + (5431563107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529478707/1000000000 : ℝ)^4535 ≤ (43985303123053/100000000000000 : ℝ)^3511 := by
    have hnat : (529478707 : ℕ)^4535*100000000000000^3511 ≤ 43985303123053^3511*1000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529478707 1000000000 43985303123053 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1753885493/10000000000 : ℝ)^4535 ≤ (1055627190641/10000000000000 : ℝ)^3511 := by
    have hnat : (1753885493 : ℕ)^4535*10000000000000^3511 ≤ 1055627190641^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753885493 10000000000 1055627190641 10000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431563107/10000000000 : ℝ)^4535 ≤ (45458424959169/100000000000000 : ℝ)^3511 := by
    have hnat : (5431563107 : ℕ)^4535*100000000000000^3511 ≤ 45458424959169^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431563107 10000000000 45458424959169 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529478707/1000000000 : ℝ), (-1753885493/10000000000 : ℝ), (5431563107/10000000000 : ℝ)] ![(43985303123053/100000000000000 : ℝ), (1055627190641/10000000000000 : ℝ), (45458424959169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529478707/1000000000 : ℝ)|^4535 ≤ (43985303123053/100000000000000 : ℝ)^3511
        have hw : |(529478707/1000000000 : ℝ)|=(529478707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1753885493/10000000000 : ℝ)|^4535 ≤ (1055627190641/10000000000000 : ℝ)^3511
        have hw : |(-1753885493/10000000000 : ℝ)|=(1753885493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431563107/10000000000 : ℝ)|^4535 ≤ (45458424959169/100000000000000 : ℝ)^3511
        have hw : |(5431563107/10000000000 : ℝ)|=(5431563107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_6 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330924193/625000000 : ℝ)*x 0 + (5431563097/10000000000 : ℝ)*x 1 + (-876942741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330924193/625000000 : ℝ)^4535 ≤ (10996325829049/25000000000000 : ℝ)^3511 := by
    have hnat : (330924193 : ℕ)^4535*25000000000000^3511 ≤ 10996325829049^3511*625000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330924193 625000000 10996325829049 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431563097/10000000000 : ℝ)^4535 ≤ (22729212425533/50000000000000 : ℝ)^3511 := by
    have hnat : (5431563097 : ℕ)^4535*50000000000000^3511 ≤ 22729212425533^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431563097 10000000000 22729212425533 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876942741/5000000000 : ℝ)^4535 ≤ (5278135910447/50000000000000 : ℝ)^3511 := by
    have hnat : (876942741 : ℕ)^4535*50000000000000^3511 ≤ 5278135910447^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876942741 5000000000 5278135910447 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330924193/625000000 : ℝ), (5431563097/10000000000 : ℝ), (-876942741/5000000000 : ℝ)] ![(10996325829049/25000000000000 : ℝ), (22729212425533/50000000000000 : ℝ), (5278135910447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330924193/625000000 : ℝ)|^4535 ≤ (10996325829049/25000000000000 : ℝ)^3511
        have hw : |(330924193/625000000 : ℝ)|=(330924193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431563097/10000000000 : ℝ)|^4535 ≤ (22729212425533/50000000000000 : ℝ)^3511
        have hw : |(5431563097/10000000000 : ℝ)|=(5431563097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876942741/5000000000 : ℝ)|^4535 ≤ (5278135910447/50000000000000 : ℝ)^3511
        have hw : |(-876942741/5000000000 : ℝ)|=(876942741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s4_7 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266555621/10000000000 : ℝ)*x 0 + (2257444823/5000000000 : ℝ)*x 1 + (4029983667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266555621/10000000000 : ℝ)^4535 ≤ (2080021053527/6250000000000 : ℝ)^3511 := by
    have hnat : (4266555621 : ℕ)^4535*6250000000000^3511 ≤ 2080021053527^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266555621 10000000000 2080021053527 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257444823/5000000000 : ℝ)^4535 ≤ (35803321680219/100000000000000 : ℝ)^3511 := by
    have hnat : (2257444823 : ℕ)^4535*100000000000000^3511 ≤ 35803321680219^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257444823 5000000000 35803321680219 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029983667/10000000000 : ℝ)^4535 ≤ (15458170724987/50000000000000 : ℝ)^3511 := by
    have hnat : (4029983667 : ℕ)^4535*50000000000000^3511 ≤ 15458170724987^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029983667 10000000000 15458170724987 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266555621/10000000000 : ℝ), (2257444823/5000000000 : ℝ), (4029983667/10000000000 : ℝ)] ![(2080021053527/6250000000000 : ℝ), (35803321680219/100000000000000 : ℝ), (15458170724987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266555621/10000000000 : ℝ)|^4535 ≤ (2080021053527/6250000000000 : ℝ)^3511
        have hw : |(4266555621/10000000000 : ℝ)|=(4266555621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257444823/5000000000 : ℝ)|^4535 ≤ (35803321680219/100000000000000 : ℝ)^3511
        have hw : |(2257444823/5000000000 : ℝ)|=(2257444823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029983667/10000000000 : ℝ)|^4535 ≤ (15458170724987/50000000000000 : ℝ)^3511
        have hw : |(4029983667/10000000000 : ℝ)|=(4029983667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1519_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7773/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1367/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7773/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7773/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7773/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7773/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7773/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7773/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2721/25000 : ℝ) ^ (4533/1024 : ℝ) ≤ (136155792556733/2500000000000000000 : ℝ) := by
    have hpowers : (2721/25000 : ℝ)^4533 ≤ (136155792556733/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2721 : ℕ)^4533*2500000000000000000^1024 ≤ 136155792556733^1024*25000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2721 25000 136155792556733 2500000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2721/25000 : ℝ)) (X := (136155792556733/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7773/50000 : ℝ) ^ (4533/1024 : ℝ) ≤ (26393172886999497/100000000000000000000 : ℝ) := by
    have hpowers : (7773/50000 : ℝ)^4533 ≤ (26393172886999497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7773 : ℕ)^4533*100000000000000000000^1024 ≤ 26393172886999497^1024*50000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7773 50000 26393172886999497 100000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7773/50000 : ℝ)) (X := (26393172886999497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250136155792556733/1250000000000000000 : ℝ) ≤ (2500061512311473/2500000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (1250136155792556733/1250000000000000000 : ℝ)^1024 ≤ (2500061512311473/2500000000000000 : ℝ)^4533 := by
      have hnat : (1250136155792556733 : ℕ)^1024*2500000000000000^4533 ≤ 2500061512311473^4533*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250136155792556733 1250000000000000000 2500061512311473 2500000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500061512311473/2500000000000000 : ℝ)) (X := (1250136155792556733/1250000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031839404589268817/100000000000000000000 : ℝ) ≤ (2500179790057197/2500000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (100031839404589268817/100000000000000000000 : ℝ)^1024 ≤ (2500179790057197/2500000000000000 : ℝ)^4533 := by
      have hnat : (100031839404589268817 : ℕ)^1024*2500000000000000^4533 ≤ 2500179790057197^4533*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031839404589268817 100000000000000000000 2500179790057197 2500000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500179790057197/2500000000000000 : ℝ)) (X := (100031839404589268817/100000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026393172886999497/50000000000000000000 : ℝ) ≤ (2500298067802921/2500000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (50026393172886999497/50000000000000000000 : ℝ)^1024 ≤ (2500298067802921/2500000000000000 : ℝ)^4533 := by
      have hnat : (50026393172886999497 : ℕ)^1024*2500000000000000^4533 ≤ 2500298067802921^4533*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026393172886999497 50000000000000000000 2500298067802921 2500000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500298067802921/2500000000000000 : ℝ)) (X := (50026393172886999497/50000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(136155792556733/2500000000000000000 : ℝ) ≤ ((1942118683404527849/1942500000000000000 : ℝ)+2*(29569436431/29137500000000 : ℝ)*(2721/25000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (1942118683404527849/1942500000000000000 : ℝ)+2*(29569436431/29137500000000 : ℝ)*(2721/25000 : ℝ)=(2500061512311473/2500000000000000 : ℝ) by norm_num, show 1+2*(136155792556733/2500000000000000000 : ℝ)=(1250136155792556733/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26393172886999497/100000000000000000000 : ℝ)+(136155792556733/2500000000000000000 : ℝ) ≤ ((1942118683404527849/1942500000000000000 : ℝ)+(29569436431/29137500000000 : ℝ)*((7773/50000 : ℝ)+(2721/25000 : ℝ)))^(4533/1024 : ℝ) := by
    rw [show (1942118683404527849/1942500000000000000 : ℝ)+(29569436431/29137500000000 : ℝ)*((7773/50000 : ℝ)+(2721/25000 : ℝ))=(2500179790057197/2500000000000000 : ℝ) by norm_num, show 1+(26393172886999497/100000000000000000000 : ℝ)+(136155792556733/2500000000000000000 : ℝ)=(100031839404589268817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26393172886999497/100000000000000000000 : ℝ) ≤ ((1942118683404527849/1942500000000000000 : ℝ)+2*(29569436431/29137500000000 : ℝ)*(7773/50000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (1942118683404527849/1942500000000000000 : ℝ)+2*(29569436431/29137500000000 : ℝ)*(7773/50000 : ℝ)=(2500298067802921/2500000000000000 : ℝ) by norm_num, show 1+2*(26393172886999497/100000000000000000000 : ℝ)=(50026393172886999497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1942118683404527849/1942500000000000000 : ℝ)*(X 1 0+X 2 0)+(29569436431/29137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (7773/50000 : ℝ)) (c := (1942118683404527849/1942500000000000000 : ℝ)) (alpha := (29569436431/29137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1942118683404527849/1942500000000000000 : ℝ)*(X 0 1+X 2 1)+(29569436431/29137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (7773/50000 : ℝ)) (c := (1942118683404527849/1942500000000000000 : ℝ)) (alpha := (29569436431/29137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1942118683404527849/1942500000000000000 : ℝ)*(X 0 2+X 1 2)+(29569436431/29137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (7773/50000 : ℝ)) (c := (1942118683404527849/1942500000000000000 : ℝ)) (alpha := (29569436431/29137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1857672059/10000000000 : ℝ)*X 0 0+(2716341589/5000000000 : ℝ)*X 0 1+(1304414683/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133782303/250000000 : ℝ)*X 1 0+(-122986879/625000000 : ℝ)*X 1 1+(5217659159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668911551/1250000000 : ℝ)*X 2 0+(5217658889/10000000000 : ℝ)*X 2 1+(-983895019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266489403/10000000000 : ℝ)*X 0 0+(4027431537/10000000000 : ℝ)*X 0 1+(451742329/1000000000 : ℝ)*X 0 2+(4266489403/10000000000 : ℝ)*X 1 0+(4027431537/10000000000 : ℝ)*X 1 1+(451742329/1000000000 : ℝ)*X 1 2+(4266489403/10000000000 : ℝ)*X 2 0+(4027431537/10000000000 : ℝ)*X 2 1+(451742329/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-464425223/2500000000 : ℝ)*X 0 0+(5218770669/10000000000 : ℝ)*X 0 1+(1357890777/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529478707/1000000000 : ℝ)*X 1 0+(-1753885493/10000000000 : ℝ)*X 1 1+(5431563107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330924193/625000000 : ℝ)*X 2 0+(5431563097/10000000000 : ℝ)*X 2 1+(-876942741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4266555621/10000000000 : ℝ)*X 0 0+(2257444823/5000000000 : ℝ)*X 0 1+(4029983667/10000000000 : ℝ)*X 0 2+(4266555621/10000000000 : ℝ)*X 1 0+(2257444823/5000000000 : ℝ)*X 1 1+(4029983667/10000000000 : ℝ)*X 1 2+(4266555621/10000000000 : ℝ)*X 2 0+(2257444823/5000000000 : ℝ)*X 2 1+(4029983667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303946477617920638579797617/48562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7112427/3125000000000 : ℝ)*(base19) + (73379313/20000000000000 : ℝ)*(base23) + (140340021/100000000000000 : ℝ)*(upper3) + (29697861/50000000000000 : ℝ)*(upper4) + (64123201/50000000000000 : ℝ)*(upper5) + (3345751030983689/100000000000000 : ℝ)*(major0) + (3345751030983689/100000000000000 : ℝ)*(major1) + (3345751030983689/100000000000000 : ℝ)*(major2) + (4650639553915897/100000000000000 : ℝ)*(sp0) + (1162661784409881/25000000000000 : ℝ)*(sp1) + (4650646998340623/100000000000000 : ℝ)*(sp2) + (255106505313063/12500000000000 : ℝ)*(sp3) + (7811321291/100000000000000 : ℝ)*(sp4) + (38212447/1562500000000 : ℝ)*(sp7) + (255106811012639/12500000000000 : ℝ)*(f.failure) + (1162661841309297/25000000000000 : ℝ)*(f.sum) + (66879406730497/11655000000000000000000000000 : ℝ)*base65 + (312202656109259269/83250000000000000000000000000000 : ℝ)*base67 + (969733053606509269/83250000000000000000000000000000 : ℝ)*base69 + (445877364342509269/83250000000000000000000000000000 : ℝ)*base71 + (3225285338767/728437500000000000000000000 : ℝ)*base73 + (56972986286490731/83250000000000000000000000000000 : ℝ)*base76 + (89888767284509269/83250000000000000000000000000000 : ℝ)*base77 + (929829952067759269/83250000000000000000000000000000 : ℝ)*base79 + (24317364952631/5827500000000000000000000000 : ℝ)*base81 + (1165667/250000000000000000000 : ℝ)*base90 + (1165667/250000000000000000000 : ℝ)*base92 + (1165667/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148306971148625619792791229/32375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183285887/25000000000000 : ℝ)*(base19) + (4139133/500000000000 : ℝ)*(base23) + (92555183/100000000000000 : ℝ)*(upper3) + (35209819/100000000000000 : ℝ)*(lower4) + (50754857/50000000000000 : ℝ)*(upper5) + (3380835110423793/100000000000000 : ℝ)*(major0) + (3380835110423793/100000000000000 : ℝ)*(major1) + (3380835110423793/100000000000000 : ℝ)*(major2) + (282728393/2500000000000 : ℝ)*(sp1) + (12453026429/100000000000000 : ℝ)*(sp2) + (4699414854076969/100000000000000 : ℝ)*(sp4) + (4699402811797701/100000000000000 : ℝ)*(sp5) + (4699401573223939/100000000000000 : ℝ)*(sp6) + (1031127607036797/50000000000000 : ℝ)*(sp7) + (1031127607036797/50000000000000 : ℝ)*(f.failure) + (4699414854076969/100000000000000 : ℝ)*(f.sum) + (6476937377789/1942500000000000000000000000 : ℝ)*base65 + (239486605103808751/27750000000000000000000000000000 : ℝ)*base67 + (246212681600058751/27750000000000000000000000000000 : ℝ)*base69 + (308334511641558751/27750000000000000000000000000000 : ℝ)*base71 + (20280772925953/3885000000000000000000000000 : ℝ)*base73 + (4282164428808751/27750000000000000000000000000000 : ℝ)*base75 + (260501886758058751/27750000000000000000000000000000 : ℝ)*base77 + (469047530970558751/27750000000000000000000000000000 : ℝ)*base79 + (6026848915679/1942500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (10273641/1000000000000000000000 : ℝ)*base90 + (10273641/1000000000000000000000 : ℝ)*base92 + (10273641/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1519_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7773/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1519_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1519_s5_0 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116107521/625000000 : ℝ)*x 0 + (43458881/80000000 : ℝ)*x 1 + (1043589977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116107521/625000000 : ℝ)^4535 ≤ (710648688757/6250000000000 : ℝ)^3511 := by
    have hnat : (116107521 : ℕ)^4535*6250000000000^3511 ≤ 710648688757^3511*625000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116107521 625000000 710648688757 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43458881/80000000 : ℝ)^4535 ≤ (9093408222579/20000000000000 : ℝ)^3511 := by
    have hnat : (43458881 : ℕ)^4535*20000000000000^3511 ≤ 9093408222579^3511*80000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43458881 80000000 9093408222579 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043589977/2000000000 : ℝ)^4535 ≤ (43162579850417/100000000000000 : ℝ)^3511 := by
    have hnat : (1043589977 : ℕ)^4535*100000000000000^3511 ≤ 43162579850417^3511*2000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043589977 2000000000 43162579850417 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116107521/625000000 : ℝ), (43458881/80000000 : ℝ), (1043589977/2000000000 : ℝ)] ![(710648688757/6250000000000 : ℝ), (9093408222579/20000000000000 : ℝ), (43162579850417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116107521/625000000 : ℝ)|^4535 ≤ (710648688757/6250000000000 : ℝ)^3511
        have hw : |(-116107521/625000000 : ℝ)|=(116107521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43458881/80000000 : ℝ)|^4535 ≤ (9093408222579/20000000000000 : ℝ)^3511
        have hw : |(43458881/80000000 : ℝ)|=(43458881/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043589977/2000000000 : ℝ)|^4535 ≤ (43162579850417/100000000000000 : ℝ)^3511
        have hw : |(1043589977/2000000000 : ℝ)|=(1043589977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_1 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668901011/1250000000 : ℝ)*x 0 + (-491879063/2500000000 : ℝ)*x 1 + (65224373/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668901011/1250000000 : ℝ)^4535 ≤ (22295823587251/50000000000000 : ℝ)^3511 := by
    have hnat : (668901011 : ℕ)^4535*50000000000000^3511 ≤ 22295823587251^3511*1250000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668901011 1250000000 22295823587251 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491879063/2500000000 : ℝ)^4535 ≤ (12245773439301/100000000000000 : ℝ)^3511 := by
    have hnat : (491879063 : ℕ)^4535*100000000000000^3511 ≤ 12245773439301^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491879063 2500000000 12245773439301 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65224373/125000000 : ℝ)^4535 ≤ (8632515873923/20000000000000 : ℝ)^3511 := by
    have hnat : (65224373 : ℕ)^4535*20000000000000^3511 ≤ 8632515873923^3511*125000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65224373 125000000 8632515873923 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668901011/1250000000 : ℝ), (-491879063/2500000000 : ℝ), (65224373/125000000 : ℝ)] ![(22295823587251/50000000000000 : ℝ), (12245773439301/100000000000000 : ℝ), (8632515873923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668901011/1250000000 : ℝ)|^4535 ≤ (22295823587251/50000000000000 : ℝ)^3511
        have hw : |(668901011/1250000000 : ℝ)|=(668901011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491879063/2500000000 : ℝ)|^4535 ≤ (12245773439301/100000000000000 : ℝ)^3511
        have hw : |(-491879063/2500000000 : ℝ)|=(491879063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65224373/125000000 : ℝ)|^4535 ≤ (8632515873923/20000000000000 : ℝ)^3511
        have hw : |(65224373/125000000 : ℝ)|=(65224373/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_2 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351208029/10000000000 : ℝ)*x 0 + (5217949909/10000000000 : ℝ)*x 1 + (-983758119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351208029/10000000000 : ℝ)^4535 ≤ (44591646539463/100000000000000 : ℝ)^3511 := by
    have hnat : (5351208029 : ℕ)^4535*100000000000000^3511 ≤ 44591646539463^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351208029 10000000000 44591646539463 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217949909/10000000000 : ℝ)^4535 ≤ (8632516021369/20000000000000 : ℝ)^3511 := by
    have hnat : (5217949909 : ℕ)^4535*20000000000000^3511 ≤ 8632516021369^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217949909 10000000000 8632516021369 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983758119/5000000000 : ℝ)^4535 ≤ (382680416461/3125000000000 : ℝ)^3511 := by
    have hnat : (983758119 : ℕ)^4535*3125000000000^3511 ≤ 382680416461^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983758119 5000000000 382680416461 3125000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351208029/10000000000 : ℝ), (5217949909/10000000000 : ℝ), (-983758119/5000000000 : ℝ)] ![(44591646539463/100000000000000 : ℝ), (8632516021369/20000000000000 : ℝ), (382680416461/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351208029/10000000000 : ℝ)|^4535 ≤ (44591646539463/100000000000000 : ℝ)^3511
        have hw : |(5351208029/10000000000 : ℝ)|=(5351208029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217949909/10000000000 : ℝ)|^4535 ≤ (8632516021369/20000000000000 : ℝ)^3511
        have hw : |(5217949909/10000000000 : ℝ)|=(5217949909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983758119/5000000000 : ℝ)|^4535 ≤ (382680416461/3125000000000 : ℝ)^3511
        have hw : |(-983758119/5000000000 : ℝ)|=(983758119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_3 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066629973/2500000000 : ℝ)*x 0 + (4028127691/10000000000 : ℝ)*x 1 + (2258360021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066629973/2500000000 : ℝ)^4535 ≤ (33279976877491/100000000000000 : ℝ)^3511 := by
    have hnat : (1066629973 : ℕ)^4535*100000000000000^3511 ≤ 33279976877491^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066629973 2500000000 33279976877491 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028127691/10000000000 : ℝ)^4535 ≤ (772448793949/2500000000000 : ℝ)^3511 := by
    have hnat : (4028127691 : ℕ)^4535*2500000000000^3511 ≤ 772448793949^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028127691 10000000000 772448793949 2500000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258360021/5000000000 : ℝ)^4535 ≤ (8955517834801/25000000000000 : ℝ)^3511 := by
    have hnat : (2258360021 : ℕ)^4535*25000000000000^3511 ≤ 8955517834801^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258360021 5000000000 8955517834801 25000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066629973/2500000000 : ℝ), (4028127691/10000000000 : ℝ), (2258360021/5000000000 : ℝ)] ![(33279976877491/100000000000000 : ℝ), (772448793949/2500000000000 : ℝ), (8955517834801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066629973/2500000000 : ℝ)|^4535 ≤ (33279976877491/100000000000000 : ℝ)^3511
        have hw : |(1066629973/2500000000 : ℝ)|=(1066629973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028127691/10000000000 : ℝ)|^4535 ≤ (772448793949/2500000000000 : ℝ)^3511
        have hw : |(4028127691/10000000000 : ℝ)|=(4028127691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258360021/5000000000 : ℝ)|^4535 ≤ (8955517834801/25000000000000 : ℝ)^3511
        have hw : |(2258360021/5000000000 : ℝ)|=(2258360021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_4 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1857749041/10000000000 : ℝ)*x 0 + (260952773/500000000 : ℝ)*x 1 + (5431246401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1857749041/10000000000 : ℝ)^4535 ≤ (710662872133/6250000000000 : ℝ)^3511 := by
    have hnat : (1857749041 : ℕ)^4535*6250000000000^3511 ≤ 710662872133^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857749041 10000000000 710662872133 6250000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260952773/500000000 : ℝ)^4535 ≤ (43174392724657/100000000000000 : ℝ)^3511 := by
    have hnat : (260952773 : ℕ)^4535*100000000000000^3511 ≤ 43174392724657^3511*500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260952773 500000000 43174392724657 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431246401/10000000000 : ℝ)^4535 ≤ (45455001315047/100000000000000 : ℝ)^3511 := by
    have hnat : (5431246401 : ℕ)^4535*100000000000000^3511 ≤ 45455001315047^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431246401 10000000000 45455001315047 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1857749041/10000000000 : ℝ), (260952773/500000000 : ℝ), (5431246401/10000000000 : ℝ)] ![(710662872133/6250000000000 : ℝ), (43174392724657/100000000000000 : ℝ), (45455001315047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1857749041/10000000000 : ℝ)|^4535 ≤ (710662872133/6250000000000 : ℝ)^3511
        have hw : |(-1857749041/10000000000 : ℝ)|=(1857749041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260952773/500000000 : ℝ)|^4535 ≤ (43174392724657/100000000000000 : ℝ)^3511
        have hw : |(260952773/500000000 : ℝ)|=(260952773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431246401/10000000000 : ℝ)|^4535 ≤ (45455001315047/100000000000000 : ℝ)^3511
        have hw : |(5431246401/10000000000 : ℝ)|=(5431246401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_5 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323715997/2500000000 : ℝ)*x 0 + (-1754219743/10000000000 : ℝ)*x 1 + (5431246373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323715997/2500000000 : ℝ)^4535 ≤ (2199306423301/5000000000000 : ℝ)^3511 := by
    have hnat : (1323715997 : ℕ)^4535*5000000000000^3511 ≤ 2199306423301^3511*2500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323715997 2500000000 2199306423301 5000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1754219743/10000000000 : ℝ)^4535 ≤ (5279435252741/50000000000000 : ℝ)^3511 := by
    have hnat : (1754219743 : ℕ)^4535*50000000000000^3511 ≤ 5279435252741^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754219743 10000000000 5279435252741 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431246373/10000000000 : ℝ)^4535 ≤ (9091000202473/20000000000000 : ℝ)^3511 := by
    have hnat : (5431246373 : ℕ)^4535*20000000000000^3511 ≤ 9091000202473^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431246373 10000000000 9091000202473 20000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323715997/2500000000 : ℝ), (-1754219743/10000000000 : ℝ), (5431246373/10000000000 : ℝ)] ![(2199306423301/5000000000000 : ℝ), (5279435252741/50000000000000 : ℝ), (9091000202473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323715997/2500000000 : ℝ)|^4535 ≤ (2199306423301/5000000000000 : ℝ)^3511
        have hw : |(1323715997/2500000000 : ℝ)|=(1323715997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1754219743/10000000000 : ℝ)|^4535 ≤ (5279435252741/50000000000000 : ℝ)^3511
        have hw : |(-1754219743/10000000000 : ℝ)|=(1754219743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431246373/10000000000 : ℝ)|^4535 ≤ (9091000202473/20000000000000 : ℝ)^3511
        have hw : |(5431246373/10000000000 : ℝ)|=(5431246373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_6 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294863939/10000000000 : ℝ)*x 0 + (271562321/500000000 : ℝ)*x 1 + (-877109873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294863939/10000000000 : ℝ)^4535 ≤ (43986127940241/100000000000000 : ℝ)^3511 := by
    have hnat : (5294863939 : ℕ)^4535*100000000000000^3511 ≤ 43986127940241^3511*10000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294863939 10000000000 43986127940241 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271562321/500000000 : ℝ)^4535 ≤ (22727500760219/50000000000000 : ℝ)^3511 := by
    have hnat : (271562321 : ℕ)^4535*50000000000000^3511 ≤ 22727500760219^3511*500000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271562321 500000000 22727500760219 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877109873/5000000000 : ℝ)^4535 ≤ (5279435264403/50000000000000 : ℝ)^3511 := by
    have hnat : (877109873 : ℕ)^4535*50000000000000^3511 ≤ 5279435264403^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877109873 5000000000 5279435264403 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294863939/10000000000 : ℝ), (271562321/500000000 : ℝ), (-877109873/5000000000 : ℝ)] ![(43986127940241/100000000000000 : ℝ), (22727500760219/50000000000000 : ℝ), (5279435264403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294863939/10000000000 : ℝ)|^4535 ≤ (43986127940241/100000000000000 : ℝ)^3511
        have hw : |(5294863939/10000000000 : ℝ)|=(5294863939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271562321/500000000 : ℝ)|^4535 ≤ (22727500760219/50000000000000 : ℝ)^3511
        have hw : |(271562321/500000000 : ℝ)|=(271562321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-877109873/5000000000 : ℝ)|^4535 ≤ (5279435264403/50000000000000 : ℝ)^3511
        have hw : |(-877109873/5000000000 : ℝ)|=(877109873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1519_s5_7 (p : ℝ) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66665397/156250000 : ℝ)*x 0 + (2257100389/5000000000 : ℝ)*x 1 + (251916589/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66665397/156250000 : ℝ)^4535 ≤ (33280636968853/100000000000000 : ℝ)^3511 := by
    have hnat : (66665397 : ℕ)^4535*100000000000000^3511 ≤ 33280636968853^3511*156250000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66665397 156250000 33280636968853 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257100389/5000000000 : ℝ)^4535 ≤ (17898132917947/50000000000000 : ℝ)^3511 := by
    have hnat : (2257100389 : ℕ)^4535*50000000000000^3511 ≤ 17898132917947^3511*5000000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257100389 5000000000 17898132917947 50000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251916589/625000000 : ℝ)^4535 ≤ (30923097169179/100000000000000 : ℝ)^3511 := by
    have hnat : (251916589 : ℕ)^4535*100000000000000^3511 ≤ 30923097169179^3511*625000000^4535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251916589 625000000 30923097169179 100000000000000 4535 3511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4535/1024 : ℝ)) 4535 3511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66665397/156250000 : ℝ), (2257100389/5000000000 : ℝ), (251916589/625000000 : ℝ)] ![(33280636968853/100000000000000 : ℝ), (17898132917947/50000000000000 : ℝ), (30923097169179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66665397/156250000 : ℝ)|^4535 ≤ (33280636968853/100000000000000 : ℝ)^3511
        have hw : |(66665397/156250000 : ℝ)|=(66665397/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257100389/5000000000 : ℝ)|^4535 ≤ (17898132917947/50000000000000 : ℝ)^3511
        have hw : |(2257100389/5000000000 : ℝ)|=(2257100389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251916589/625000000 : ℝ)|^4535 ≤ (30923097169179/100000000000000 : ℝ)^3511
        have hw : |(251916589/625000000 : ℝ)|=(251916589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1519_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5471/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1367/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1367/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1367/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1367/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1367/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1367/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1367/12500 : ℝ) ^ (4533/1024 : ℝ) ≤ (5562363452576703/100000000000000000000 : ℝ) := by
    have hpowers : (1367/12500 : ℝ)^4533 ≤ (5562363452576703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1367 : ℕ)^4533*100000000000000000000^1024 ≤ 5562363452576703^1024*12500^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1367 12500 5562363452576703 100000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1367/12500 : ℝ)) (X := (5562363452576703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4533/1024 : ℝ) ≤ (6493723528498993/25000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4533 ≤ (6493723528498993/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4533*25000000000000000000^1024 ≤ 6493723528498993^1024*10000^4533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 6493723528498993 25000000000000000000 4533 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (6493723528498993/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005562363452576703/50000000000000000000 : ℝ) ≤ (2500062823901803/2500000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (50005562363452576703/50000000000000000000 : ℝ)^1024 ≤ (2500062823901803/2500000000000000 : ℝ)^4533 := by
      have hnat : (50005562363452576703 : ℕ)^1024*2500000000000000^4533 ≤ 2500062823901803^4533*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005562363452576703 50000000000000000000 2500062823901803 2500000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500062823901803/2500000000000000 : ℝ)) (X := (50005562363452576703/50000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001261490302662907/4000000000000000000 : ℝ) ≤ (625044521027043/625000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (4001261490302662907/4000000000000000000 : ℝ)^1024 ≤ (625044521027043/625000000000000 : ℝ)^4533 := by
      have hnat : (4001261490302662907 : ℕ)^1024*625000000000000^4533 ≤ 625044521027043^4533*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001261490302662907 4000000000000000000 625044521027043 625000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625044521027043/625000000000000 : ℝ)) (X := (4001261490302662907/4000000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506493723528498993/12500000000000000000 : ℝ) ≤ (2500293344314541/2500000000000000 : ℝ) ^ (4533/1024 : ℝ) := by
    have hpowers : (12506493723528498993/12500000000000000000 : ℝ)^1024 ≤ (2500293344314541/2500000000000000 : ℝ)^4533 := by
      have hnat : (12506493723528498993 : ℕ)^1024*2500000000000000^4533 ≤ 2500293344314541^4533*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506493723528498993 12500000000000000000 2500293344314541 2500000000000000 1024 4533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500293344314541/2500000000000000 : ℝ)) (X := (12506493723528498993/12500000000000000000 : ℝ)) (by norm_num) 4533 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5562363452576703/100000000000000000000 : ℝ) ≤ ((517398414946141277/517500000000000000 : ℝ)+2*(10478200579/10350000000000 : ℝ)*(1367/12500 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (517398414946141277/517500000000000000 : ℝ)+2*(10478200579/10350000000000 : ℝ)*(1367/12500 : ℝ)=(2500062823901803/2500000000000000 : ℝ) by norm_num, show 1+2*(5562363452576703/100000000000000000000 : ℝ)=(50005562363452576703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6493723528498993/25000000000000000000 : ℝ)+(5562363452576703/100000000000000000000 : ℝ) ≤ ((517398414946141277/517500000000000000 : ℝ)+(10478200579/10350000000000 : ℝ)*((1549/10000 : ℝ)+(1367/12500 : ℝ)))^(4533/1024 : ℝ) := by
    rw [show (517398414946141277/517500000000000000 : ℝ)+(10478200579/10350000000000 : ℝ)*((1549/10000 : ℝ)+(1367/12500 : ℝ))=(625044521027043/625000000000000 : ℝ) by norm_num, show 1+(6493723528498993/25000000000000000000 : ℝ)+(5562363452576703/100000000000000000000 : ℝ)=(4001261490302662907/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6493723528498993/25000000000000000000 : ℝ) ≤ ((517398414946141277/517500000000000000 : ℝ)+2*(10478200579/10350000000000 : ℝ)*(1549/10000 : ℝ))^(4533/1024 : ℝ) := by
    rw [show (517398414946141277/517500000000000000 : ℝ)+2*(10478200579/10350000000000 : ℝ)*(1549/10000 : ℝ)=(2500293344314541/2500000000000000 : ℝ) by norm_num, show 1+2*(6493723528498993/25000000000000000000 : ℝ)=(12506493723528498993/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (517398414946141277/517500000000000000 : ℝ)*(X 1 0+X 2 0)+(10478200579/10350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (517398414946141277/517500000000000000 : ℝ)) (alpha := (10478200579/10350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (517398414946141277/517500000000000000 : ℝ)*(X 0 1+X 2 1)+(10478200579/10350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (517398414946141277/517500000000000000 : ℝ)) (alpha := (10478200579/10350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (517398414946141277/517500000000000000 : ℝ)*(X 0 2+X 1 2)+(10478200579/10350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4533/1024 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (517398414946141277/517500000000000000 : ℝ)) (alpha := (10478200579/10350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116107521/625000000 : ℝ)*X 0 0+(43458881/80000000 : ℝ)*X 0 1+(1043589977/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668901011/1250000000 : ℝ)*X 1 0+(-491879063/2500000000 : ℝ)*X 1 1+(65224373/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351208029/10000000000 : ℝ)*X 2 0+(5217949909/10000000000 : ℝ)*X 2 1+(-983758119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1066629973/2500000000 : ℝ)*X 0 0+(4028127691/10000000000 : ℝ)*X 0 1+(2258360021/5000000000 : ℝ)*X 0 2+(1066629973/2500000000 : ℝ)*X 1 0+(4028127691/10000000000 : ℝ)*X 1 1+(2258360021/5000000000 : ℝ)*X 1 2+(1066629973/2500000000 : ℝ)*X 2 0+(4028127691/10000000000 : ℝ)*X 2 1+(2258360021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1857749041/10000000000 : ℝ)*X 0 0+(260952773/500000000 : ℝ)*X 0 1+(5431246401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323715997/2500000000 : ℝ)*X 1 0+(-1754219743/10000000000 : ℝ)*X 1 1+(5431246373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294863939/10000000000 : ℝ)*X 2 0+(271562321/500000000 : ℝ)*X 2 1+(-877109873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((66665397/156250000 : ℝ)*X 0 0+(2257100389/5000000000 : ℝ)*X 0 1+(251916589/625000000 : ℝ)*X 0 2+(66665397/156250000 : ℝ)*X 1 0+(2257100389/5000000000 : ℝ)*X 1 1+(251916589/625000000 : ℝ)*X 1 2+(66665397/156250000 : ℝ)*X 2 0+(2257100389/5000000000 : ℝ)*X 2 1+(251916589/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1519_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15029753788004470516447771/2156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (614860979/50000000000000 : ℝ)*(base19) + (225857653/20000000000000 : ℝ)*(base23) + (2622659/10000000000000 : ℝ)*(lower2) + (75271993/50000000000000 : ℝ)*(upper3) + (119530981/100000000000000 : ℝ)*(upper5) + (838838551680259/25000000000000 : ℝ)*(major0) + (838838551680259/25000000000000 : ℝ)*(major1) + (838838551680259/25000000000000 : ℝ)*(major2) + (233198819083779/5000000000000 : ℝ)*(sp0) + (1165998670009559/25000000000000 : ℝ)*(sp1) + (4663994780471929/100000000000000 : ℝ)*(sp2) + (511675974926677/25000000000000 : ℝ)*(sp3) + (9764042307/50000000000000 : ℝ)*(sp4) + (418581557/5000000000000 : ℝ)*(sp7) + (255839033917231/12500000000000 : ℝ)*(f.failure) + (932799181952039/20000000000000 : ℝ)*(f.sum) + (474236293309/517500000000000000000000000 : ℝ)*base65 + (17646391230500743/12937500000000000000000000000000 : ℝ)*base67 + (79510805539625743/12937500000000000000000000000000 : ℝ)*base69 + (20939304071000743/12937500000000000000000000000000 : ℝ)*base71 + (925853412493/258750000000000000000000000 : ℝ)*base74 + (108609834084500743/12937500000000000000000000000000 : ℝ)*base75 + (43690348395313243/12937500000000000000000000000000 : ℝ)*base77 + (180844356490063243/12937500000000000000000000000000 : ℝ)*base79 + (458622597949/517500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1031443/250000000000000000000 : ℝ)*base90 + (1031443/250000000000000000000 : ℝ)*base92 + (1031443/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4276544199588969197623/345000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2031200329/100000000000000 : ℝ)*(base19) + (541264177/25000000000000 : ℝ)*(base23) + (65664263/10000000000000 : ℝ)*(lower1) + (258167189/100000000000000 : ℝ)*(upper3) + (40554873/50000000000000 : ℝ)*(lower4) + (8036477/3125000000000 : ℝ)*(upper5) + (1695197829624707/50000000000000 : ℝ)*(major0) + (1695197829624707/50000000000000 : ℝ)*(major1) + (1695197829624707/50000000000000 : ℝ)*(major2) + (2281982833/100000000000000 : ℝ)*(sp2) + (1178175977432137/25000000000000 : ℝ)*(sp4) + (235635093926411/5000000000000 : ℝ)*(sp5) + (4712699462689007/100000000000000 : ℝ)*(sp6) + (1034043497788797/50000000000000 : ℝ)*(sp7) + (1034043497788797/50000000000000 : ℝ)*(f.failure) + (1178175977432137/25000000000000 : ℝ)*(f.sum) + (283219726967/64687500000000000000000000 : ℝ)*base65 + (367662811493880839/25875000000000000000000000000000 : ℝ)*base67 + (236674345524119161/25875000000000000000000000000000 : ℝ)*base70 + (113339194318619161/25875000000000000000000000000000 : ℝ)*base72 + (198094131473/258750000000000000000000000 : ℝ)*base73 + (378084855152880839/25875000000000000000000000000000 : ℝ)*base75 + (26229433482630839/25875000000000000000000000000000 : ℝ)*base77 + (229447966855994161/25875000000000000000000000000000 : ℝ)*base80 + (917337774611/129375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4529641/1000000000000000000000 : ℝ)*base90 + (4529641/1000000000000000000000 : ℝ)*base92 + (4529641/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1519_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1519_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1519_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1597/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1519_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1519_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1519_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4533/1024 : ℝ) ≤ p) (hpb : p ≤ (4535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32787747/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1597/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1519_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
