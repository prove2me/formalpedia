-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:51.934178+00:00
-- url     : https://prove2.me/submissions/c513e725-58c4-4a15-be9c-cc189daa0167

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
theorem support_rectangle_w1251_box_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-99620437/500000000 : ℝ)*x 0 + (5374707681/10000000000 : ℝ)*x 1 + (5374707637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99620437/500000000 : ℝ)^2111 ≤ (11886098540991/100000000000000 : ℝ)^1599 := by
    have hnat : (99620437 : ℕ)^2111*100000000000000^1599 ≤ 11886098540991^1599*500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99620437 500000000 11886098540991 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374707681/10000000000 : ℝ)^2111 ≤ (2753559435143/6250000000000 : ℝ)^1599 := by
    have hnat : (5374707681 : ℕ)^2111*6250000000000^1599 ≤ 2753559435143^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374707681 10000000000 2753559435143 6250000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374707637/10000000000 : ℝ)^2111 ≤ (44056950486129/100000000000000 : ℝ)^1599 := by
    have hnat : (5374707637 : ℕ)^2111*100000000000000^1599 ≤ 44056950486129^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374707637 10000000000 44056950486129 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99620437/500000000 : ℝ), (5374707681/10000000000 : ℝ), (5374707637/10000000000 : ℝ)] ![(11886098540991/100000000000000 : ℝ), (2753559435143/6250000000000 : ℝ), (44056950486129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99620437/500000000 : ℝ)|^2111 ≤ (11886098540991/100000000000000 : ℝ)^1599
        have hw : |(-99620437/500000000 : ℝ)|=(99620437/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374707681/10000000000 : ℝ)|^2111 ≤ (2753559435143/6250000000000 : ℝ)^1599
        have hw : |(5374707681/10000000000 : ℝ)|=(5374707681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374707637/10000000000 : ℝ)|^2111 ≤ (44056950486129/100000000000000 : ℝ)^1599
        have hw : |(5374707637/10000000000 : ℝ)|=(5374707637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2648428407/5000000000 : ℝ)*x 0 + (-419648047/2000000000 : ℝ)*x 1 + (214988313/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648428407/5000000000 : ℝ)^2111 ≤ (1350513278297/3125000000000 : ℝ)^1599 := by
    have hnat : (2648428407 : ℕ)^2111*3125000000000^1599 ≤ 1350513278297^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648428407 5000000000 1350513278297 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419648047/2000000000 : ℝ)^2111 ≤ (397706955039/3125000000000 : ℝ)^1599 := by
    have hnat : (419648047 : ℕ)^2111*3125000000000^1599 ≤ 397706955039^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419648047 2000000000 397706955039 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214988313/400000000 : ℝ)^2111 ≤ (22028476260313/50000000000000 : ℝ)^1599 := by
    have hnat : (214988313 : ℕ)^2111*50000000000000^1599 ≤ 22028476260313^1599*400000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214988313 400000000 22028476260313 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648428407/5000000000 : ℝ), (-419648047/2000000000 : ℝ), (214988313/400000000 : ℝ)] ![(1350513278297/3125000000000 : ℝ), (397706955039/3125000000000 : ℝ), (22028476260313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648428407/5000000000 : ℝ)|^2111 ≤ (1350513278297/3125000000000 : ℝ)^1599
        have hw : |(2648428407/5000000000 : ℝ)|=(2648428407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419648047/2000000000 : ℝ)|^2111 ≤ (397706955039/3125000000000 : ℝ)^1599
        have hw : |(-419648047/2000000000 : ℝ)|=(419648047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(214988313/400000000 : ℝ)|^2111 ≤ (22028476260313/50000000000000 : ℝ)^1599
        have hw : |(214988313/400000000 : ℝ)|=(214988313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5296857033/10000000000 : ℝ)*x 0 + (5374707523/10000000000 : ℝ)*x 1 + (-524560087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296857033/10000000000 : ℝ)^2111 ≤ (43216427264431/100000000000000 : ℝ)^1599 := by
    have hnat : (5296857033 : ℕ)^2111*100000000000000^1599 ≤ 43216427264431^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296857033 10000000000 43216427264431 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374707523/10000000000 : ℝ)^2111 ≤ (11014237313111/25000000000000 : ℝ)^1599 := by
    have hnat : (5374707523 : ℕ)^2111*25000000000000^1599 ≤ 11014237313111^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374707523 10000000000 11014237313111 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524560087/2500000000 : ℝ)^2111 ≤ (12726623466097/100000000000000 : ℝ)^1599 := by
    have hnat : (524560087 : ℕ)^2111*100000000000000^1599 ≤ 12726623466097^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524560087 2500000000 12726623466097 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296857033/10000000000 : ℝ), (5374707523/10000000000 : ℝ), (-524560087/2500000000 : ℝ)] ![(43216427264431/100000000000000 : ℝ), (11014237313111/25000000000000 : ℝ), (12726623466097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296857033/10000000000 : ℝ)|^2111 ≤ (43216427264431/100000000000000 : ℝ)^1599
        have hw : |(5296857033/10000000000 : ℝ)|=(5296857033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374707523/10000000000 : ℝ)|^2111 ≤ (11014237313111/25000000000000 : ℝ)^1599
        have hw : |(5374707523/10000000000 : ℝ)|=(5374707523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524560087/2500000000 : ℝ)|^2111 ≤ (12726623466097/100000000000000 : ℝ)^1599
        have hw : |(-524560087/2500000000 : ℝ)|=(524560087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (139249521/312500000 : ℝ)*x 0 + (4298357289/10000000000 : ℝ)*x 1 + (4298357119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139249521/312500000 : ℝ)^2111 ≤ (4299771990771/12500000000000 : ℝ)^1599 := by
    have hnat : (139249521 : ℕ)^2111*12500000000000^1599 ≤ 4299771990771^1599*312500000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139249521 312500000 4299771990771 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4298357289/10000000000 : ℝ)^2111 ≤ (8200228220193/25000000000000 : ℝ)^1599 := by
    have hnat : (4298357289 : ℕ)^2111*25000000000000^1599 ≤ 8200228220193^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298357289 10000000000 8200228220193 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4298357119/10000000000 : ℝ)^2111 ≤ (32800911168109/100000000000000 : ℝ)^1599 := by
    have hnat : (4298357119 : ℕ)^2111*100000000000000^1599 ≤ 32800911168109^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298357119 10000000000 32800911168109 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139249521/312500000 : ℝ), (4298357289/10000000000 : ℝ), (4298357119/10000000000 : ℝ)] ![(4299771990771/12500000000000 : ℝ), (8200228220193/25000000000000 : ℝ), (32800911168109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139249521/312500000 : ℝ)|^2111 ≤ (4299771990771/12500000000000 : ℝ)^1599
        have hw : |(139249521/312500000 : ℝ)|=(139249521/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4298357289/10000000000 : ℝ)|^2111 ≤ (8200228220193/25000000000000 : ℝ)^1599
        have hw : |(4298357289/10000000000 : ℝ)|=(4298357289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4298357119/10000000000 : ℝ)|^2111 ≤ (32800911168109/100000000000000 : ℝ)^1599
        have hw : |(4298357119/10000000000 : ℝ)|=(4298357119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-448125059/2000000000 : ℝ)*x 0 + (2641187871/5000000000 : ℝ)*x 1 + (1056475157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448125059/2000000000 : ℝ)^2111 ≤ (6939487319309/50000000000000 : ℝ)^1599 := by
    have hnat : (448125059 : ℕ)^2111*50000000000000^1599 ≤ 6939487319309^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448125059 2000000000 6939487319309 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641187871/5000000000 : ℝ)^2111 ≤ (21530256220403/50000000000000 : ℝ)^1599 := by
    have hnat : (2641187871 : ℕ)^2111*50000000000000^1599 ≤ 21530256220403^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641187871 5000000000 21530256220403 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056475157/2000000000 : ℝ)^2111 ≤ (43060512903569/100000000000000 : ℝ)^1599 := by
    have hnat : (1056475157 : ℕ)^2111*100000000000000^1599 ≤ 43060512903569^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056475157 2000000000 43060512903569 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448125059/2000000000 : ℝ), (2641187871/5000000000 : ℝ), (1056475157/2000000000 : ℝ)] ![(6939487319309/50000000000000 : ℝ), (21530256220403/50000000000000 : ℝ), (43060512903569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448125059/2000000000 : ℝ)|^2111 ≤ (6939487319309/50000000000000 : ℝ)^1599
        have hw : |(-448125059/2000000000 : ℝ)|=(448125059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641187871/5000000000 : ℝ)|^2111 ≤ (21530256220403/50000000000000 : ℝ)^1599
        have hw : |(2641187871/5000000000 : ℝ)|=(2641187871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056475157/2000000000 : ℝ)|^2111 ≤ (43060512903569/100000000000000 : ℝ)^1599
        have hw : |(1056475157/2000000000 : ℝ)|=(1056475157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167560359/312500000 : ℝ)*x 0 + (-426973841/2000000000 : ℝ)*x 1 + (5282375667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167560359/312500000 : ℝ)^2111 ≤ (1372460695311/3125000000000 : ℝ)^1599 := by
    have hnat : (167560359 : ℕ)^2111*3125000000000^1599 ≤ 1372460695311^1599*312500000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167560359 312500000 1372460695311 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426973841/2000000000 : ℝ)^2111 ≤ (203449157767/1562500000000 : ℝ)^1599 := by
    have hnat : (426973841 : ℕ)^2111*1562500000000^1599 ≤ 203449157767^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426973841 2000000000 203449157767 1562500000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282375667/10000000000 : ℝ)^2111 ≤ (21530255816831/50000000000000 : ℝ)^1599 := by
    have hnat : (5282375667 : ℕ)^2111*50000000000000^1599 ≤ 21530255816831^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282375667 10000000000 21530255816831 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167560359/312500000 : ℝ), (-426973841/2000000000 : ℝ), (5282375667/10000000000 : ℝ)] ![(1372460695311/3125000000000 : ℝ), (203449157767/1562500000000 : ℝ), (21530255816831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167560359/312500000 : ℝ)|^2111 ≤ (1372460695311/3125000000000 : ℝ)^1599
        have hw : |(167560359/312500000 : ℝ)|=(167560359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426973841/2000000000 : ℝ)|^2111 ≤ (203449157767/1562500000000 : ℝ)^1599
        have hw : |(-426973841/2000000000 : ℝ)|=(426973841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282375667/10000000000 : ℝ)|^2111 ≤ (21530255816831/50000000000000 : ℝ)^1599
        have hw : |(5282375667/10000000000 : ℝ)|=(5282375667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_6 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167560359/312500000 : ℝ)*x 0 + (1056475139/2000000000 : ℝ)*x 1 + (-133429323/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167560359/312500000 : ℝ)^2111 ≤ (1372460695311/3125000000000 : ℝ)^1599 := by
    have hnat : (167560359 : ℕ)^2111*3125000000000^1599 ≤ 1372460695311^1599*312500000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167560359 312500000 1372460695311 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056475139/2000000000 : ℝ)^2111 ≤ (10765127983749/25000000000000 : ℝ)^1599 := by
    have hnat : (1056475139 : ℕ)^2111*25000000000000^1599 ≤ 10765127983749^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056475139 2000000000 10765127983749 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133429323/625000000 : ℝ)^2111 ≤ (3255186449791/25000000000000 : ℝ)^1599 := by
    have hnat : (133429323 : ℕ)^2111*25000000000000^1599 ≤ 3255186449791^1599*625000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133429323 625000000 3255186449791 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167560359/312500000 : ℝ), (1056475139/2000000000 : ℝ), (-133429323/625000000 : ℝ)] ![(1372460695311/3125000000000 : ℝ), (10765127983749/25000000000000 : ℝ), (3255186449791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167560359/312500000 : ℝ)|^2111 ≤ (1372460695311/3125000000000 : ℝ)^1599
        have hw : |(167560359/312500000 : ℝ)|=(167560359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056475139/2000000000 : ℝ)|^2111 ≤ (10765127983749/25000000000000 : ℝ)^1599
        have hw : |(1056475139/2000000000 : ℝ)|=(1056475139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133429323/625000000 : ℝ)|^2111 ≤ (3255186449791/25000000000000 : ℝ)^1599
        have hw : |(-133429323/625000000 : ℝ)|=(133429323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_7 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2121346927/5000000000 : ℝ)*x 0 + (2202491269/5000000000 : ℝ)*x 1 + (880996523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121346927/5000000000 : ℝ)^2111 ≤ (644825961963/2000000000000 : ℝ)^1599 := by
    have hnat : (2121346927 : ℕ)^2111*2000000000000^1599 ≤ 644825961963^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121346927 5000000000 644825961963 2000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202491269/5000000000 : ℝ)^2111 ≤ (264682426221/781250000000 : ℝ)^1599 := by
    have hnat : (2202491269 : ℕ)^2111*781250000000^1599 ≤ 264682426221^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202491269 5000000000 264682426221 781250000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880996523/2000000000 : ℝ)^2111 ≤ (16939675669067/50000000000000 : ℝ)^1599 := by
    have hnat : (880996523 : ℕ)^2111*50000000000000^1599 ≤ 16939675669067^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880996523 2000000000 16939675669067 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121346927/5000000000 : ℝ), (2202491269/5000000000 : ℝ), (880996523/2000000000 : ℝ)] ![(644825961963/2000000000000 : ℝ), (264682426221/781250000000 : ℝ), (16939675669067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121346927/5000000000 : ℝ)|^2111 ≤ (644825961963/2000000000000 : ℝ)^1599
        have hw : |(2121346927/5000000000 : ℝ)|=(2121346927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2202491269/5000000000 : ℝ)|^2111 ≤ (264682426221/781250000000 : ℝ)^1599
        have hw : |(2202491269/5000000000 : ℝ)|=(2202491269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880996523/2000000000 : ℝ)|^2111 ≤ (16939675669067/50000000000000 : ℝ)^1599
        have hw : |(880996523/2000000000 : ℝ)|=(880996523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_8 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-218860267/1000000000 : ℝ)*x 0 + (5219378827/10000000000 : ℝ)*x 1 + (2692160541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218860267/1000000000 : ℝ)^2111 ≤ (13455142185239/100000000000000 : ℝ)^1599 := by
    have hnat : (218860267 : ℕ)^2111*100000000000000^1599 ≤ 13455142185239^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218860267 1000000000 13455142185239 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219378827/10000000000 : ℝ)^2111 ≤ (10595960699131/25000000000000 : ℝ)^1599 := by
    have hnat : (5219378827 : ℕ)^2111*25000000000000^1599 ≤ 10595960699131^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219378827 10000000000 10595960699131 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692160541/5000000000 : ℝ)^2111 ≤ (44161015009791/100000000000000 : ℝ)^1599 := by
    have hnat : (2692160541 : ℕ)^2111*100000000000000^1599 ≤ 44161015009791^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692160541 5000000000 44161015009791 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218860267/1000000000 : ℝ), (5219378827/10000000000 : ℝ), (2692160541/5000000000 : ℝ)] ![(13455142185239/100000000000000 : ℝ), (10595960699131/25000000000000 : ℝ), (44161015009791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218860267/1000000000 : ℝ)|^2111 ≤ (13455142185239/100000000000000 : ℝ)^1599
        have hw : |(-218860267/1000000000 : ℝ)|=(218860267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219378827/10000000000 : ℝ)|^2111 ≤ (10595960699131/25000000000000 : ℝ)^1599
        have hw : |(5219378827/10000000000 : ℝ)|=(5219378827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692160541/5000000000 : ℝ)|^2111 ≤ (44161015009791/100000000000000 : ℝ)^1599
        have hw : |(2692160541/5000000000 : ℝ)|=(2692160541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_9 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058015681/2000000000 : ℝ)*x 0 + (-2094359877/10000000000 : ℝ)*x 1 + (5384320899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058015681/2000000000 : ℝ)^2111 ≤ (345147417707/800000000000 : ℝ)^1599 := by
    have hnat : (1058015681 : ℕ)^2111*800000000000^1599 ≤ 345147417707^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058015681 2000000000 345147417707 800000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094359877/10000000000 : ℝ)^2111 ≤ (1586944967837/12500000000000 : ℝ)^1599 := by
    have hnat : (2094359877 : ℕ)^2111*12500000000000^1599 ≤ 1586944967837^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094359877 10000000000 1586944967837 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384320899/10000000000 : ℝ)^2111 ≤ (11040253257067/25000000000000 : ℝ)^1599 := by
    have hnat : (5384320899 : ℕ)^2111*25000000000000^1599 ≤ 11040253257067^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384320899 10000000000 11040253257067 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058015681/2000000000 : ℝ), (-2094359877/10000000000 : ℝ), (5384320899/10000000000 : ℝ)] ![(345147417707/800000000000 : ℝ), (1586944967837/12500000000000 : ℝ), (11040253257067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058015681/2000000000 : ℝ)|^2111 ≤ (345147417707/800000000000 : ℝ)^1599
        have hw : |(1058015681/2000000000 : ℝ)|=(1058015681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094359877/10000000000 : ℝ)|^2111 ≤ (1586944967837/12500000000000 : ℝ)^1599
        have hw : |(-2094359877/10000000000 : ℝ)|=(2094359877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384320899/10000000000 : ℝ)|^2111 ≤ (11040253257067/25000000000000 : ℝ)^1599
        have hw : |(5384320899/10000000000 : ℝ)|=(5384320899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_10 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322519567/2500000000 : ℝ)*x 0 + (5384321233/10000000000 : ℝ)*x 1 + (-209435961/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322519567/2500000000 : ℝ)^2111 ≤ (674116027161/1562500000000 : ℝ)^1599 := by
    have hnat : (1322519567 : ℕ)^2111*1562500000000^1599 ≤ 674116027161^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322519567 2500000000 674116027161 1562500000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384321233/10000000000 : ℝ)^2111 ≤ (44161016644817/100000000000000 : ℝ)^1599 := by
    have hnat : (5384321233 : ℕ)^2111*100000000000000^1599 ≤ 44161016644817^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384321233 10000000000 44161016644817 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209435961/1000000000 : ℝ)^2111 ≤ (3173889401489/25000000000000 : ℝ)^1599 := by
    have hnat : (209435961 : ℕ)^2111*25000000000000^1599 ≤ 3173889401489^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209435961 1000000000 3173889401489 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322519567/2500000000 : ℝ), (5384321233/10000000000 : ℝ), (-209435961/1000000000 : ℝ)] ![(674116027161/1562500000000 : ℝ), (44161016644817/100000000000000 : ℝ), (3173889401489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322519567/2500000000 : ℝ)|^2111 ≤ (674116027161/1562500000000 : ℝ)^1599
        have hw : |(1322519567/2500000000 : ℝ)|=(1322519567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384321233/10000000000 : ℝ)|^2111 ≤ (44161016644817/100000000000000 : ℝ)^1599
        have hw : |(5384321233/10000000000 : ℝ)|=(5384321233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209435961/1000000000 : ℝ)|^2111 ≤ (3173889401489/25000000000000 : ℝ)^1599
        have hw : |(-209435961/1000000000 : ℝ)|=(209435961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_11 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4477919627/10000000000 : ℝ)*x 0 + (857449833/2000000000 : ℝ)*x 1 + (1071812301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4477919627/10000000000 : ℝ)^2111 ≤ (17310949298907/50000000000000 : ℝ)^1599 := by
    have hnat : (4477919627 : ℕ)^2111*50000000000000^1599 ≤ 17310949298907^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477919627 10000000000 17310949298907 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857449833/2000000000 : ℝ)^2111 ≤ (6537810098941/20000000000000 : ℝ)^1599 := by
    have hnat : (857449833 : ℕ)^2111*20000000000000^1599 ≤ 6537810098941^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857449833 2000000000 6537810098941 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071812301/2500000000 : ℝ)^2111 ≤ (6537810177457/20000000000000 : ℝ)^1599 := by
    have hnat : (1071812301 : ℕ)^2111*20000000000000^1599 ≤ 6537810177457^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071812301 2500000000 6537810177457 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4477919627/10000000000 : ℝ), (857449833/2000000000 : ℝ), (1071812301/2500000000 : ℝ)] ![(17310949298907/50000000000000 : ℝ), (6537810098941/20000000000000 : ℝ), (6537810177457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4477919627/10000000000 : ℝ)|^2111 ≤ (17310949298907/50000000000000 : ℝ)^1599
        have hw : |(4477919627/10000000000 : ℝ)|=(4477919627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(857449833/2000000000 : ℝ)|^2111 ≤ (6537810098941/20000000000000 : ℝ)^1599
        have hw : |(857449833/2000000000 : ℝ)|=(857449833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1071812301/2500000000 : ℝ)|^2111 ≤ (6537810177457/20000000000000 : ℝ)^1599
        have hw : |(1071812301/2500000000 : ℝ)|=(1071812301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_12 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044686003/10000000000 : ℝ)*x 0 + (5436501523/10000000000 : ℝ)*x 1 + (5274293381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044686003/10000000000 : ℝ)^2111 ≤ (6149774440251/50000000000000 : ℝ)^1599 := by
    have hnat : (2044686003 : ℕ)^2111*50000000000000^1599 ≤ 6149774440251^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044686003 10000000000 6149774440251 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436501523/10000000000 : ℝ)^2111 ≤ (44726899057327/100000000000000 : ℝ)^1599 := by
    have hnat : (5436501523 : ℕ)^2111*100000000000000^1599 ≤ 44726899057327^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436501523 10000000000 44726899057327 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274293381/10000000000 : ℝ)^2111 ≤ (42973552050193/100000000000000 : ℝ)^1599 := by
    have hnat : (5274293381 : ℕ)^2111*100000000000000^1599 ≤ 42973552050193^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274293381 10000000000 42973552050193 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044686003/10000000000 : ℝ), (5436501523/10000000000 : ℝ), (5274293381/10000000000 : ℝ)] ![(6149774440251/50000000000000 : ℝ), (44726899057327/100000000000000 : ℝ), (42973552050193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044686003/10000000000 : ℝ)|^2111 ≤ (6149774440251/50000000000000 : ℝ)^1599
        have hw : |(-2044686003/10000000000 : ℝ)|=(2044686003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436501523/10000000000 : ℝ)|^2111 ≤ (44726899057327/100000000000000 : ℝ)^1599
        have hw : |(5436501523/10000000000 : ℝ)|=(5436501523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274293381/10000000000 : ℝ)|^2111 ≤ (42973552050193/100000000000000 : ℝ)^1599
        have hw : |(5274293381/10000000000 : ℝ)|=(5274293381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_13 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5367626839/10000000000 : ℝ)*x 0 + (-1069009799/5000000000 : ℝ)*x 1 + (1318573093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367626839/10000000000 : ℝ)^2111 ≤ (10995084924783/25000000000000 : ℝ)^1599 := by
    have hnat : (5367626839 : ℕ)^2111*25000000000000^1599 ≤ 10995084924783^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367626839 10000000000 10995084924783 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069009799/5000000000 : ℝ)^2111 ≤ (13046119087759/100000000000000 : ℝ)^1599 := by
    have hnat : (1069009799 : ℕ)^2111*100000000000000^1599 ≤ 13046119087759^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069009799 5000000000 13046119087759 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318573093/2500000000 : ℝ)^2111 ≤ (42973541196741/100000000000000 : ℝ)^1599 := by
    have hnat : (1318573093 : ℕ)^2111*100000000000000^1599 ≤ 42973541196741^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318573093 2500000000 42973541196741 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367626839/10000000000 : ℝ), (-1069009799/5000000000 : ℝ), (1318573093/2500000000 : ℝ)] ![(10995084924783/25000000000000 : ℝ), (13046119087759/100000000000000 : ℝ), (42973541196741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367626839/10000000000 : ℝ)|^2111 ≤ (10995084924783/25000000000000 : ℝ)^1599
        have hw : |(5367626839/10000000000 : ℝ)|=(5367626839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069009799/5000000000 : ℝ)|^2111 ≤ (13046119087759/100000000000000 : ℝ)^1599
        have hw : |(-1069009799/5000000000 : ℝ)|=(1069009799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318573093/2500000000 : ℝ)|^2111 ≤ (42973541196741/100000000000000 : ℝ)^1599
        have hw : |(1318573093/2500000000 : ℝ)|=(1318573093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_14 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536762641/1000000000 : ℝ)*x 0 + (5274292547/10000000000 : ℝ)*x 1 + (-106900997/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536762641/1000000000 : ℝ)^2111 ≤ (43980335058541/100000000000000 : ℝ)^1599 := by
    have hnat : (536762641 : ℕ)^2111*100000000000000^1599 ≤ 43980335058541^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536762641 1000000000 43980335058541 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274292547/10000000000 : ℝ)^2111 ≤ (21486771539577/50000000000000 : ℝ)^1599 := by
    have hnat : (5274292547 : ℕ)^2111*50000000000000^1599 ≤ 21486771539577^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274292547 10000000000 21486771539577 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106900997/500000000 : ℝ)^2111 ≤ (407691307589/3125000000000 : ℝ)^1599 := by
    have hnat : (106900997 : ℕ)^2111*3125000000000^1599 ≤ 407691307589^1599*500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106900997 500000000 407691307589 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536762641/1000000000 : ℝ), (5274292547/10000000000 : ℝ), (-106900997/500000000 : ℝ)] ![(43980335058541/100000000000000 : ℝ), (21486771539577/50000000000000 : ℝ), (407691307589/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536762641/1000000000 : ℝ)|^2111 ≤ (43980335058541/100000000000000 : ℝ)^1599
        have hw : |(536762641/1000000000 : ℝ)|=(536762641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274292547/10000000000 : ℝ)|^2111 ≤ (21486771539577/50000000000000 : ℝ)^1599
        have hw : |(5274292547/10000000000 : ℝ)|=(5274292547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106900997/500000000 : ℝ)|^2111 ≤ (407691307589/3125000000000 : ℝ)^1599
        have hw : |(-106900997/500000000 : ℝ)|=(106900997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_box_15 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4223790199/10000000000 : ℝ)*x 0 + (2207155641/5000000000 : ℝ)*x 1 + (441431201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223790199/10000000000 : ℝ)^2111 ≤ (8012945494881/25000000000000 : ℝ)^1599 := by
    have hnat : (4223790199 : ℕ)^2111*25000000000000^1599 ≤ 8012945494881^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223790199 10000000000 8012945494881 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207155641/5000000000 : ℝ)^2111 ≤ (33974105305091/100000000000000 : ℝ)^1599 := by
    have hnat : (2207155641 : ℕ)^2111*100000000000000^1599 ≤ 33974105305091^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207155641 5000000000 33974105305091 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441431201/1000000000 : ℝ)^2111 ≤ (16987056351051/50000000000000 : ℝ)^1599 := by
    have hnat : (441431201 : ℕ)^2111*50000000000000^1599 ≤ 16987056351051^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441431201 1000000000 16987056351051 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223790199/10000000000 : ℝ), (2207155641/5000000000 : ℝ), (441431201/1000000000 : ℝ)] ![(8012945494881/25000000000000 : ℝ), (33974105305091/100000000000000 : ℝ), (16987056351051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223790199/10000000000 : ℝ)|^2111 ≤ (8012945494881/25000000000000 : ℝ)^1599
        have hw : |(4223790199/10000000000 : ℝ)|=(4223790199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207155641/5000000000 : ℝ)|^2111 ≤ (33974105305091/100000000000000 : ℝ)^1599
        have hw : |(2207155641/5000000000 : ℝ)|=(2207155641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441431201/1000000000 : ℝ)|^2111 ≤ (16987056351051/50000000000000 : ℝ)^1599
        have hw : |(441431201/1000000000 : ℝ)|=(441431201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7781/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11877/20000 : ℝ) ∧ (16027/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16673/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1149/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1149/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1149/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1149/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1149/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1149/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1149/10000 : ℝ) ^ (8443/2048 : ℝ) ≤ (13369472088269053/100000000000000000000 : ℝ) := by
    have hpowers : (1149/10000 : ℝ)^8443 ≤ (13369472088269053/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1149 : ℕ)^8443*100000000000000000000^2048 ≤ 13369472088269053^2048*10000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1149 10000 13369472088269053 100000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1149/10000 : ℝ)) (X := (13369472088269053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (8443/2048 : ℝ) ≤ (31170831555195517/100000000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^8443 ≤ (31170831555195517/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14109 : ℕ)^8443*100000000000000000000^2048 ≤ 31170831555195517^2048*100000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 31170831555195517 100000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (31170831555195517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013369472088269053/50000000000000000000 : ℝ) ≤ (10000648535036721/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50013369472088269053/50000000000000000000 : ℝ)^2048 ≤ (10000648535036721/10000000000000000 : ℝ)^8443 := by
      have hnat : (50013369472088269053 : ℕ)^2048*10000000000000000^8443 ≤ 10000648535036721^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013369472088269053 50000000000000000000 10000648535036721 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000648535036721/10000000000000000 : ℝ)) (X := (50013369472088269053/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004454030364346457/10000000000000000000 : ℝ) ≤ (2000216044436843/2000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (10004454030364346457/10000000000000000000 : ℝ)^2048 ≤ (2000216044436843/2000000000000000 : ℝ)^8443 := by
      have hnat : (10004454030364346457 : ℕ)^2048*2000000000000000^8443 ≤ 2000216044436843^8443*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004454030364346457 10000000000000000000 2000216044436843 2000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000216044436843/2000000000000000 : ℝ)) (X := (10004454030364346457/10000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031170831555195517/50000000000000000000 : ℝ) ≤ (10001511909331709/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50031170831555195517/50000000000000000000 : ℝ)^2048 ≤ (10001511909331709/10000000000000000 : ℝ)^8443 := by
      have hnat : (50031170831555195517 : ℕ)^2048*10000000000000000^8443 ≤ 10001511909331709^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031170831555195517 50000000000000000000 10001511909331709 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001511909331709/10000000000000000 : ℝ)) (X := (50031170831555195517/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13369472088269053/100000000000000000000 : ℝ) ≤ ((8727259447537253393/8730000000000000000 : ℝ)+2*(215843573747/130950000000000 : ℝ)*(1149/10000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (8727259447537253393/8730000000000000000 : ℝ)+2*(215843573747/130950000000000 : ℝ)*(1149/10000 : ℝ)=(10000648535036721/10000000000000000 : ℝ) by norm_num, show 1+2*(13369472088269053/100000000000000000000 : ℝ)=(50013369472088269053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31170831555195517/100000000000000000000 : ℝ)+(13369472088269053/100000000000000000000 : ℝ) ≤ ((8727259447537253393/8730000000000000000 : ℝ)+(215843573747/130950000000000 : ℝ)*((14109/100000 : ℝ)+(1149/10000 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (8727259447537253393/8730000000000000000 : ℝ)+(215843573747/130950000000000 : ℝ)*((14109/100000 : ℝ)+(1149/10000 : ℝ))=(2000216044436843/2000000000000000 : ℝ) by norm_num, show 1+(31170831555195517/100000000000000000000 : ℝ)+(13369472088269053/100000000000000000000 : ℝ)=(10004454030364346457/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31170831555195517/100000000000000000000 : ℝ) ≤ ((8727259447537253393/8730000000000000000 : ℝ)+2*(215843573747/130950000000000 : ℝ)*(14109/100000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (8727259447537253393/8730000000000000000 : ℝ)+2*(215843573747/130950000000000 : ℝ)*(14109/100000 : ℝ)=(10001511909331709/10000000000000000 : ℝ) by norm_num, show 1+2*(31170831555195517/100000000000000000000 : ℝ)=(50031170831555195517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8727259447537253393/8730000000000000000 : ℝ)*(X 1 0+X 2 0)+(215843573747/130950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (1149/10000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (8727259447537253393/8730000000000000000 : ℝ)) (alpha := (215843573747/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8727259447537253393/8730000000000000000 : ℝ)*(X 0 1+X 2 1)+(215843573747/130950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (1149/10000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (8727259447537253393/8730000000000000000 : ℝ)) (alpha := (215843573747/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8727259447537253393/8730000000000000000 : ℝ)*(X 0 2+X 1 2)+(215843573747/130950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (1149/10000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (8727259447537253393/8730000000000000000 : ℝ)) (alpha := (215843573747/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-99620437/500000000 : ℝ)*X 0 0+(5374707681/10000000000 : ℝ)*X 0 1+(5374707637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648428407/5000000000 : ℝ)*X 1 0+(-419648047/2000000000 : ℝ)*X 1 1+(214988313/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296857033/10000000000 : ℝ)*X 2 0+(5374707523/10000000000 : ℝ)*X 2 1+(-524560087/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((139249521/312500000 : ℝ)*X 0 0+(4298357289/10000000000 : ℝ)*X 0 1+(4298357119/10000000000 : ℝ)*X 0 2+(139249521/312500000 : ℝ)*X 1 0+(4298357289/10000000000 : ℝ)*X 1 1+(4298357119/10000000000 : ℝ)*X 1 2+(139249521/312500000 : ℝ)*X 2 0+(4298357289/10000000000 : ℝ)*X 2 1+(4298357119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-448125059/2000000000 : ℝ)*X 0 0+(2641187871/5000000000 : ℝ)*X 0 1+(1056475157/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((167560359/312500000 : ℝ)*X 1 0+(-426973841/2000000000 : ℝ)*X 1 1+(5282375667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((167560359/312500000 : ℝ)*X 2 0+(1056475139/2000000000 : ℝ)*X 2 1+(-133429323/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121346927/5000000000 : ℝ)*X 0 0+(2202491269/5000000000 : ℝ)*X 0 1+(880996523/2000000000 : ℝ)*X 0 2+(2121346927/5000000000 : ℝ)*X 1 0+(2202491269/5000000000 : ℝ)*X 1 1+(880996523/2000000000 : ℝ)*X 1 2+(2121346927/5000000000 : ℝ)*X 2 0+(2202491269/5000000000 : ℝ)*X 2 1+(880996523/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-218860267/1000000000 : ℝ)*X 0 0+(5219378827/10000000000 : ℝ)*X 0 1+(2692160541/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1058015681/2000000000 : ℝ)*X 1 0+(-2094359877/10000000000 : ℝ)*X 1 1+(5384320899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322519567/2500000000 : ℝ)*X 2 0+(5384321233/10000000000 : ℝ)*X 2 1+(-209435961/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4477919627/10000000000 : ℝ)*X 0 0+(857449833/2000000000 : ℝ)*X 0 1+(1071812301/2500000000 : ℝ)*X 0 2+(4477919627/10000000000 : ℝ)*X 1 0+(857449833/2000000000 : ℝ)*X 1 1+(1071812301/2500000000 : ℝ)*X 1 2+(4477919627/10000000000 : ℝ)*X 2 0+(857449833/2000000000 : ℝ)*X 2 1+(1071812301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2044686003/10000000000 : ℝ)*X 0 0+(5436501523/10000000000 : ℝ)*X 0 1+(5274293381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367626839/10000000000 : ℝ)*X 1 0+(-1069009799/5000000000 : ℝ)*X 1 1+(1318573093/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536762641/1000000000 : ℝ)*X 2 0+(5274292547/10000000000 : ℝ)*X 2 1+(-106900997/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4223790199/10000000000 : ℝ)*X 0 0+(2207155641/5000000000 : ℝ)*X 0 1+(441431201/1000000000 : ℝ)*X 0 2+(4223790199/10000000000 : ℝ)*X 1 0+(2207155641/5000000000 : ℝ)*X 1 1+(441431201/1000000000 : ℝ)*X 1 2+(4223790199/10000000000 : ℝ)*X 2 0+(2207155641/5000000000 : ℝ)*X 2 1+(441431201/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7781/12500 : ℝ) ≤ (-181135676887028184760239197/291000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48151773/100000000000000 : ℝ)*(lower2) + (2279461/5000000000000 : ℝ)*(lower3) + (24304153/50000000000000 : ℝ)*(lower4) + (49969/1000000000000 : ℝ)*(lower5) + (25065268347831/625000000000 : ℝ)*(major0) + (25065268347831/625000000000 : ℝ)*(major1) + (25065268347831/625000000000 : ℝ)*(major2) + (2068092313/100000000000000 : ℝ)*(sp1) + (2138254537/100000000000000 : ℝ)*(sp2) + (134907689546097/2500000000000 : ℝ)*(sp4) + (5396305612621489/100000000000000 : ℝ)*(sp5) + (1079261108491853/20000000000000 : ℝ)*(sp6) + (2645326836283633/100000000000000 : ℝ)*(sp7) + (98869923/100000000000000 : ℝ)*(sp8) + (2645326836283633/100000000000000 : ℝ)*(f.failure) + (2698153840356901/50000000000000 : ℝ)*(f.sum) + (1007999304173/43650000000000000000000000 : ℝ)*base65 + (49255789706978167/5456250000000000000000000000000 : ℝ)*base68 + (55811053656090667/5456250000000000000000000000000 : ℝ)*base70 + (153139285389565583/5456250000000000000000000000000 : ℝ)*base71 + (815740199713/436500000000000000000000000 : ℝ)*base74 + (6329931465128167/5456250000000000000000000000000 : ℝ)*base76 + (74439270443496833/5456250000000000000000000000000 : ℝ)*base77 + (38099499865615583/5456250000000000000000000000000 : ℝ)*base79 + (1491886953011/873000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11328103/5000000000000000000000 : ℝ)*base90 + (11328103/5000000000000000000000 : ℝ)*base92 + (11328103/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11877/20000 : ℝ) ≤ (43204073661925161810081107553067/72750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30711327/20000000000000 : ℝ)*(lower0) + (31903679/20000000000000 : ℝ)*(lower1) + (11683/31250000000 : ℝ)*(lower2) + (28583951/50000000000000 : ℝ)*(lower3) + (123505719/100000000000000 : ℝ)*(lower5) + (4076403236320219/100000000000000 : ℝ)*(major0) + (4076403236320219/100000000000000 : ℝ)*(major1) + (4076403236320219/100000000000000 : ℝ)*(major2) + (5444175904983661/100000000000000 : ℝ)*(sp0) + (5444175904983661/100000000000000 : ℝ)*(sp1) + (2722027586147823/50000000000000 : ℝ)*(sp2) + (672207410125827/25000000000000 : ℝ)*(sp3) + (5246208683/100000000000000 : ℝ)*(sp7) + (24146537603/20000000000000 : ℝ)*(sp10) + (268883488671199/10000000000000 : ℝ)*(f.failure) + (5444175904983661/100000000000000 : ℝ)*(f.sum) + (8442380900503/1636875000000000000000000000 : ℝ)*base66 + (27014410108137640799/2619000000000000000000000000000000 : ℝ)*base68 + (254302266231869359201/2619000000000000000000000000000000 : ℝ)*base69 + (32597478299532640799/2619000000000000000000000000000000 : ℝ)*base72 + (29777742289259/13095000000000000000000000000 : ℝ)*base74 + (112716348902022640799/2619000000000000000000000000000000 : ℝ)*base76 + (41291040023328640799/2619000000000000000000000000000000 : ℝ)*base78 + (281343580936365640799/2619000000000000000000000000000000 : ℝ)*base80 + (126952284583981/13095000000000000000000000000 : ℝ)*base81 + (1881609/500000000000000000000 : ℝ)*base90 + (1881609/500000000000000000000 : ℝ)*base92 + (1881609/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (16027/20000 : ℝ) ≤ (69960328971255816929509529433053/87300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30508777/20000000000000 : ℝ)*(lower3) + (16288057/25000000000000 : ℝ)*(upper4) + (63833927/100000000000000 : ℝ)*(lower5) + (908609207144207/20000000000000 : ℝ)*(major0) + (908609207144207/20000000000000 : ℝ)*(major1) + (908609207144207/20000000000000 : ℝ)*(major2) + (8806008763/100000000000000 : ℝ)*(sp0) + (10415254497/20000000000000 : ℝ)*(sp1) + (270714839521/100000000000000 : ℝ)*(sp2) + (27174654241/25000000000000 : ℝ)*(sp3) + (3031366838366817/50000000000000 : ℝ)*(sp8) + (6062690406469913/100000000000000 : ℝ)*(sp9) + (1515617941975719/25000000000000 : ℝ)*(sp10) + (2996528278791653/100000000000000 : ℝ)*(sp11) + (2996636977408617/100000000000000 : ℝ)*(f.failure) + (6062742482742397/100000000000000 : ℝ)*(f.sum) + (3382280213083/2619000000000000000000000000 : ℝ)*base66 + (4352871096843333053/523800000000000000000000000000000 : ℝ)*base67 + (7716900236159666947/523800000000000000000000000000000 : ℝ)*base70 + (2371513299018266947/523800000000000000000000000000000 : ℝ)*base72 + (6759998819377/2619000000000000000000000000 : ℝ)*base74 + (8194926345713066947/523800000000000000000000000000000 : ℝ)*base76 + (2162521502081066947/523800000000000000000000000000000 : ℝ)*base78 + (1672478243097333053/523800000000000000000000000000000 : ℝ)*base79 + (9598649382341/1309500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4041647/5000000000000000000000 : ℝ)*base90 + (4041647/5000000000000000000000 : ℝ)*base92 + (4041647/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-16673/20000 : ℝ) ≤ (-90969807937377884526503326983457/109125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9437647/100000000000000 : ℝ)*(lower3) + (36666489/10000000000000 : ℝ)*(lower4) + (5614717/10000000000000 : ℝ)*(upper5) + (2289321041451517/50000000000000 : ℝ)*(major0) + (2289321041451517/50000000000000 : ℝ)*(major1) + (2289321041451517/50000000000000 : ℝ)*(major2) + (2513587191/10000000000000 : ℝ)*(sp4) + (783000217301/100000000000000 : ℝ)*(sp5) + (481248393599/50000000000000 : ℝ)*(sp6) + (355495292791/100000000000000 : ℝ)*(sp7) + (6164930203086509/100000000000000 : ℝ)*(sp12) + (6164172338741119/100000000000000 : ℝ)*(sp13) + (3081996421085611/50000000000000 : ℝ)*(sp14) + (1509880489059193/50000000000000 : ℝ)*(sp15) + (1510058236705589/50000000000000 : ℝ)*(f.failure) + (308247766947921/5000000000000 : ℝ)*(f.sum) + (23102110240451/13095000000000000000000000000 : ℝ)*base65 + (4511719883751958457/1309500000000000000000000000000000 : ℝ)*base68 + (7517260994361541543/1309500000000000000000000000000000 : ℝ)*base69 + (9955438693341958457/1309500000000000000000000000000000 : ℝ)*base72 + (28516287073789/13095000000000000000000000000 : ℝ)*base74 + (3095532984620458457/1309500000000000000000000000000000 : ℝ)*base76 + (12376831103534458457/1309500000000000000000000000000000 : ℝ)*base78 + (468474444713458457/1309500000000000000000000000000000 : ℝ)*base80 + (64539168337601/13095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (19963901/2500000000000000000000 : ℝ)*base89 + (19963901/2500000000000000000000 : ℝ)*base91 + (19963901/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1251_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11877/20000 : ℝ) else (16027/20000 : ℝ) ≤ X j i ∧ X j i ≤ (16673/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1251_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1251_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11877/20000 : ℝ) else (16027/20000 : ℝ) ≤ X j i ∧ X j i ≤ (16673/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1251_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11877/20000 : ℝ) else (16027/20000 : ℝ) ≤ X j i ∧ X j i ≤ (16673/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
