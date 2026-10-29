-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1438_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:34.093762+00:00
-- url     : https://prove2.me/submissions/96bf4e30-0fa1-4e74-9aac-1150b6eaa015

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
theorem support_rectangle_w1438_s3_0 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962849683/10000000000 : ℝ)*x 0 + (1354094933/2500000000 : ℝ)*x 1 + (5239139447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962849683/10000000000 : ℝ)^2199 ≤ (5987563744243/50000000000000 : ℝ)^1687 := by
    have hnat : (1962849683 : ℕ)^2199*50000000000000^1687 ≤ 5987563744243^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962849683 10000000000 5987563744243 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354094933/2500000000 : ℝ)^2199 ≤ (22483324678451/50000000000000 : ℝ)^1687 := by
    have hnat : (1354094933 : ℕ)^2199*50000000000000^1687 ≤ 22483324678451^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354094933 2500000000 22483324678451 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239139447/10000000000 : ℝ)^2199 ≤ (21529111569519/50000000000000 : ℝ)^1687 := by
    have hnat : (5239139447 : ℕ)^2199*50000000000000^1687 ≤ 21529111569519^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239139447 10000000000 21529111569519 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962849683/10000000000 : ℝ), (1354094933/2500000000 : ℝ), (5239139447/10000000000 : ℝ)] ![(5987563744243/50000000000000 : ℝ), (22483324678451/50000000000000 : ℝ), (21529111569519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962849683/10000000000 : ℝ)|^2199 ≤ (5987563744243/50000000000000 : ℝ)^1687
        have hw : |(-1962849683/10000000000 : ℝ)|=(1962849683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354094933/2500000000 : ℝ)|^2199 ≤ (22483324678451/50000000000000 : ℝ)^1687
        have hw : |(1354094933/2500000000 : ℝ)|=(1354094933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239139447/10000000000 : ℝ)|^2199 ≤ (21529111569519/50000000000000 : ℝ)^1687
        have hw : |(5239139447/10000000000 : ℝ)|=(5239139447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_1 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83583839/156250000 : ℝ)*x 0 + (-2005122/9765625 : ℝ)*x 1 + (1309784749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83583839/156250000 : ℝ)^2199 ≤ (44242815607621/100000000000000 : ℝ)^1687 := by
    have hnat : (83583839 : ℕ)^2199*100000000000000^1687 ≤ 44242815607621^1687*156250000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83583839 156250000 44242815607621 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005122/9765625 : ℝ)^2199 ≤ (12698966075021/100000000000000 : ℝ)^1687 := by
    have hnat : (2005122 : ℕ)^2199*100000000000000^1687 ≤ 12698966075021^1687*9765625^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005122 9765625 12698966075021 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309784749/2500000000 : ℝ)^2199 ≤ (43058218307529/100000000000000 : ℝ)^1687 := by
    have hnat : (1309784749 : ℕ)^2199*100000000000000^1687 ≤ 43058218307529^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309784749 2500000000 43058218307529 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83583839/156250000 : ℝ), (-2005122/9765625 : ℝ), (1309784749/2500000000 : ℝ)] ![(44242815607621/100000000000000 : ℝ), (12698966075021/100000000000000 : ℝ), (43058218307529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83583839/156250000 : ℝ)|^2199 ≤ (44242815607621/100000000000000 : ℝ)^1687
        have hw : |(83583839/156250000 : ℝ)|=(83583839/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005122/9765625 : ℝ)|^2199 ≤ (12698966075021/100000000000000 : ℝ)^1687
        have hw : |(-2005122/9765625 : ℝ)|=(2005122/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309784749/2500000000 : ℝ)|^2199 ≤ (43058218307529/100000000000000 : ℝ)^1687
        have hw : |(1309784749/2500000000 : ℝ)|=(1309784749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_2 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337341411/2500000000 : ℝ)*x 0 + (2619569503/5000000000 : ℝ)*x 1 + (-256655623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337341411/2500000000 : ℝ)^2199 ≤ (2212140752351/5000000000000 : ℝ)^1687 := by
    have hnat : (1337341411 : ℕ)^2199*5000000000000^1687 ≤ 2212140752351^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337341411 2500000000 2212140752351 5000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619569503/5000000000 : ℝ)^2199 ≤ (21529109207329/50000000000000 : ℝ)^1687 := by
    have hnat : (2619569503 : ℕ)^2199*50000000000000^1687 ≤ 21529109207329^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619569503 5000000000 21529109207329 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256655623/1250000000 : ℝ)^2199 ≤ (1587370815811/12500000000000 : ℝ)^1687 := by
    have hnat : (256655623 : ℕ)^2199*12500000000000^1687 ≤ 1587370815811^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256655623 1250000000 1587370815811 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337341411/2500000000 : ℝ), (2619569503/5000000000 : ℝ), (-256655623/1250000000 : ℝ)] ![(2212140752351/5000000000000 : ℝ), (21529109207329/50000000000000 : ℝ), (1587370815811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337341411/2500000000 : ℝ)|^2199 ≤ (2212140752351/5000000000000 : ℝ)^1687
        have hw : |(1337341411/2500000000 : ℝ)|=(1337341411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619569503/5000000000 : ℝ)|^2199 ≤ (21529109207329/50000000000000 : ℝ)^1687
        have hw : |(2619569503/5000000000 : ℝ)|=(2619569503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256655623/1250000000 : ℝ)|^2199 ≤ (1587370815811/12500000000000 : ℝ)^1687
        have hw : |(-256655623/1250000000 : ℝ)|=(256655623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_3 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215075733/500000000 : ℝ)*x 0 + (514127473/1250000000 : ℝ)*x 1 + (899542827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215075733/500000000 : ℝ)^2199 ≤ (4162329861983/12500000000000 : ℝ)^1687 := by
    have hnat : (215075733 : ℕ)^2199*12500000000000^1687 ≤ 4162329861983^1687*500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215075733 500000000 4162329861983 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514127473/1250000000 : ℝ)^2199 ≤ (1256375970281/4000000000000 : ℝ)^1687 := by
    have hnat : (514127473 : ℕ)^2199*4000000000000^1687 ≤ 1256375970281^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514127473 1250000000 1256375970281 4000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899542827/2000000000 : ℝ)^2199 ≤ (7058392368627/20000000000000 : ℝ)^1687 := by
    have hnat : (899542827 : ℕ)^2199*20000000000000^1687 ≤ 7058392368627^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899542827 2000000000 7058392368627 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215075733/500000000 : ℝ), (514127473/1250000000 : ℝ), (899542827/2000000000 : ℝ)] ![(4162329861983/12500000000000 : ℝ), (1256375970281/4000000000000 : ℝ), (7058392368627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215075733/500000000 : ℝ)|^2199 ≤ (4162329861983/12500000000000 : ℝ)^1687
        have hw : |(215075733/500000000 : ℝ)|=(215075733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514127473/1250000000 : ℝ)|^2199 ≤ (1256375970281/4000000000000 : ℝ)^1687
        have hw : |(514127473/1250000000 : ℝ)|=(514127473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899542827/2000000000 : ℝ)|^2199 ≤ (7058392368627/20000000000000 : ℝ)^1687
        have hw : |(899542827/2000000000 : ℝ)|=(899542827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_4 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962864241/10000000000 : ℝ)*x 0 + (5239844853/10000000000 : ℝ)*x 1 + (5415670687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962864241/10000000000 : ℝ)^2199 ≤ (11975243260997/100000000000000 : ℝ)^1687 := by
    have hnat : (1962864241 : ℕ)^2199*100000000000000^1687 ≤ 11975243260997^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962864241 10000000000 11975243260997 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239844853/10000000000 : ℝ)^2199 ≤ (2153289011209/5000000000000 : ℝ)^1687 := by
    have hnat : (5239844853 : ℕ)^2199*5000000000000^1687 ≤ 2153289011209^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239844853 10000000000 2153289011209 5000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415670687/10000000000 : ℝ)^2199 ≤ (5619872063289/12500000000000 : ℝ)^1687 := by
    have hnat : (5415670687 : ℕ)^2199*12500000000000^1687 ≤ 5619872063289^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415670687 10000000000 5619872063289 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962864241/10000000000 : ℝ), (5239844853/10000000000 : ℝ), (5415670687/10000000000 : ℝ)] ![(11975243260997/100000000000000 : ℝ), (2153289011209/5000000000000 : ℝ), (5619872063289/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962864241/10000000000 : ℝ)|^2199 ≤ (11975243260997/100000000000000 : ℝ)^1687
        have hw : |(-1962864241/10000000000 : ℝ)|=(1962864241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239844853/10000000000 : ℝ)|^2199 ≤ (2153289011209/5000000000000 : ℝ)^1687
        have hw : |(5239844853/10000000000 : ℝ)|=(5239844853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415670687/10000000000 : ℝ)|^2199 ≤ (5619872063289/12500000000000 : ℝ)^1687
        have hw : |(5415670687/10000000000 : ℝ)|=(5415670687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_5 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651624039/5000000000 : ℝ)*x 0 + (-938356887/5000000000 : ℝ)*x 1 + (5415670621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651624039/5000000000 : ℝ)^2199 ≤ (8749256593007/20000000000000 : ℝ)^1687 := by
    have hnat : (2651624039 : ℕ)^2199*20000000000000^1687 ≤ 8749256593007^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651624039 5000000000 8749256593007 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938356887/5000000000 : ℝ)^2199 ≤ (1411842653273/12500000000000 : ℝ)^1687 := by
    have hnat : (938356887 : ℕ)^2199*12500000000000^1687 ≤ 1411842653273^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938356887 5000000000 1411842653273 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415670621/10000000000 : ℝ)^2199 ≤ (22479487896057/50000000000000 : ℝ)^1687 := by
    have hnat : (5415670621 : ℕ)^2199*50000000000000^1687 ≤ 22479487896057^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415670621 10000000000 22479487896057 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651624039/5000000000 : ℝ), (-938356887/5000000000 : ℝ), (5415670621/10000000000 : ℝ)] ![(8749256593007/20000000000000 : ℝ), (1411842653273/12500000000000 : ℝ), (22479487896057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651624039/5000000000 : ℝ)|^2199 ≤ (8749256593007/20000000000000 : ℝ)^1687
        have hw : |(2651624039/5000000000 : ℝ)|=(2651624039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-938356887/5000000000 : ℝ)|^2199 ≤ (1411842653273/12500000000000 : ℝ)^1687
        have hw : |(-938356887/5000000000 : ℝ)|=(938356887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415670621/10000000000 : ℝ)|^2199 ≤ (22479487896057/50000000000000 : ℝ)^1687
        have hw : |(5415670621/10000000000 : ℝ)|=(5415670621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_6 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303246743/10000000000 : ℝ)*x 0 + (1353917931/2500000000 : ℝ)*x 1 + (-1876714083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303246743/10000000000 : ℝ)^2199 ≤ (43746268610451/100000000000000 : ℝ)^1687 := by
    have hnat : (5303246743 : ℕ)^2199*100000000000000^1687 ≤ 43746268610451^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303246743 10000000000 43746268610451 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353917931/2500000000 : ℝ)^2199 ≤ (11239746931967/25000000000000 : ℝ)^1687 := by
    have hnat : (1353917931 : ℕ)^2199*25000000000000^1687 ≤ 11239746931967^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353917931 2500000000 11239746931967 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876714083/10000000000 : ℝ)^2199 ≤ (1411842956283/12500000000000 : ℝ)^1687 := by
    have hnat : (1876714083 : ℕ)^2199*12500000000000^1687 ≤ 1411842956283^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876714083 10000000000 1411842956283 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303246743/10000000000 : ℝ), (1353917931/2500000000 : ℝ), (-1876714083/10000000000 : ℝ)] ![(43746268610451/100000000000000 : ℝ), (11239746931967/25000000000000 : ℝ), (1411842956283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303246743/10000000000 : ℝ)|^2199 ≤ (43746268610451/100000000000000 : ℝ)^1687
        have hw : |(5303246743/10000000000 : ℝ)|=(5303246743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353917931/2500000000 : ℝ)|^2199 ≤ (11239746931967/25000000000000 : ℝ)^1687
        have hw : |(1353917931/2500000000 : ℝ)|=(1353917931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876714083/10000000000 : ℝ)|^2199 ≤ (1411842956283/12500000000000 : ℝ)^1687
        have hw : |(-1876714083/10000000000 : ℝ)|=(1876714083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s3_7 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (860309291/2000000000 : ℝ)*x 0 + (562023011/1250000000 : ℝ)*x 1 + (4114559519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860309291/2000000000 : ℝ)^2199 ≤ (4162369965693/12500000000000 : ℝ)^1687 := by
    have hnat : (860309291 : ℕ)^2199*12500000000000^1687 ≤ 4162369965693^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860309291 2000000000 4162369965693 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562023011/1250000000 : ℝ)^2199 ≤ (1411052528343/4000000000000 : ℝ)^1687 := by
    have hnat : (562023011 : ℕ)^2199*4000000000000^1687 ≤ 1411052528343^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562023011 1250000000 1411052528343 4000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4114559519/10000000000 : ℝ)^2199 ≤ (31424727050101/100000000000000 : ℝ)^1687 := by
    have hnat : (4114559519 : ℕ)^2199*100000000000000^1687 ≤ 31424727050101^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114559519 10000000000 31424727050101 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860309291/2000000000 : ℝ), (562023011/1250000000 : ℝ), (4114559519/10000000000 : ℝ)] ![(4162369965693/12500000000000 : ℝ), (1411052528343/4000000000000 : ℝ), (31424727050101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860309291/2000000000 : ℝ)|^2199 ≤ (4162369965693/12500000000000 : ℝ)^1687
        have hw : |(860309291/2000000000 : ℝ)|=(860309291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562023011/1250000000 : ℝ)|^2199 ≤ (1411052528343/4000000000000 : ℝ)^1687
        have hw : |(562023011/1250000000 : ℝ)|=(562023011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4114559519/10000000000 : ℝ)|^2199 ≤ (31424727050101/100000000000000 : ℝ)^1687
        have hw : |(4114559519/10000000000 : ℝ)|=(4114559519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1438_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3943/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2797/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7471/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3943/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2083/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3943/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2083/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3943/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2083/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3943/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2083/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3943/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2083/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3943/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2083/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2083/20000 : ℝ) ^ (4397/1024 : ℝ) ≤ (6051773224605089/100000000000000000000 : ℝ) := by
    have hpowers : (2083/20000 : ℝ)^4397 ≤ (6051773224605089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2083 : ℕ)^4397*100000000000000000000^1024 ≤ 6051773224605089^1024*20000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2083 20000 6051773224605089 100000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2083/20000 : ℝ)) (X := (6051773224605089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3943/25000 : ℝ) ^ (4397/1024 : ℝ) ≤ (35955857377131969/100000000000000000000 : ℝ) := by
    have hpowers : (3943/25000 : ℝ)^4397 ≤ (35955857377131969/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3943 : ℕ)^4397*100000000000000000000^1024 ≤ 35955857377131969^1024*25000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3943 25000 35955857377131969 100000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3943/25000 : ℝ)) (X := (35955857377131969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006051773224605089/50000000000000000000 : ℝ) ≤ (10000281861638039/10000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50006051773224605089/50000000000000000000 : ℝ)^1024 ≤ (10000281861638039/10000000000000000 : ℝ)^4397 := by
      have hnat : (50006051773224605089 : ℕ)^1024*10000000000000000^4397 ≤ 10000281861638039^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006051773224605089 50000000000000000000 10000281861638039 10000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281861638039/10000000000000000 : ℝ)) (X := (50006051773224605089/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021003815300868529/50000000000000000000 : ℝ) ≤ (1250122267695603/1250000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50021003815300868529/50000000000000000000 : ℝ)^1024 ≤ (1250122267695603/1250000000000000 : ℝ)^4397 := by
      have hnat : (50021003815300868529 : ℕ)^1024*1250000000000000^4397 ≤ 1250122267695603^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021003815300868529 50000000000000000000 1250122267695603 1250000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250122267695603/1250000000000000 : ℝ)) (X := (50021003815300868529/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035955857377131969/50000000000000000000 : ℝ) ≤ (10001674421491609/10000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50035955857377131969/50000000000000000000 : ℝ)^1024 ≤ (10001674421491609/10000000000000000 : ℝ)^4397 := by
      have hnat : (50035955857377131969 : ℕ)^1024*10000000000000000^4397 ≤ 10001674421491609^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035955857377131969 50000000000000000000 10001674421491609 10000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001674421491609/10000000000000000 : ℝ)) (X := (50035955857377131969/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6051773224605089/100000000000000000000 : ℝ) ≤ ((53557006421920043373/53570000000000000000 : ℝ)+2*(139255985357/107140000000000 : ℝ)*(2083/20000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (53557006421920043373/53570000000000000000 : ℝ)+2*(139255985357/107140000000000 : ℝ)*(2083/20000 : ℝ)=(10000281861638039/10000000000000000 : ℝ) by norm_num, show 1+2*(6051773224605089/100000000000000000000 : ℝ)=(50006051773224605089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35955857377131969/100000000000000000000 : ℝ)+(6051773224605089/100000000000000000000 : ℝ) ≤ ((53557006421920043373/53570000000000000000 : ℝ)+(139255985357/107140000000000 : ℝ)*((3943/25000 : ℝ)+(2083/20000 : ℝ)))^(4397/1024 : ℝ) := by
    rw [show (53557006421920043373/53570000000000000000 : ℝ)+(139255985357/107140000000000 : ℝ)*((3943/25000 : ℝ)+(2083/20000 : ℝ))=(1250122267695603/1250000000000000 : ℝ) by norm_num, show 1+(35955857377131969/100000000000000000000 : ℝ)+(6051773224605089/100000000000000000000 : ℝ)=(50021003815300868529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35955857377131969/100000000000000000000 : ℝ) ≤ ((53557006421920043373/53570000000000000000 : ℝ)+2*(139255985357/107140000000000 : ℝ)*(3943/25000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (53557006421920043373/53570000000000000000 : ℝ)+2*(139255985357/107140000000000 : ℝ)*(3943/25000 : ℝ)=(10001674421491609/10000000000000000 : ℝ) by norm_num, show 1+2*(35955857377131969/100000000000000000000 : ℝ)=(50035955857377131969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53557006421920043373/53570000000000000000 : ℝ)*(X 1 0+X 2 0)+(139255985357/107140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (3943/25000 : ℝ)) (c := (53557006421920043373/53570000000000000000 : ℝ)) (alpha := (139255985357/107140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53557006421920043373/53570000000000000000 : ℝ)*(X 0 1+X 2 1)+(139255985357/107140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (3943/25000 : ℝ)) (c := (53557006421920043373/53570000000000000000 : ℝ)) (alpha := (139255985357/107140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53557006421920043373/53570000000000000000 : ℝ)*(X 0 2+X 1 2)+(139255985357/107140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (3943/25000 : ℝ)) (c := (53557006421920043373/53570000000000000000 : ℝ)) (alpha := (139255985357/107140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1962849683/10000000000 : ℝ)*X 0 0+(1354094933/2500000000 : ℝ)*X 0 1+(5239139447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83583839/156250000 : ℝ)*X 1 0+(-2005122/9765625 : ℝ)*X 1 1+(1309784749/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337341411/2500000000 : ℝ)*X 2 0+(2619569503/5000000000 : ℝ)*X 2 1+(-256655623/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215075733/500000000 : ℝ)*X 0 0+(514127473/1250000000 : ℝ)*X 0 1+(899542827/2000000000 : ℝ)*X 0 2+(215075733/500000000 : ℝ)*X 1 0+(514127473/1250000000 : ℝ)*X 1 1+(899542827/2000000000 : ℝ)*X 1 2+(215075733/500000000 : ℝ)*X 2 0+(514127473/1250000000 : ℝ)*X 2 1+(899542827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1962864241/10000000000 : ℝ)*X 0 0+(5239844853/10000000000 : ℝ)*X 0 1+(5415670687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651624039/5000000000 : ℝ)*X 1 0+(-938356887/5000000000 : ℝ)*X 1 1+(5415670621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303246743/10000000000 : ℝ)*X 2 0+(1353917931/2500000000 : ℝ)*X 2 1+(-1876714083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860309291/2000000000 : ℝ)*X 0 0+(562023011/1250000000 : ℝ)*X 0 1+(4114559519/10000000000 : ℝ)*X 0 2+(860309291/2000000000 : ℝ)*X 1 0+(562023011/1250000000 : ℝ)*X 1 1+(4114559519/10000000000 : ℝ)*X 1 2+(860309291/2000000000 : ℝ)*X 2 0+(562023011/1250000000 : ℝ)*X 2 1+(4114559519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1190341078777937669529761829/121750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1576872253/100000000000000 : ℝ)*(base19) + (755112941/50000000000000 : ℝ)*(base23) + (6312693/100000000000000 : ℝ)*(lower2) + (97888251/50000000000000 : ℝ)*(upper3) + (55913073/50000000000000 : ℝ)*(upper5) + (412078833942009/10000000000000 : ℝ)*(major0) + (412078833942009/10000000000000 : ℝ)*(major1) + (1030197084855023/25000000000000 : ℝ)*(major2) + (564207833192409/10000000000000 : ℝ)*(sp0) + (5642093777079191/100000000000000 : ℝ)*(sp1) + (5642093843725561/100000000000000 : ℝ)*(sp2) + (649868278457321/25000000000000 : ℝ)*(sp3) + (17022027353/100000000000000 : ℝ)*(sp4) + (7885161819/100000000000000 : ℝ)*(sp7) + (2599480998991103/100000000000000 : ℝ)*(f.failure) + (1410523838487861/25000000000000 : ℝ)*(f.sum) + (17492444945007/5357000000000000000000000000 : ℝ)*base66 + (229869455564358513/48700000000000000000000000000000 : ℝ)*base68 + (9024902621330337421/1339250000000000000000000000000000 : ℝ)*base70 + (51346829030841487/48700000000000000000000000000000 : ℝ)*base71 + (7747382307127/5357000000000000000000000000 : ℝ)*base73 + (12058775950259087421/1339250000000000000000000000000000 : ℝ)*base76 + (2925543508579956357/535700000000000000000000000000000 : ℝ)*base77 + (1682295381497456357/535700000000000000000000000000000 : ℝ)*base79 + (37611922583459/5357000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (113393809/10000000000000000000000 : ℝ)*base89 + (113393809/10000000000000000000000 : ℝ)*base91 + (86606191/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8321350756789714780399599/1071400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241014039/100000000000000 : ℝ)*(base8) + (1226023281/100000000000000 : ℝ)*(base21) + (167059903/100000000000000 : ℝ)*(upper2) + (17752547/100000000000000 : ℝ)*(lower4) + (3323131901921/80000000000 : ℝ)*(major0) + (3323131901921/80000000000 : ℝ)*(major1) + (3323131901921/80000000000 : ℝ)*(major2) + (1584823949/100000000000000 : ℝ)*(sp0) + (6852323467/100000000000000 : ℝ)*(sp1) + (6554955443/100000000000000 : ℝ)*(sp2) + (177732804556093/3125000000000 : ℝ)*(sp4) + (5687444719309497/100000000000000 : ℝ)*(sp5) + (5687443790654239/100000000000000 : ℝ)*(sp6) + (655094481069039/25000000000000 : ℝ)*(sp7) + (655094481069039/25000000000000 : ℝ)*(f.failure) + (5687451571632963/100000000000000 : ℝ)*(f.sum) + (104331781556879/5357000000000000000000000000 : ℝ)*base66 + (39099540023374867/4285600000000000000000000000000 : ℝ)*base68 + (18932568202202867/4285600000000000000000000000000 : ℝ)*base70 + (26023085255277267/4285600000000000000000000000000 : ℝ)*base72 + (11983994443/5231445312500000000000000 : ℝ)*base73 + (30433070316825267/4285600000000000000000000000000 : ℝ)*base76 + (17548999630045133/4285600000000000000000000000000 : ℝ)*base77 + (48046533564803667/4285600000000000000000000000000 : ℝ)*base80 + (2504287292699/1071400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2876383/2500000000000000000000 : ℝ)*base90 + (2876383/2500000000000000000000 : ℝ)*base92 + (2876383/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1438_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3943/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2797/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7471/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1438_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1438_s4_0 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-490926497/2500000000 : ℝ)*x 0 + (1081808761/2000000000 : ℝ)*x 1 + (5245911269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490926497/2500000000 : ℝ)^2199 ≤ (748871106129/6250000000000 : ℝ)^1687 := by
    have hnat : (490926497 : ℕ)^2199*6250000000000^1687 ≤ 748871106129^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490926497 2500000000 748871106129 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081808761/2000000000 : ℝ)^2199 ≤ (11221819798377/25000000000000 : ℝ)^1687 := by
    have hnat : (1081808761 : ℕ)^2199*25000000000000^1687 ≤ 11221819798377^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081808761 2000000000 11221819798377 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245911269/10000000000 : ℝ)^2199 ≤ (8626156617859/20000000000000 : ℝ)^1687 := by
    have hnat : (5245911269 : ℕ)^2199*20000000000000^1687 ≤ 8626156617859^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245911269 10000000000 8626156617859 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490926497/2500000000 : ℝ), (1081808761/2000000000 : ℝ), (5245911269/10000000000 : ℝ)] ![(748871106129/6250000000000 : ℝ), (11221819798377/25000000000000 : ℝ), (8626156617859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490926497/2500000000 : ℝ)|^2199 ≤ (748871106129/6250000000000 : ℝ)^1687
        have hw : |(-490926497/2500000000 : ℝ)|=(490926497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081808761/2000000000 : ℝ)|^2199 ≤ (11221819798377/25000000000000 : ℝ)^1687
        have hw : |(1081808761/2000000000 : ℝ)|=(1081808761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245911269/10000000000 : ℝ)|^2199 ≤ (8626156617859/20000000000000 : ℝ)^1687
        have hw : |(5245911269/10000000000 : ℝ)|=(5245911269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_1 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673734789/5000000000 : ℝ)*x 0 + (-1023387963/5000000000 : ℝ)*x 1 + (2622955789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673734789/5000000000 : ℝ)^2199 ≤ (44222375055869/100000000000000 : ℝ)^1687 := by
    have hnat : (2673734789 : ℕ)^2199*100000000000000^1687 ≤ 44222375055869^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673734789 5000000000 44222375055869 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023387963/5000000000 : ℝ)^2199 ≤ (12646838538983/100000000000000 : ℝ)^1687 := by
    have hnat : (1023387963 : ℕ)^2199*100000000000000^1687 ≤ 12646838538983^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023387963 5000000000 12646838538983 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622955789/5000000000 : ℝ)^2199 ≤ (21565393200437/50000000000000 : ℝ)^1687 := by
    have hnat : (2622955789 : ℕ)^2199*50000000000000^1687 ≤ 21565393200437^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622955789 5000000000 21565393200437 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673734789/5000000000 : ℝ), (-1023387963/5000000000 : ℝ), (2622955789/5000000000 : ℝ)] ![(44222375055869/100000000000000 : ℝ), (12646838538983/100000000000000 : ℝ), (21565393200437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673734789/5000000000 : ℝ)|^2199 ≤ (44222375055869/100000000000000 : ℝ)^1687
        have hw : |(2673734789/5000000000 : ℝ)|=(2673734789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023387963/5000000000 : ℝ)|^2199 ≤ (12646838538983/100000000000000 : ℝ)^1687
        have hw : |(-1023387963/5000000000 : ℝ)|=(1023387963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622955789/5000000000 : ℝ)|^2199 ≤ (21565393200437/50000000000000 : ℝ)^1687
        have hw : |(2622955789/5000000000 : ℝ)|=(2622955789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_2 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069493957/2000000000 : ℝ)*x 0 + (1311477873/2500000000 : ℝ)*x 1 + (-2046775763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069493957/2000000000 : ℝ)^2199 ≤ (11055594321813/25000000000000 : ℝ)^1687 := by
    have hnat : (1069493957 : ℕ)^2199*25000000000000^1687 ≤ 11055594321813^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069493957 2000000000 11055594321813 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311477873/2500000000 : ℝ)^2199 ≤ (8626157095841/20000000000000 : ℝ)^1687 := by
    have hnat : (1311477873 : ℕ)^2199*20000000000000^1687 ≤ 8626157095841^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311477873 2500000000 8626157095841 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046775763/10000000000 : ℝ)^2199 ≤ (252936744523/2000000000000 : ℝ)^1687 := by
    have hnat : (2046775763 : ℕ)^2199*2000000000000^1687 ≤ 252936744523^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046775763 10000000000 252936744523 2000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069493957/2000000000 : ℝ), (1311477873/2500000000 : ℝ), (-2046775763/10000000000 : ℝ)] ![(11055594321813/25000000000000 : ℝ), (8626157095841/20000000000000 : ℝ), (252936744523/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069493957/2000000000 : ℝ)|^2199 ≤ (11055594321813/25000000000000 : ℝ)^1687
        have hw : |(1069493957/2000000000 : ℝ)|=(1069493957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311477873/2500000000 : ℝ)|^2199 ≤ (8626157095841/20000000000000 : ℝ)^1687
        have hw : |(1311477873/2500000000 : ℝ)|=(1311477873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2046775763/10000000000 : ℝ)|^2199 ≤ (252936744523/2000000000000 : ℝ)^1687
        have hw : |(-2046775763/10000000000 : ℝ)|=(2046775763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_3 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302040001/10000000000 : ℝ)*x 0 + (4128267059/10000000000 : ℝ)*x 1 + (112058511/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302040001/10000000000 : ℝ)^2199 ≤ (41629924973/125000000000 : ℝ)^1687 := by
    have hnat : (4302040001 : ℕ)^2199*125000000000^1687 ≤ 41629924973^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302040001 10000000000 41629924973 125000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128267059/10000000000 : ℝ)^2199 ≤ (31561259902951/100000000000000 : ℝ)^1687 := by
    have hnat : (4128267059 : ℕ)^2199*100000000000000^1687 ≤ 31561259902951^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128267059 10000000000 31561259902951 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112058511/250000000 : ℝ)^2199 ≤ (35134800093189/100000000000000 : ℝ)^1687 := by
    have hnat : (112058511 : ℕ)^2199*100000000000000^1687 ≤ 35134800093189^1687*250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112058511 250000000 35134800093189 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302040001/10000000000 : ℝ), (4128267059/10000000000 : ℝ), (112058511/250000000 : ℝ)] ![(41629924973/125000000000 : ℝ), (31561259902951/100000000000000 : ℝ), (35134800093189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302040001/10000000000 : ℝ)|^2199 ≤ (41629924973/125000000000 : ℝ)^1687
        have hw : |(4302040001/10000000000 : ℝ)|=(4302040001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128267059/10000000000 : ℝ)|^2199 ≤ (31561259902951/100000000000000 : ℝ)^1687
        have hw : |(4128267059/10000000000 : ℝ)|=(4128267059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112058511/250000000 : ℝ)|^2199 ≤ (35134800093189/100000000000000 : ℝ)^1687
        have hw : |(112058511/250000000 : ℝ)|=(112058511/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_4 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1963717927/10000000000 : ℝ)*x 0 + (1311627319/2500000000 : ℝ)*x 1 + (5408442531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963717927/10000000000 : ℝ)^2199 ≤ (2995508163881/25000000000000 : ℝ)^1687 := by
    have hnat : (1963717927 : ℕ)^2199*25000000000000^1687 ≤ 2995508163881^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963717927 10000000000 2995508163881 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311627319/2500000000 : ℝ)^2199 ≤ (5392149011269/12500000000000 : ℝ)^1687 := by
    have hnat : (1311627319 : ℕ)^2199*12500000000000^1687 ≤ 5392149011269^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311627319 2500000000 5392149011269 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408442531/10000000000 : ℝ)^2199 ≤ (1402524225969/3125000000000 : ℝ)^1687 := by
    have hnat : (5408442531 : ℕ)^2199*3125000000000^1687 ≤ 1402524225969^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408442531 10000000000 1402524225969 3125000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1963717927/10000000000 : ℝ), (1311627319/2500000000 : ℝ), (5408442531/10000000000 : ℝ)] ![(2995508163881/25000000000000 : ℝ), (5392149011269/12500000000000 : ℝ), (1402524225969/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1963717927/10000000000 : ℝ)|^2199 ≤ (2995508163881/25000000000000 : ℝ)^1687
        have hw : |(-1963717927/10000000000 : ℝ)|=(1963717927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311627319/2500000000 : ℝ)|^2199 ≤ (5392149011269/12500000000000 : ℝ)^1687
        have hw : |(1311627319/2500000000 : ℝ)|=(1311627319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408442531/10000000000 : ℝ)|^2199 ≤ (1402524225969/3125000000000 : ℝ)^1687
        have hw : |(5408442531/10000000000 : ℝ)|=(5408442531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_5 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061004579/2000000000 : ℝ)*x 0 + (-942122399/5000000000 : ℝ)*x 1 + (5408442501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061004579/2000000000 : ℝ)^2199 ≤ (4376536764997/10000000000000 : ℝ)^1687 := by
    have hnat : (1061004579 : ℕ)^2199*10000000000000^1687 ≤ 4376536764997^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061004579 2000000000 4376536764997 10000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942122399/5000000000 : ℝ)^2199 ≤ (11353857432889/100000000000000 : ℝ)^1687 := by
    have hnat : (942122399 : ℕ)^2199*100000000000000^1687 ≤ 11353857432889^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942122399 5000000000 11353857432889 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408442501/10000000000 : ℝ)^2199 ≤ (8976154981301/20000000000000 : ℝ)^1687 := by
    have hnat : (5408442501 : ℕ)^2199*20000000000000^1687 ≤ 8976154981301^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408442501 10000000000 8976154981301 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061004579/2000000000 : ℝ), (-942122399/5000000000 : ℝ), (5408442501/10000000000 : ℝ)] ![(4376536764997/10000000000000 : ℝ), (11353857432889/100000000000000 : ℝ), (8976154981301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061004579/2000000000 : ℝ)|^2199 ≤ (4376536764997/10000000000000 : ℝ)^1687
        have hw : |(1061004579/2000000000 : ℝ)|=(1061004579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942122399/5000000000 : ℝ)|^2199 ≤ (11353857432889/100000000000000 : ℝ)^1687
        have hw : |(-942122399/5000000000 : ℝ)|=(942122399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408442501/10000000000 : ℝ)|^2199 ≤ (8976154981301/20000000000000 : ℝ)^1687
        have hw : |(5408442501/10000000000 : ℝ)|=(5408442501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_6 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305022849/10000000000 : ℝ)*x 0 + (338027659/625000000 : ℝ)*x 1 + (-1884244801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305022849/10000000000 : ℝ)^2199 ≤ (8753073431061/20000000000000 : ℝ)^1687 := by
    have hnat : (5305022849 : ℕ)^2199*20000000000000^1687 ≤ 8753073431061^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305022849 10000000000 8753073431061 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338027659/625000000 : ℝ)^2199 ≤ (44880775371627/100000000000000 : ℝ)^1687 := by
    have hnat : (338027659 : ℕ)^2199*100000000000000^1687 ≤ 44880775371627^1687*625000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338027659 625000000 44880775371627 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884244801/10000000000 : ℝ)^2199 ≤ (2838464364113/25000000000000 : ℝ)^1687 := by
    have hnat : (1884244801 : ℕ)^2199*25000000000000^1687 ≤ 2838464364113^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884244801 10000000000 2838464364113 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305022849/10000000000 : ℝ), (338027659/625000000 : ℝ), (-1884244801/10000000000 : ℝ)] ![(8753073431061/20000000000000 : ℝ), (44880775371627/100000000000000 : ℝ), (2838464364113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305022849/10000000000 : ℝ)|^2199 ≤ (8753073431061/20000000000000 : ℝ)^1687
        have hw : |(5305022849/10000000000 : ℝ)|=(5305022849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338027659/625000000 : ℝ)|^2199 ≤ (44880775371627/100000000000000 : ℝ)^1687
        have hw : |(338027659/625000000 : ℝ)|=(338027659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884244801/10000000000 : ℝ)|^2199 ≤ (2838464364113/25000000000000 : ℝ)^1687
        have hw : |(-1884244801/10000000000 : ℝ)|=(1884244801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s4_7 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537758203/1250000000 : ℝ)*x 0 + (1120260687/2500000000 : ℝ)*x 1 + (2064785751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537758203/1250000000 : ℝ)^2199 ≤ (33304198538607/100000000000000 : ℝ)^1687 := by
    have hnat : (537758203 : ℕ)^2199*100000000000000^1687 ≤ 33304198538607^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537758203 1250000000 33304198538607 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120260687/2500000000 : ℝ)^2199 ≤ (35121541564257/100000000000000 : ℝ)^1687 := by
    have hnat : (1120260687 : ℕ)^2199*100000000000000^1687 ≤ 35121541564257^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120260687 2500000000 35121541564257 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064785751/5000000000 : ℝ)^2199 ≤ (7893564970279/25000000000000 : ℝ)^1687 := by
    have hnat : (2064785751 : ℕ)^2199*25000000000000^1687 ≤ 7893564970279^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064785751 5000000000 7893564970279 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537758203/1250000000 : ℝ), (1120260687/2500000000 : ℝ), (2064785751/5000000000 : ℝ)] ![(33304198538607/100000000000000 : ℝ), (35121541564257/100000000000000 : ℝ), (7893564970279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537758203/1250000000 : ℝ)|^2199 ≤ (33304198538607/100000000000000 : ℝ)^1687
        have hw : |(537758203/1250000000 : ℝ)|=(537758203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120260687/2500000000 : ℝ)|^2199 ≤ (35121541564257/100000000000000 : ℝ)^1687
        have hw : |(1120260687/2500000000 : ℝ)|=(1120260687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064785751/5000000000 : ℝ)|^2199 ≤ (7893564970279/25000000000000 : ℝ)^1687
        have hw : |(2064785751/5000000000 : ℝ)|=(2064785751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1438_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7471/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2797/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11333/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14789/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7471/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2797/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7471/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2797/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7471/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2797/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7471/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2797/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7471/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2797/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7471/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2797/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2797/25000 : ℝ) ^ (4397/1024 : ℝ) ≤ (4114954893847841/50000000000000000000 : ℝ) := by
    have hpowers : (2797/25000 : ℝ)^4397 ≤ (4114954893847841/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2797 : ℕ)^4397*50000000000000000000^1024 ≤ 4114954893847841^1024*25000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2797 25000 4114954893847841 50000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2797/25000 : ℝ)) (X := (4114954893847841/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7471/50000 : ℝ) ^ (4397/1024 : ℝ) ≤ (28507310432841397/100000000000000000000 : ℝ) := by
    have hpowers : (7471/50000 : ℝ)^4397 ≤ (28507310432841397/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7471 : ℕ)^4397*100000000000000000000^1024 ≤ 28507310432841397^1024*50000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7471 50000 28507310432841397 100000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7471/50000 : ℝ)) (X := (28507310432841397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004114954893847841/25000000000000000000 : ℝ) ≤ (2500095825513159/2500000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (25004114954893847841/25000000000000000000 : ℝ)^1024 ≤ (2500095825513159/2500000000000000 : ℝ)^4397 := by
      have hnat : (25004114954893847841 : ℕ)^1024*2500000000000000^4397 ≤ 2500095825513159^4397*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004114954893847841 25000000000000000000 2500095825513159 2500000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500095825513159/2500000000000000 : ℝ)) (X := (25004114954893847841/25000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036737220220537079/100000000000000000000 : ℝ) ≤ (2500213859528317/2500000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (100036737220220537079/100000000000000000000 : ℝ)^1024 ≤ (2500213859528317/2500000000000000 : ℝ)^4397 := by
      have hnat : (100036737220220537079 : ℕ)^1024*2500000000000000^4397 ≤ 2500213859528317^4397*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036737220220537079 100000000000000000000 2500213859528317 2500000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500213859528317/2500000000000000 : ℝ)) (X := (100036737220220537079/100000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028507310432841397/50000000000000000000 : ℝ) ≤ (100013275741739/100000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50028507310432841397/50000000000000000000 : ℝ)^1024 ≤ (100013275741739/100000000000000 : ℝ)^4397 := by
      have hnat : (50028507310432841397 : ℕ)^1024*100000000000000^4397 ≤ 100013275741739^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028507310432841397 50000000000000000000 100013275741739 100000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100013275741739/100000000000000 : ℝ)) (X := (50028507310432841397/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4114954893847841/50000000000000000000 : ℝ) ≤ ((4691359299926611739/4692500000000000000 : ℝ)+2*(59017007579/46925000000000 : ℝ)*(2797/25000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (4691359299926611739/4692500000000000000 : ℝ)+2*(59017007579/46925000000000 : ℝ)*(2797/25000 : ℝ)=(2500095825513159/2500000000000000 : ℝ) by norm_num, show 1+2*(4114954893847841/50000000000000000000 : ℝ)=(25004114954893847841/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28507310432841397/100000000000000000000 : ℝ)+(4114954893847841/50000000000000000000 : ℝ) ≤ ((4691359299926611739/4692500000000000000 : ℝ)+(59017007579/46925000000000 : ℝ)*((7471/50000 : ℝ)+(2797/25000 : ℝ)))^(4397/1024 : ℝ) := by
    rw [show (4691359299926611739/4692500000000000000 : ℝ)+(59017007579/46925000000000 : ℝ)*((7471/50000 : ℝ)+(2797/25000 : ℝ))=(2500213859528317/2500000000000000 : ℝ) by norm_num, show 1+(28507310432841397/100000000000000000000 : ℝ)+(4114954893847841/50000000000000000000 : ℝ)=(100036737220220537079/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28507310432841397/100000000000000000000 : ℝ) ≤ ((4691359299926611739/4692500000000000000 : ℝ)+2*(59017007579/46925000000000 : ℝ)*(7471/50000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (4691359299926611739/4692500000000000000 : ℝ)+2*(59017007579/46925000000000 : ℝ)*(7471/50000 : ℝ)=(100013275741739/100000000000000 : ℝ) by norm_num, show 1+2*(28507310432841397/100000000000000000000 : ℝ)=(50028507310432841397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4691359299926611739/4692500000000000000 : ℝ)*(X 1 0+X 2 0)+(59017007579/46925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2797/25000 : ℝ)) (hi := (7471/50000 : ℝ)) (c := (4691359299926611739/4692500000000000000 : ℝ)) (alpha := (59017007579/46925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4691359299926611739/4692500000000000000 : ℝ)*(X 0 1+X 2 1)+(59017007579/46925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2797/25000 : ℝ)) (hi := (7471/50000 : ℝ)) (c := (4691359299926611739/4692500000000000000 : ℝ)) (alpha := (59017007579/46925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4691359299926611739/4692500000000000000 : ℝ)*(X 0 2+X 1 2)+(59017007579/46925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (2797/25000 : ℝ)) (hi := (7471/50000 : ℝ)) (c := (4691359299926611739/4692500000000000000 : ℝ)) (alpha := (59017007579/46925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-490926497/2500000000 : ℝ)*X 0 0+(1081808761/2000000000 : ℝ)*X 0 1+(5245911269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673734789/5000000000 : ℝ)*X 1 0+(-1023387963/5000000000 : ℝ)*X 1 1+(2622955789/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069493957/2000000000 : ℝ)*X 2 0+(1311477873/2500000000 : ℝ)*X 2 1+(-2046775763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302040001/10000000000 : ℝ)*X 0 0+(4128267059/10000000000 : ℝ)*X 0 1+(112058511/250000000 : ℝ)*X 0 2+(4302040001/10000000000 : ℝ)*X 1 0+(4128267059/10000000000 : ℝ)*X 1 1+(112058511/250000000 : ℝ)*X 1 2+(4302040001/10000000000 : ℝ)*X 2 0+(4128267059/10000000000 : ℝ)*X 2 1+(112058511/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1963717927/10000000000 : ℝ)*X 0 0+(1311627319/2500000000 : ℝ)*X 0 1+(5408442531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061004579/2000000000 : ℝ)*X 1 0+(-942122399/5000000000 : ℝ)*X 1 1+(5408442501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305022849/10000000000 : ℝ)*X 2 0+(338027659/625000000 : ℝ)*X 2 1+(-1884244801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537758203/1250000000 : ℝ)*X 0 0+(1120260687/2500000000 : ℝ)*X 0 1+(2064785751/5000000000 : ℝ)*X 0 2+(537758203/1250000000 : ℝ)*X 1 0+(1120260687/2500000000 : ℝ)*X 1 1+(2064785751/5000000000 : ℝ)*X 1 2+(537758203/1250000000 : ℝ)*X 2 0+(1120260687/2500000000 : ℝ)*X 2 1+(2064785751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18787828448381788497850467/2932812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (654183751/100000000000000 : ℝ)*(base19) + (8003777/1250000000000 : ℝ)*(base23) + (67157421/50000000000000 : ℝ)*(lower2) + (17485177/50000000000000 : ℝ)*(upper3) + (24257803/25000000000000 : ℝ)*(upper5) + (6995565551703/156250000000 : ℝ)*(major0) + (6995565551703/156250000000 : ℝ)*(major1) + (6995565551703/156250000000 : ℝ)*(major2) + (6130005994715737/100000000000000 : ℝ)*(sp0) + (191563561820331/3125000000000 : ℝ)*(sp1) + (6130033992132183/100000000000000 : ℝ)*(sp2) + (1412140330055663/50000000000000 : ℝ)*(sp3) + (14318859303/50000000000000 : ℝ)*(sp4) + (42000491/500000000000 : ℝ)*(sp7) + (1412144530104763/50000000000000 : ℝ)*(f.failure) + (6130034632434343/100000000000000 : ℝ)*(f.sum) + (947614381559/234625000000000000000000000 : ℝ)*base66 + (17091054194922761/5865625000000000000000000000000 : ℝ)*base67 + (30163306291772761/5865625000000000000000000000000 : ℝ)*base69 + (31134031589681693/2932812500000000000000000000000 : ℝ)*base71 + (222721624291/187700000000000000000000000 : ℝ)*base73 + (5085054319445983/733203125000000000000000000000 : ℝ)*base76 + (50899892557229011/5865625000000000000000000000000 : ℝ)*base77 + (10723339894905807/2932812500000000000000000000000 : ℝ)*base80 + (2654904996103/1877000000000000000000000000 : ℝ)*base82 + (12255211/5000000000000000000000 : ℝ)*base90 + (12255211/5000000000000000000000 : ℝ)*base92 + (12255211/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13709471418612180697671/1173125000000000000000000000 : ℝ) := by norm_num
    linear_combination (23941241/1250000000000 : ℝ)*(base19) + (1024061401/50000000000000 : ℝ)*(base23) + (229858587/100000000000000 : ℝ)*(upper3) + (86994897/100000000000000 : ℝ)*(lower4) + (24167421/10000000000000 : ℝ)*(upper5) + (1127570539106343/25000000000000 : ℝ)*(major0) + (1127570539106343/25000000000000 : ℝ)*(major1) + (1127570539106343/25000000000000 : ℝ)*(major2) + (19412796473/50000000000000 : ℝ)*(sp1) + (41622979949/100000000000000 : ℝ)*(sp2) + (1543845483460681/25000000000000 : ℝ)*(sp4) + (3087670596475249/50000000000000 : ℝ)*(sp5) + (6175338262739973/100000000000000 : ℝ)*(sp6) + (2845181989465229/100000000000000 : ℝ)*(sp7) + (2845181989465229/100000000000000 : ℝ)*(f.failure) + (1543845483460681/25000000000000 : ℝ)*(f.sum) + (12480632983107/2346250000000000000000000000 : ℝ)*base66 + (724441648682110477/117312500000000000000000000000000 : ℝ)*base67 + (616269987818235477/117312500000000000000000000000000 : ℝ)*base69 + (91809256618264523/117312500000000000000000000000000 : ℝ)*base72 + (1747729119717/2346250000000000000000000000 : ℝ)*base74 + (2216136821978610477/117312500000000000000000000000000 : ℝ)*base75 + (93092132623764523/117312500000000000000000000000000 : ℝ)*base78 + (1145071162086139523/117312500000000000000000000000000 : ℝ)*base80 + (13713919470589/4692500000000000000000000000 : ℝ)*base82 + (2222813/10000000000000000000000 : ℝ)*base90 + (2222813/10000000000000000000000 : ℝ)*base92 + (2222813/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1438_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7471/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2797/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1438_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1438_s5_0 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1963830841/10000000000 : ℝ)*x 0 + (2703962273/5000000000 : ℝ)*x 1 + (2623474127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963830841/10000000000 : ℝ)^2199 ≤ (11982930731591/100000000000000 : ℝ)^1687 := by
    have hnat : (1963830841 : ℕ)^2199*100000000000000^1687 ≤ 11982930731591^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963830841 10000000000 11982930731591 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703962273/5000000000 : ℝ)^2199 ≤ (5609396547379/12500000000000 : ℝ)^1687 := by
    have hnat : (2703962273 : ℕ)^2199*12500000000000^1687 ≤ 5609396547379^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703962273 5000000000 5609396547379 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623474127/5000000000 : ℝ)^2199 ≤ (43141896875823/100000000000000 : ℝ)^1687 := by
    have hnat : (2623474127 : ℕ)^2199*100000000000000^1687 ≤ 43141896875823^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623474127 5000000000 43141896875823 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1963830841/10000000000 : ℝ), (2703962273/5000000000 : ℝ), (2623474127/5000000000 : ℝ)] ![(11982930731591/100000000000000 : ℝ), (5609396547379/12500000000000 : ℝ), (43141896875823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1963830841/10000000000 : ℝ)|^2199 ≤ (11982930731591/100000000000000 : ℝ)^1687
        have hw : |(-1963830841/10000000000 : ℝ)|=(1963830841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703962273/5000000000 : ℝ)|^2199 ≤ (5609396547379/12500000000000 : ℝ)^1687
        have hw : |(2703962273/5000000000 : ℝ)|=(2703962273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623474127/5000000000 : ℝ)|^2199 ≤ (43141896875823/100000000000000 : ℝ)^1687
        have hw : |(2623474127/5000000000 : ℝ)|=(2623474127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_1 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347181021/10000000000 : ℝ)*x 0 + (-2045782053/10000000000 : ℝ)*x 1 + (5246948653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347181021/10000000000 : ℝ)^2199 ≤ (44219264543407/100000000000000 : ℝ)^1687 := by
    have hnat : (5347181021 : ℕ)^2199*100000000000000^1687 ≤ 44219264543407^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347181021 10000000000 44219264543407 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045782053/10000000000 : ℝ)^2199 ≤ (12638834287837/100000000000000 : ℝ)^1687 := by
    have hnat : (2045782053 : ℕ)^2199*100000000000000^1687 ≤ 12638834287837^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045782053 10000000000 12638834287837 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246948653/10000000000 : ℝ)^2199 ≤ (8628380230439/20000000000000 : ℝ)^1687 := by
    have hnat : (5246948653 : ℕ)^2199*20000000000000^1687 ≤ 8628380230439^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246948653 10000000000 8628380230439 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347181021/10000000000 : ℝ), (-2045782053/10000000000 : ℝ), (5246948653/10000000000 : ℝ)] ![(44219264543407/100000000000000 : ℝ), (12638834287837/100000000000000 : ℝ), (8628380230439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347181021/10000000000 : ℝ)|^2199 ≤ (44219264543407/100000000000000 : ℝ)^1687
        have hw : |(5347181021/10000000000 : ℝ)|=(5347181021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045782053/10000000000 : ℝ)|^2199 ≤ (12638834287837/100000000000000 : ℝ)^1687
        have hw : |(-2045782053/10000000000 : ℝ)|=(2045782053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246948653/10000000000 : ℝ)|^2199 ≤ (8628380230439/20000000000000 : ℝ)^1687
        have hw : |(5246948653/10000000000 : ℝ)|=(5246948653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_2 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347180933/10000000000 : ℝ)*x 0 + (2623474559/5000000000 : ℝ)*x 1 + (-127861347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347180933/10000000000 : ℝ)^2199 ≤ (8843852718963/20000000000000 : ℝ)^1687 := by
    have hnat : (5347180933 : ℕ)^2199*20000000000000^1687 ≤ 8843852718963^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347180933 10000000000 8843852718963 20000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623474559/5000000000 : ℝ)^2199 ≤ (43141906135937/100000000000000 : ℝ)^1687 := by
    have hnat : (2623474559 : ℕ)^2199*100000000000000^1687 ≤ 43141906135937^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623474559 5000000000 43141906135937 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127861347/625000000 : ℝ)^2199 ≤ (12638830253283/100000000000000 : ℝ)^1687 := by
    have hnat : (127861347 : ℕ)^2199*100000000000000^1687 ≤ 12638830253283^1687*625000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127861347 625000000 12638830253283 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347180933/10000000000 : ℝ), (2623474559/5000000000 : ℝ), (-127861347/625000000 : ℝ)] ![(8843852718963/20000000000000 : ℝ), (43141906135937/100000000000000 : ℝ), (12638830253283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347180933/10000000000 : ℝ)|^2199 ≤ (8843852718963/20000000000000 : ℝ)^1687
        have hw : |(5347180933/10000000000 : ℝ)|=(5347180933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623474559/5000000000 : ℝ)|^2199 ≤ (43141906135937/100000000000000 : ℝ)^1687
        have hw : |(2623474559/5000000000 : ℝ)|=(2623474559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127861347/625000000 : ℝ)|^2199 ≤ (12638830253283/100000000000000 : ℝ)^1687
        have hw : |(-127861347/625000000 : ℝ)|=(127861347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_3 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4302115799/10000000000 : ℝ)*x 0 + (2065300303/5000000000 : ℝ)*x 1 + (559998651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302115799/10000000000 : ℝ)^2199 ≤ (2081544053311/6250000000000 : ℝ)^1687 := by
    have hnat : (4302115799 : ℕ)^2199*6250000000000^1687 ≤ 2081544053311^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302115799 10000000000 2081544053311 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065300303/5000000000 : ℝ)^2199 ≤ (31584516731587/100000000000000 : ℝ)^1687 := by
    have hnat : (2065300303 : ℕ)^2199*100000000000000^1687 ≤ 31584516731587^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065300303 5000000000 31584516731587 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559998651/1250000000 : ℝ)^2199 ≤ (35110778395169/100000000000000 : ℝ)^1687 := by
    have hnat : (559998651 : ℕ)^2199*100000000000000^1687 ≤ 35110778395169^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559998651 1250000000 35110778395169 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302115799/10000000000 : ℝ), (2065300303/5000000000 : ℝ), (559998651/1250000000 : ℝ)] ![(2081544053311/6250000000000 : ℝ), (31584516731587/100000000000000 : ℝ), (35110778395169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302115799/10000000000 : ℝ)|^2199 ≤ (2081544053311/6250000000000 : ℝ)^1687
        have hw : |(4302115799/10000000000 : ℝ)|=(4302115799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065300303/5000000000 : ℝ)|^2199 ≤ (31584516731587/100000000000000 : ℝ)^1687
        have hw : |(2065300303/5000000000 : ℝ)|=(2065300303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559998651/1250000000 : ℝ)|^2199 ≤ (35110778395169/100000000000000 : ℝ)^1687
        have hw : |(559998651/1250000000 : ℝ)|=(559998651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_4 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-392768369/2000000000 : ℝ)*x 0 + (5247531507/10000000000 : ℝ)*x 1 + (5407338507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392768369/2000000000 : ℝ)^2199 ≤ (11983018254163/100000000000000 : ℝ)^1687 := by
    have hnat : (392768369 : ℕ)^2199*100000000000000^1687 ≤ 11983018254163^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392768369 2000000000 11983018254163 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247531507/10000000000 : ℝ)^2199 ≤ (21574074063209/50000000000000 : ℝ)^1687 := by
    have hnat : (5247531507 : ℕ)^2199*50000000000000^1687 ≤ 21574074063209^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247531507 10000000000 21574074063209 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407338507/10000000000 : ℝ)^2199 ≤ (11217208402127/25000000000000 : ℝ)^1687 := by
    have hnat : (5407338507 : ℕ)^2199*25000000000000^1687 ≤ 11217208402127^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407338507 10000000000 11217208402127 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392768369/2000000000 : ℝ), (5247531507/10000000000 : ℝ), (5407338507/10000000000 : ℝ)] ![(11983018254163/100000000000000 : ℝ), (21574074063209/50000000000000 : ℝ), (11217208402127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392768369/2000000000 : ℝ)|^2199 ≤ (11983018254163/100000000000000 : ℝ)^1687
        have hw : |(-392768369/2000000000 : ℝ)|=(392768369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247531507/10000000000 : ℝ)|^2199 ≤ (21574074063209/50000000000000 : ℝ)^1687
        have hw : |(5247531507/10000000000 : ℝ)|=(5247531507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407338507/10000000000 : ℝ)|^2199 ≤ (11217208402127/25000000000000 : ℝ)^1687
        have hw : |(5407338507/10000000000 : ℝ)|=(5407338507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_5 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061059003/2000000000 : ℝ)*x 0 + (-471348151/2500000000 : ℝ)*x 1 + (2703669197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061059003/2000000000 : ℝ)^2199 ≤ (43768293939599/100000000000000 : ℝ)^1687 := by
    have hnat : (1061059003 : ℕ)^2199*100000000000000^1687 ≤ 43768293939599^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061059003 2000000000 43768293939599 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471348151/2500000000 : ℝ)^2199 ≤ (11362873660927/100000000000000 : ℝ)^1687 := by
    have hnat : (471348151 : ℕ)^2199*100000000000000^1687 ≤ 11362873660927^1687*2500000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471348151 2500000000 11362873660927 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703669197/5000000000 : ℝ)^2199 ≤ (44868832386287/100000000000000 : ℝ)^1687 := by
    have hnat : (2703669197 : ℕ)^2199*100000000000000^1687 ≤ 44868832386287^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703669197 5000000000 44868832386287 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061059003/2000000000 : ℝ), (-471348151/2500000000 : ℝ), (2703669197/5000000000 : ℝ)] ![(43768293939599/100000000000000 : ℝ), (11362873660927/100000000000000 : ℝ), (44868832386287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061059003/2000000000 : ℝ)|^2199 ≤ (43768293939599/100000000000000 : ℝ)^1687
        have hw : |(1061059003/2000000000 : ℝ)|=(1061059003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471348151/2500000000 : ℝ)|^2199 ≤ (11362873660927/100000000000000 : ℝ)^1687
        have hw : |(-471348151/2500000000 : ℝ)|=(471348151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703669197/5000000000 : ℝ)|^2199 ≤ (44868832386287/100000000000000 : ℝ)^1687
        have hw : |(2703669197/5000000000 : ℝ)|=(2703669197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_6 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652647809/5000000000 : ℝ)*x 0 + (2703668939/5000000000 : ℝ)*x 1 + (-235674061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652647809/5000000000 : ℝ)^2199 ≤ (21884150212057/50000000000000 : ℝ)^1687 := by
    have hnat : (2652647809 : ℕ)^2199*50000000000000^1687 ≤ 21884150212057^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652647809 5000000000 21884150212057 50000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703668939/5000000000 : ℝ)^2199 ≤ (44868826805171/100000000000000 : ℝ)^1687 := by
    have hnat : (2703668939 : ℕ)^2199*100000000000000^1687 ≤ 44868826805171^1687*5000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703668939 5000000000 44868826805171 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235674061/1250000000 : ℝ)^2199 ≤ (11362872749641/100000000000000 : ℝ)^1687 := by
    have hnat : (235674061 : ℕ)^2199*100000000000000^1687 ≤ 11362872749641^1687*1250000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235674061 1250000000 11362872749641 100000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652647809/5000000000 : ℝ), (2703668939/5000000000 : ℝ), (-235674061/1250000000 : ℝ)] ![(21884150212057/50000000000000 : ℝ), (44868826805171/100000000000000 : ℝ), (11362872749641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652647809/5000000000 : ℝ)|^2199 ≤ (21884150212057/50000000000000 : ℝ)^1687
        have hw : |(2652647809/5000000000 : ℝ)|=(2652647809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703668939/5000000000 : ℝ)|^2199 ≤ (44868826805171/100000000000000 : ℝ)^1687
        have hw : |(2703668939/5000000000 : ℝ)|=(2703668939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235674061/1250000000 : ℝ)|^2199 ≤ (11362872749641/100000000000000 : ℝ)^1687
        have hw : |(-235674061/1250000000 : ℝ)|=(235674061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1438_s5_7 (p : ℝ) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ)) (x : Fin 3 → ℝ) :
    (860428259/2000000000 : ℝ)*x 0 + (4478725611/10000000000 : ℝ)*x 1 + (4131869803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860428259/2000000000 : ℝ)^2199 ≤ (2081560133313/6250000000000 : ℝ)^1687 := by
    have hnat : (860428259 : ℕ)^2199*6250000000000^1687 ≤ 2081560133313^1687*2000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860428259 2000000000 2081560133313 6250000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478725611/10000000000 : ℝ)^2199 ≤ (4387233782023/12500000000000 : ℝ)^1687 := by
    have hnat : (4478725611 : ℕ)^2199*12500000000000^1687 ≤ 4387233782023^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478725611 10000000000 4387233782023 12500000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131869803/10000000000 : ℝ)^2199 ≤ (7899291900911/25000000000000 : ℝ)^1687 := by
    have hnat : (4131869803 : ℕ)^2199*25000000000000^1687 ≤ 7899291900911^1687*10000000000^2199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131869803 10000000000 7899291900911 25000000000000 2199 1687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2199/512 : ℝ)) 2199 1687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860428259/2000000000 : ℝ), (4478725611/10000000000 : ℝ), (4131869803/10000000000 : ℝ)] ![(2081560133313/6250000000000 : ℝ), (4387233782023/12500000000000 : ℝ), (7899291900911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860428259/2000000000 : ℝ)|^2199 ≤ (2081560133313/6250000000000 : ℝ)^1687
        have hw : |(860428259/2000000000 : ℝ)|=(860428259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478725611/10000000000 : ℝ)|^2199 ≤ (4387233782023/12500000000000 : ℝ)^1687
        have hw : |(4478725611/10000000000 : ℝ)|=(4478725611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131869803/10000000000 : ℝ)|^2199 ≤ (7899291900911/25000000000000 : ℝ)^1687
        have hw : |(4131869803/10000000000 : ℝ)|=(4131869803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1438_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11333/100000 : ℝ) ^ (4397/1024 : ℝ) ≤ (543611562147103/6250000000000000000 : ℝ) := by
    have hpowers : (11333/100000 : ℝ)^4397 ≤ (543611562147103/6250000000000000000 : ℝ)^1024 := by
      have hnat : (11333 : ℕ)^4397*6250000000000000000^1024 ≤ 543611562147103^1024*100000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11333 100000 543611562147103 6250000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11333/100000 : ℝ)) (X := (543611562147103/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14789/100000 : ℝ) ^ (4397/1024 : ℝ) ≤ (13637433438618803/50000000000000000000 : ℝ) := by
    have hpowers : (14789/100000 : ℝ)^4397 ≤ (13637433438618803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14789 : ℕ)^4397*50000000000000000000^1024 ≤ 13637433438618803^1024*100000^4397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14789 100000 13637433438618803 50000000000000000000 4397 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14789/100000 : ℝ)) (X := (13637433438618803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125543611562147103/3125000000000000000 : ℝ) ≤ (1000040509154579/1000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (3125543611562147103/3125000000000000000 : ℝ)^1024 ≤ (1000040509154579/1000000000000000 : ℝ)^4397 := by
      have hnat : (3125543611562147103 : ℕ)^1024*1000000000000000^4397 ≤ 1000040509154579^4397*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125543611562147103 3125000000000000000 1000040509154579 1000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000040509154579/1000000000000000 : ℝ)) (X := (3125543611562147103/3125000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017986325935795627/50000000000000000000 : ℝ) ≤ (5000418818673233/5000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (50017986325935795627/50000000000000000000 : ℝ)^1024 ≤ (5000418818673233/5000000000000000 : ℝ)^4397 := by
      have hnat : (50017986325935795627 : ℕ)^1024*5000000000000000^4397 ≤ 5000418818673233^4397*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017986325935795627 50000000000000000000 5000418818673233 5000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000418818673233/5000000000000000 : ℝ)) (X := (50017986325935795627/50000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013637433438618803/25000000000000000000 : ℝ) ≤ (5000635091573571/5000000000000000 : ℝ) ^ (4397/1024 : ℝ) := by
    have hpowers : (25013637433438618803/25000000000000000000 : ℝ)^1024 ≤ (5000635091573571/5000000000000000 : ℝ)^4397 := by
      have hnat : (25013637433438618803 : ℕ)^1024*5000000000000000^4397 ≤ 5000635091573571^4397*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013637433438618803 25000000000000000000 5000635091573571 5000000000000000 1024 4397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000635091573571/5000000000000000 : ℝ)) (X := (25013637433438618803/25000000000000000000 : ℝ)) (by norm_num) 4397 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(543611562147103/6250000000000000000 : ℝ) ≤ ((4318949489158016003/4320000000000000000 : ℝ)+2*(108136450169/86400000000000 : ℝ)*(11333/100000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (4318949489158016003/4320000000000000000 : ℝ)+2*(108136450169/86400000000000 : ℝ)*(11333/100000 : ℝ)=(1000040509154579/1000000000000000 : ℝ) by norm_num, show 1+2*(543611562147103/6250000000000000000 : ℝ)=(3125543611562147103/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13637433438618803/50000000000000000000 : ℝ)+(543611562147103/6250000000000000000 : ℝ) ≤ ((4318949489158016003/4320000000000000000 : ℝ)+(108136450169/86400000000000 : ℝ)*((14789/100000 : ℝ)+(11333/100000 : ℝ)))^(4397/1024 : ℝ) := by
    rw [show (4318949489158016003/4320000000000000000 : ℝ)+(108136450169/86400000000000 : ℝ)*((14789/100000 : ℝ)+(11333/100000 : ℝ))=(5000418818673233/5000000000000000 : ℝ) by norm_num, show 1+(13637433438618803/50000000000000000000 : ℝ)+(543611562147103/6250000000000000000 : ℝ)=(50017986325935795627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13637433438618803/50000000000000000000 : ℝ) ≤ ((4318949489158016003/4320000000000000000 : ℝ)+2*(108136450169/86400000000000 : ℝ)*(14789/100000 : ℝ))^(4397/1024 : ℝ) := by
    rw [show (4318949489158016003/4320000000000000000 : ℝ)+2*(108136450169/86400000000000 : ℝ)*(14789/100000 : ℝ)=(5000635091573571/5000000000000000 : ℝ) by norm_num, show 1+2*(13637433438618803/50000000000000000000 : ℝ)=(25013637433438618803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4318949489158016003/4320000000000000000 : ℝ)*(X 1 0+X 2 0)+(108136450169/86400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (11333/100000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (4318949489158016003/4320000000000000000 : ℝ)) (alpha := (108136450169/86400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4318949489158016003/4320000000000000000 : ℝ)*(X 0 1+X 2 1)+(108136450169/86400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (11333/100000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (4318949489158016003/4320000000000000000 : ℝ)) (alpha := (108136450169/86400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4318949489158016003/4320000000000000000 : ℝ)*(X 0 2+X 1 2)+(108136450169/86400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4397/1024 : ℝ)) (lo := (11333/100000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (4318949489158016003/4320000000000000000 : ℝ)) (alpha := (108136450169/86400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1963830841/10000000000 : ℝ)*X 0 0+(2703962273/5000000000 : ℝ)*X 0 1+(2623474127/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347181021/10000000000 : ℝ)*X 1 0+(-2045782053/10000000000 : ℝ)*X 1 1+(5246948653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347180933/10000000000 : ℝ)*X 2 0+(2623474559/5000000000 : ℝ)*X 2 1+(-127861347/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302115799/10000000000 : ℝ)*X 0 0+(2065300303/5000000000 : ℝ)*X 0 1+(559998651/1250000000 : ℝ)*X 0 2+(4302115799/10000000000 : ℝ)*X 1 0+(2065300303/5000000000 : ℝ)*X 1 1+(559998651/1250000000 : ℝ)*X 1 2+(4302115799/10000000000 : ℝ)*X 2 0+(2065300303/5000000000 : ℝ)*X 2 1+(559998651/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-392768369/2000000000 : ℝ)*X 0 0+(5247531507/10000000000 : ℝ)*X 0 1+(5407338507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061059003/2000000000 : ℝ)*X 1 0+(-471348151/2500000000 : ℝ)*X 1 1+(2703669197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652647809/5000000000 : ℝ)*X 2 0+(2703668939/5000000000 : ℝ)*X 2 1+(-235674061/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860428259/2000000000 : ℝ)*X 0 0+(4478725611/10000000000 : ℝ)*X 0 1+(4131869803/10000000000 : ℝ)*X 0 2+(860428259/2000000000 : ℝ)*X 1 0+(4478725611/10000000000 : ℝ)*X 1 1+(4131869803/10000000000 : ℝ)*X 1 2+(860428259/2000000000 : ℝ)*X 2 0+(4478725611/10000000000 : ℝ)*X 2 1+(4131869803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1438_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93508370767817533301708009/24000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2335564829/100000000000000 : ℝ)*(base19) + (419159139/25000000000000 : ℝ)*(base23) + (157687499/50000000000000 : ℝ)*(upper4) + (37073819/50000000000000 : ℝ)*(upper5) + (4537217649220003/100000000000000 : ℝ)*(major0) + (4537217649220003/100000000000000 : ℝ)*(major1) + (4537217649220003/100000000000000 : ℝ)*(major2) + (6212172803740413/100000000000000 : ℝ)*(sp0) + (3106127567551197/50000000000000 : ℝ)*(sp1) + (1553065005066437/25000000000000 : ℝ)*(sp2) + (71553937041727/2500000000000 : ℝ)*(sp3) + (88893161891/100000000000000 : ℝ)*(sp4) + (4226235081/100000000000000 : ℝ)*(sp5) + (15989995877/100000000000000 : ℝ)*(sp7) + (1431086735832479/50000000000000 : ℝ)*(f.failure) + (194133178028197/3125000000000 : ℝ)*(f.sum) + (23216288492267/4320000000000000000000000000 : ℝ)*base65 + (746201212772313997/144000000000000000000000000000000 : ℝ)*base68 + (915209829284313997/144000000000000000000000000000000 : ℝ)*base70 + (893408893700313997/144000000000000000000000000000000 : ℝ)*base72 + (614639839787/4320000000000000000000000000 : ℝ)*base73 + (616776965492313997/144000000000000000000000000000000 : ℝ)*base76 + (1147237318580313997/144000000000000000000000000000000 : ℝ)*base78 + (1991100368948313997/144000000000000000000000000000000 : ℝ)*base80 + (1894580438507/4320000000000000000000000000 : ℝ)*base81 + (42253937/5000000000000000000000 : ℝ)*base89 + (42253937/5000000000000000000000 : ℝ)*base91 + (42253937/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25560196676751754928507449/9000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10893027/800000000000 : ℝ)*(base19) + (75539337/3125000000000 : ℝ)*(base23) + (140073571/100000000000000 : ℝ)*(lower4) + (21382881/20000000000000 : ℝ)*(upper5) + (1142574966251483/25000000000000 : ℝ)*(major0) + (1142574966251483/25000000000000 : ℝ)*(major1) + (1142574966251483/25000000000000 : ℝ)*(major2) + (28088343/2500000000000 : ℝ)*(sp0) + (35704267671/100000000000000 : ℝ)*(sp1) + (9176956989/20000000000000 : ℝ)*(sp2) + (156438901856123/2500000000000 : ℝ)*(sp4) + (6257520131882593/100000000000000 : ℝ)*(sp5) + (6257508895734911/100000000000000 : ℝ)*(sp6) + (22523769043483/781250000000 : ℝ)*(sp7) + (22523769043483/781250000000 : ℝ)*(f.failure) + (78219464972233/1250000000000 : ℝ)*(f.sum) + (2232571602173/1080000000000000000000000000 : ℝ)*base66 + (252011245274722517/36000000000000000000000000000000 : ℝ)*base68 + (135766092122722517/36000000000000000000000000000000 : ℝ)*base70 + (142781630786722517/36000000000000000000000000000000 : ℝ)*base72 + (4794009296693/1080000000000000000000000000 : ℝ)*base74 + (279939377582722517/36000000000000000000000000000000 : ℝ)*base76 + (237970227878722517/36000000000000000000000000000000 : ℝ)*base78 + (32269889637277483/36000000000000000000000000000000 : ℝ)*base79 + (1216556029507/1080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (105949/78125000000000000000 : ℝ)*base89 + (105949/78125000000000000000 : ℝ)*base91 + (105949/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1438_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1438_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1438_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3943/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1438_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1438_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1438_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4397/1024 : ℝ) ≤ p) (hpb : p ≤ (2199/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158523503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3943/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1438_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
