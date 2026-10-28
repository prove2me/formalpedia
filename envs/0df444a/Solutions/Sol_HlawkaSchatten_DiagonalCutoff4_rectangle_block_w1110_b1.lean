-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:55.365832+00:00
-- url     : https://prove2.me/submissions/cfc03bb8-1b3e-40f5-97e8-4a7c263f78f5

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
theorem support_rectangle_w1110_s3_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435622247/2000000000 : ℝ)*x 0 + (1358142631/2500000000 : ℝ)*x 1 + (2614487473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435622247/2000000000 : ℝ)^8303 ≤ (13223776708427/100000000000000 : ℝ)^6255 := by
    have hnat : (435622247 : ℕ)^8303*100000000000000^6255 ≤ 13223776708427^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435622247 2000000000 13223776708427 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358142631/2500000000 : ℝ)^8303 ≤ (44487842519009/100000000000000 : ℝ)^6255 := by
    have hnat : (1358142631 : ℕ)^8303*100000000000000^6255 ≤ 44487842519009^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358142631 2500000000 44487842519009 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614487473/5000000000 : ℝ)^8303 ≤ (42288380752263/100000000000000 : ℝ)^6255 := by
    have hnat : (2614487473 : ℕ)^8303*100000000000000^6255 ≤ 42288380752263^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614487473 5000000000 42288380752263 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435622247/2000000000 : ℝ), (1358142631/2500000000 : ℝ), (2614487473/5000000000 : ℝ)] ![(13223776708427/100000000000000 : ℝ), (44487842519009/100000000000000 : ℝ), (42288380752263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435622247/2000000000 : ℝ)|^8303 ≤ (13223776708427/100000000000000 : ℝ)^6255
        have hw : |(-435622247/2000000000 : ℝ)|=(435622247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358142631/2500000000 : ℝ)|^8303 ≤ (44487842519009/100000000000000 : ℝ)^6255
        have hw : |(1358142631/2500000000 : ℝ)|=(1358142631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614487473/5000000000 : ℝ)|^8303 ≤ (42288380752263/100000000000000 : ℝ)^6255
        have hw : |(2614487473/5000000000 : ℝ)|=(2614487473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214183073/400000000 : ℝ)*x 0 + (-1141128741/5000000000 : ℝ)*x 1 + (1307243751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214183073/400000000 : ℝ)^8303 ≤ (21821011241337/50000000000000 : ℝ)^6255 := by
    have hnat : (214183073 : ℕ)^8303*50000000000000^6255 ≤ 21821011241337^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214183073 400000000 21821011241337 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141128741/5000000000 : ℝ)^8303 ≤ (14069596125971/100000000000000 : ℝ)^6255 := by
    have hnat : (1141128741 : ℕ)^8303*100000000000000^6255 ≤ 14069596125971^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141128741 5000000000 14069596125971 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307243751/2500000000 : ℝ)^8303 ≤ (10572095343727/25000000000000 : ℝ)^6255 := by
    have hnat : (1307243751 : ℕ)^8303*25000000000000^6255 ≤ 10572095343727^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307243751 2500000000 10572095343727 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214183073/400000000 : ℝ), (-1141128741/5000000000 : ℝ), (1307243751/2500000000 : ℝ)] ![(21821011241337/50000000000000 : ℝ), (14069596125971/100000000000000 : ℝ), (10572095343727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214183073/400000000 : ℝ)|^8303 ≤ (21821011241337/50000000000000 : ℝ)^6255
        have hw : |(214183073/400000000 : ℝ)|=(214183073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141128741/5000000000 : ℝ)|^8303 ≤ (14069596125971/100000000000000 : ℝ)^6255
        have hw : |(-1141128741/5000000000 : ℝ)|=(1141128741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307243751/2500000000 : ℝ)|^8303 ≤ (10572095343727/25000000000000 : ℝ)^6255
        have hw : |(1307243751/2500000000 : ℝ)|=(1307243751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669322119/1250000000 : ℝ)*x 0 + (5228975103/10000000000 : ℝ)*x 1 + (-2282257183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669322119/1250000000 : ℝ)^8303 ≤ (2727626491043/6250000000000 : ℝ)^6255 := by
    have hnat : (669322119 : ℕ)^8303*6250000000000^6255 ≤ 2727626491043^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669322119 1250000000 2727626491043 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228975103/10000000000 : ℝ)^8303 ≤ (42288382437697/100000000000000 : ℝ)^6255 := by
    have hnat : (5228975103 : ℕ)^8303*100000000000000^6255 ≤ 42288382437697^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228975103 10000000000 42288382437697 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282257183/10000000000 : ℝ)^8303 ≤ (2813918735837/20000000000000 : ℝ)^6255 := by
    have hnat : (2282257183 : ℕ)^8303*20000000000000^6255 ≤ 2813918735837^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282257183 10000000000 2813918735837 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669322119/1250000000 : ℝ), (5228975103/10000000000 : ℝ), (-2282257183/10000000000 : ℝ)] ![(2727626491043/6250000000000 : ℝ), (42288382437697/100000000000000 : ℝ), (2813918735837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669322119/1250000000 : ℝ)|^8303 ≤ (2727626491043/6250000000000 : ℝ)^6255
        have hw : |(669322119/1250000000 : ℝ)|=(669322119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228975103/10000000000 : ℝ)|^8303 ≤ (42288382437697/100000000000000 : ℝ)^6255
        have hw : |(5228975103/10000000000 : ℝ)|=(5228975103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282257183/10000000000 : ℝ)|^8303 ≤ (2813918735837/20000000000000 : ℝ)^6255
        have hw : |(-2282257183/10000000000 : ℝ)|=(2282257183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091682109/2500000000 : ℝ)*x 0 + (4170117921/10000000000 : ℝ)*x 1 + (4572624441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091682109/2500000000 : ℝ)^8303 ≤ (33291764835311/100000000000000 : ℝ)^6255 := by
    have hnat : (1091682109 : ℕ)^8303*100000000000000^6255 ≤ 33291764835311^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091682109 2500000000 33291764835311 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170117921/10000000000 : ℝ)^8303 ≤ (31316847604471/100000000000000 : ℝ)^6255 := by
    have hnat : (4170117921 : ℕ)^8303*100000000000000^6255 ≤ 31316847604471^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170117921 10000000000 31316847604471 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4572624441/10000000000 : ℝ)^8303 ≤ (17695693767339/50000000000000 : ℝ)^6255 := by
    have hnat : (4572624441 : ℕ)^8303*50000000000000^6255 ≤ 17695693767339^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572624441 10000000000 17695693767339 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091682109/2500000000 : ℝ), (4170117921/10000000000 : ℝ), (4572624441/10000000000 : ℝ)] ![(33291764835311/100000000000000 : ℝ), (31316847604471/100000000000000 : ℝ), (17695693767339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091682109/2500000000 : ℝ)|^8303 ≤ (33291764835311/100000000000000 : ℝ)^6255
        have hw : |(1091682109/2500000000 : ℝ)|=(1091682109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170117921/10000000000 : ℝ)|^8303 ≤ (31316847604471/100000000000000 : ℝ)^6255
        have hw : |(4170117921/10000000000 : ℝ)|=(4170117921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4572624441/10000000000 : ℝ)|^8303 ≤ (17695693767339/50000000000000 : ℝ)^6255
        have hw : |(4572624441/10000000000 : ℝ)|=(4572624441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-136133181/625000000 : ℝ)*x 0 + (81715363/156250000 : ℝ)*x 1 + (1357939417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136133181/625000000 : ℝ)^8303 ≤ (13223935157397/100000000000000 : ℝ)^6255 := by
    have hnat : (136133181 : ℕ)^8303*100000000000000^6255 ≤ 13223935157397^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136133181 625000000 13223935157397 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81715363/156250000 : ℝ)^8303 ≤ (21148529062623/50000000000000 : ℝ)^6255 := by
    have hnat : (81715363 : ℕ)^8303*50000000000000^6255 ≤ 21148529062623^6255*156250000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81715363 156250000 21148529062623 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357939417/2500000000 : ℝ)^8303 ≤ (44479006702817/100000000000000 : ℝ)^6255 := by
    have hnat : (1357939417 : ℕ)^8303*100000000000000^6255 ≤ 44479006702817^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357939417 2500000000 44479006702817 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136133181/625000000 : ℝ), (81715363/156250000 : ℝ), (1357939417/2500000000 : ℝ)] ![(13223935157397/100000000000000 : ℝ), (21148529062623/50000000000000 : ℝ), (44479006702817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136133181/625000000 : ℝ)|^8303 ≤ (13223935157397/100000000000000 : ℝ)^6255
        have hw : |(-136133181/625000000 : ℝ)|=(136133181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81715363/156250000 : ℝ)|^8303 ≤ (21148529062623/50000000000000 : ℝ)^6255
        have hw : |(81715363/156250000 : ℝ)|=(81715363/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357939417/2500000000 : ℝ)|^8303 ≤ (44479006702817/100000000000000 : ℝ)^6255
        have hw : |(1357939417/2500000000 : ℝ)|=(1357939417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530311887/1000000000 : ℝ)*x 0 + (-415894933/2000000000 : ℝ)*x 1 + (5431757849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530311887/1000000000 : ℝ)^8303 ≤ (1346443007047/3125000000000 : ℝ)^6255 := by
    have hnat : (530311887 : ℕ)^8303*3125000000000^6255 ≤ 1346443007047^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530311887 1000000000 1346443007047 3125000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415894933/2000000000 : ℝ)^8303 ≤ (12434815093091/100000000000000 : ℝ)^6255 := by
    have hnat : (415894933 : ℕ)^8303*100000000000000^6255 ≤ 12434815093091^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415894933 2000000000 12434815093091 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431757849/10000000000 : ℝ)^8303 ≤ (22239504335127/50000000000000 : ℝ)^6255 := by
    have hnat : (5431757849 : ℕ)^8303*50000000000000^6255 ≤ 22239504335127^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431757849 10000000000 22239504335127 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530311887/1000000000 : ℝ), (-415894933/2000000000 : ℝ), (5431757849/10000000000 : ℝ)] ![(1346443007047/3125000000000 : ℝ), (12434815093091/100000000000000 : ℝ), (22239504335127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530311887/1000000000 : ℝ)|^8303 ≤ (1346443007047/3125000000000 : ℝ)^6255
        have hw : |(530311887/1000000000 : ℝ)|=(530311887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415894933/2000000000 : ℝ)|^8303 ≤ (12434815093091/100000000000000 : ℝ)^6255
        have hw : |(-415894933/2000000000 : ℝ)|=(415894933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431757849/10000000000 : ℝ)|^8303 ≤ (22239504335127/50000000000000 : ℝ)^6255
        have hw : |(5431757849/10000000000 : ℝ)|=(5431757849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060623783/2000000000 : ℝ)*x 0 + (2715878841/5000000000 : ℝ)*x 1 + (-129967177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060623783/2000000000 : ℝ)^8303 ≤ (43086176710823/100000000000000 : ℝ)^6255 := by
    have hnat : (1060623783 : ℕ)^8303*100000000000000^6255 ≤ 43086176710823^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060623783 2000000000 43086176710823 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715878841/5000000000 : ℝ)^8303 ≤ (22239503427497/50000000000000 : ℝ)^6255 := by
    have hnat : (2715878841 : ℕ)^8303*50000000000000^6255 ≤ 22239503427497^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715878841 5000000000 22239503427497 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129967177/625000000 : ℝ)^8303 ≤ (12434816418683/100000000000000 : ℝ)^6255 := by
    have hnat : (129967177 : ℕ)^8303*100000000000000^6255 ≤ 12434816418683^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129967177 625000000 12434816418683 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060623783/2000000000 : ℝ), (2715878841/5000000000 : ℝ), (-129967177/625000000 : ℝ)] ![(43086176710823/100000000000000 : ℝ), (22239503427497/50000000000000 : ℝ), (12434816418683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060623783/2000000000 : ℝ)|^8303 ≤ (43086176710823/100000000000000 : ℝ)^6255
        have hw : |(1060623783/2000000000 : ℝ)|=(1060623783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715878841/5000000000 : ℝ)|^8303 ≤ (22239503427497/50000000000000 : ℝ)^6255
        have hw : |(2715878841/5000000000 : ℝ)|=(2715878841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129967177/625000000 : ℝ)|^8303 ≤ (12434816418683/100000000000000 : ℝ)^6255
        have hw : |(-129967177/625000000 : ℝ)|=(129967177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s3_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091691821/2500000000 : ℝ)*x 0 + (142844601/312500000 : ℝ)*x 1 + (2085862209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091691821/2500000000 : ℝ)^8303 ≤ (16646078992373/50000000000000 : ℝ)^6255 := by
    have hnat : (1091691821 : ℕ)^8303*50000000000000^6255 ≤ 16646078992373^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091691821 2500000000 16646078992373 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142844601/312500000 : ℝ)^8303 ≤ (35374978739579/100000000000000 : ℝ)^6255 := by
    have hnat : (142844601 : ℕ)^8303*100000000000000^6255 ≤ 35374978739579^6255*312500000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142844601 312500000 35374978739579 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085862209/5000000000 : ℝ)^8303 ≤ (31332863260481/100000000000000 : ℝ)^6255 := by
    have hnat : (2085862209 : ℕ)^8303*100000000000000^6255 ≤ 31332863260481^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085862209 5000000000 31332863260481 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091691821/2500000000 : ℝ), (142844601/312500000 : ℝ), (2085862209/5000000000 : ℝ)] ![(16646078992373/50000000000000 : ℝ), (35374978739579/100000000000000 : ℝ), (31332863260481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091691821/2500000000 : ℝ)|^8303 ≤ (16646078992373/50000000000000 : ℝ)^6255
        have hw : |(1091691821/2500000000 : ℝ)|=(1091691821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142844601/312500000 : ℝ)|^8303 ≤ (35374978739579/100000000000000 : ℝ)^6255
        have hw : |(142844601/312500000 : ℝ)|=(142844601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085862209/5000000000 : ℝ)|^8303 ≤ (31332863260481/100000000000000 : ℝ)^6255
        have hw : |(2085862209/5000000000 : ℝ)|=(2085862209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (83/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5269/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2969/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (83/500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (83/500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (83/500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (83/500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (83/500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (83/500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8923/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (2783841677363663/50000000000000000000 : ℝ) := by
    have hpowers : (8923/100000 : ℝ)^4151 ≤ (2783841677363663/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8923 : ℕ)^4151*50000000000000000000^1024 ≤ 2783841677363663^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8923 100000 2783841677363663 50000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8923/100000 : ℝ)) (X := (2783841677363663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (83/500 : ℝ) ^ (4151/1024 : ℝ) ≤ (68951485390337233/100000000000000000000 : ℝ) := by
    have hpowers : (83/500 : ℝ)^4151 ≤ (68951485390337233/100000000000000000000 : ℝ)^1024 := by
      have hnat : (83 : ℕ)^4151*100000000000000000000^1024 ≤ 68951485390337233^1024*500^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83 500 68951485390337233 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83/500 : ℝ)) (X := (68951485390337233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002783841677363663/25000000000000000000 : ℝ) ≤ (19531786492397/19531250000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (25002783841677363663/25000000000000000000 : ℝ)^1024 ≤ (19531786492397/19531250000000 : ℝ)^4151 := by
      have hnat : (25002783841677363663 : ℕ)^1024*19531250000000^4151 ≤ 19531786492397^4151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002783841677363663 25000000000000000000 19531786492397 19531250000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19531786492397/19531250000000 : ℝ)) (X := (25002783841677363663/25000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074519168745064559/100000000000000000000 : ℝ) ≤ (10001837779330517/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (100074519168745064559/100000000000000000000 : ℝ)^1024 ≤ (10001837779330517/10000000000000000 : ℝ)^4151 := by
      have hnat : (100074519168745064559 : ℕ)^1024*10000000000000000^4151 ≤ 10001837779330517^4151*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074519168745064559 100000000000000000000 10001837779330517 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001837779330517/10000000000000000 : ℝ)) (X := (100074519168745064559/100000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50068951485390337233/50000000000000000000 : ℝ) ≤ (1000340087455377/1000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50068951485390337233/50000000000000000000 : ℝ)^1024 ≤ (1000340087455377/1000000000000000 : ℝ)^4151 := by
      have hnat : (50068951485390337233 : ℕ)^1024*1000000000000000^4151 ≤ 1000340087455377^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50068951485390337233 50000000000000000000 1000340087455377 1000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000340087455377/1000000000000000 : ℝ)) (X := (50068951485390337233/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2783841677363663/50000000000000000000 : ℝ) ≤ ((7674421375253729269/7677000000000000000 : ℝ)+2*(1563095223253/767700000000000 : ℝ)*(8923/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (7674421375253729269/7677000000000000000 : ℝ)+2*(1563095223253/767700000000000 : ℝ)*(8923/100000 : ℝ)=(19531786492397/19531250000000 : ℝ) by norm_num, show 1+2*(2783841677363663/50000000000000000000 : ℝ)=(25002783841677363663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(68951485390337233/100000000000000000000 : ℝ)+(2783841677363663/50000000000000000000 : ℝ) ≤ ((7674421375253729269/7677000000000000000 : ℝ)+(1563095223253/767700000000000 : ℝ)*((83/500 : ℝ)+(8923/100000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (7674421375253729269/7677000000000000000 : ℝ)+(1563095223253/767700000000000 : ℝ)*((83/500 : ℝ)+(8923/100000 : ℝ))=(10001837779330517/10000000000000000 : ℝ) by norm_num, show 1+(68951485390337233/100000000000000000000 : ℝ)+(2783841677363663/50000000000000000000 : ℝ)=(100074519168745064559/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(68951485390337233/100000000000000000000 : ℝ) ≤ ((7674421375253729269/7677000000000000000 : ℝ)+2*(1563095223253/767700000000000 : ℝ)*(83/500 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (7674421375253729269/7677000000000000000 : ℝ)+2*(1563095223253/767700000000000 : ℝ)*(83/500 : ℝ)=(1000340087455377/1000000000000000 : ℝ) by norm_num, show 1+2*(68951485390337233/100000000000000000000 : ℝ)=(50068951485390337233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7674421375253729269/7677000000000000000 : ℝ)*(X 1 0+X 2 0)+(1563095223253/767700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (8923/100000 : ℝ)) (hi := (83/500 : ℝ)) (c := (7674421375253729269/7677000000000000000 : ℝ)) (alpha := (1563095223253/767700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7674421375253729269/7677000000000000000 : ℝ)*(X 0 1+X 2 1)+(1563095223253/767700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (8923/100000 : ℝ)) (hi := (83/500 : ℝ)) (c := (7674421375253729269/7677000000000000000 : ℝ)) (alpha := (1563095223253/767700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7674421375253729269/7677000000000000000 : ℝ)*(X 0 2+X 1 2)+(1563095223253/767700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (8923/100000 : ℝ)) (hi := (83/500 : ℝ)) (c := (7674421375253729269/7677000000000000000 : ℝ)) (alpha := (1563095223253/767700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-435622247/2000000000 : ℝ)*X 0 0+(1358142631/2500000000 : ℝ)*X 0 1+(2614487473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214183073/400000000 : ℝ)*X 1 0+(-1141128741/5000000000 : ℝ)*X 1 1+(1307243751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669322119/1250000000 : ℝ)*X 2 0+(5228975103/10000000000 : ℝ)*X 2 1+(-2282257183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091682109/2500000000 : ℝ)*X 0 0+(4170117921/10000000000 : ℝ)*X 0 1+(4572624441/10000000000 : ℝ)*X 0 2+(1091682109/2500000000 : ℝ)*X 1 0+(4170117921/10000000000 : ℝ)*X 1 1+(4572624441/10000000000 : ℝ)*X 1 2+(1091682109/2500000000 : ℝ)*X 2 0+(4170117921/10000000000 : ℝ)*X 2 1+(4572624441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-136133181/625000000 : ℝ)*X 0 0+(81715363/156250000 : ℝ)*X 0 1+(1357939417/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530311887/1000000000 : ℝ)*X 1 0+(-415894933/2000000000 : ℝ)*X 1 1+(5431757849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060623783/2000000000 : ℝ)*X 2 0+(2715878841/5000000000 : ℝ)*X 2 1+(-129967177/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091691821/2500000000 : ℝ)*X 0 0+(142844601/312500000 : ℝ)*X 0 1+(2085862209/5000000000 : ℝ)*X 0 2+(1091691821/2500000000 : ℝ)*X 1 0+(142844601/312500000 : ℝ)*X 1 1+(2085862209/5000000000 : ℝ)*X 1 2+(1091691821/2500000000 : ℝ)*X 2 0+(142844601/312500000 : ℝ)*X 2 1+(2085862209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93279899057657619249165731/63975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381538807/50000000000000 : ℝ)*(base19) + (74483651/10000000000000 : ℝ)*(base23) + (5228979/6250000000000 : ℝ)*(lower2) + (29770023/25000000000000 : ℝ)*(upper5) + (1849045058058081/50000000000000 : ℝ)*(major0) + (1849045058058081/50000000000000 : ℝ)*(major1) + (924522529029041/25000000000000 : ℝ)*(major2) + (1227928335111973/25000000000000 : ℝ)*(sp0) + (4911731935741841/100000000000000 : ℝ)*(sp1) + (2455867096089759/50000000000000 : ℝ)*(sp2) + (248443877044339/10000000000000 : ℝ)*(sp3) + (2699571017/12500000000000 : ℝ)*(sp4) + (1119098287/50000000000000 : ℝ)*(sp5) + (6476170631/100000000000000 : ℝ)*(sp7) + (1242222623307011/50000000000000 : ℝ)*(f.failure) + (1227933734254007/25000000000000 : ℝ)*(f.sum) + (71315825613559/38385000000000000000000000000 : ℝ)*base65 + (2015274260887567211/383850000000000000000000000000000 : ℝ)*base68 + (2781492813721266029/191925000000000000000000000000000 : ℝ)*base69 + (331348990910482789/383850000000000000000000000000000 : ℝ)*base71 + (4050655343111/38385000000000000000000000000 : ℝ)*base74 + (3102704057627016029/191925000000000000000000000000000 : ℝ)*base75 + (966864314795465737/127950000000000000000000000000000 : ℝ)*base78 + (100311751335665737/127950000000000000000000000000000 : ℝ)*base80 + (4482872199077/799687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (64378063/5000000000000000000000 : ℝ)*base89 + (64378063/5000000000000000000000 : ℝ)*base91 + (35621937/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (624695118962922813858401/341200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301944973/100000000000000 : ℝ)*(base19) + (249895997/50000000000000 : ℝ)*(base23) + (7463187/12500000000000 : ℝ)*(upper3) + (20384963/25000000000000 : ℝ)*(lower4) + (29821939038553/800000000000 : ℝ)*(major0) + (29821939038553/800000000000 : ℝ)*(major1) + (1863871189909563/50000000000000 : ℝ)*(major2) + (2069276649/25000000000000 : ℝ)*(sp1) + (169820089/2000000000000 : ℝ)*(sp2) + (203739001/50000000000000 : ℝ)*(sp3) + (2475559256769463/50000000000000 : ℝ)*(sp4) + (4951109934487357/100000000000000 : ℝ)*(sp5) + (2475554761371241/50000000000000 : ℝ)*(sp6) + (500873155518419/20000000000000 : ℝ)*(sp7) + (2504366185070097/100000000000000 : ℝ)*(f.failure) + (2475559256769463/50000000000000 : ℝ)*(f.sum) + (62488446684383/76770000000000000000000000000 : ℝ)*base65 + (37730695768555597/6141600000000000000000000000000 : ℝ)*base67 + (3452089895798224447/383850000000000000000000000000000 : ℝ)*base69 + (2110917831950797/6141600000000000000000000000000 : ℝ)*base71 + (199137268397347/76770000000000000000000000000 : ℝ)*base74 + (4219749973721425553/383850000000000000000000000000000 : ℝ)*base76 + (13910550616133443/6141600000000000000000000000000 : ℝ)*base78 + (45900700438828157/6141600000000000000000000000000 : ℝ)*base79 + (2620998515861/7677000000000000000000000000 : ℝ)*base82 + (24734101/10000000000000000000000 : ℝ)*base89 + (24734101/10000000000000000000000 : ℝ)*base91 + (75265899/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1110_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (83/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5269/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2969/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_s4_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181384279/10000000000 : ℝ)*x 0 + (5403468253/10000000000 : ℝ)*x 1 + (5255937157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181384279/10000000000 : ℝ)^8303 ≤ (2650032155913/20000000000000 : ℝ)^6255 := by
    have hnat : (2181384279 : ℕ)^8303*20000000000000^6255 ≤ 2650032155913^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181384279 10000000000 2650032155913 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403468253/10000000000 : ℝ)^8303 ≤ (883435365923/2000000000000 : ℝ)^6255 := by
    have hnat : (5403468253 : ℕ)^8303*2000000000000^6255 ≤ 883435365923^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403468253 10000000000 883435365923 2000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255937157/10000000000 : ℝ)^8303 ≤ (42578070915031/100000000000000 : ℝ)^6255 := by
    have hnat : (5255937157 : ℕ)^8303*100000000000000^6255 ≤ 42578070915031^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255937157 10000000000 42578070915031 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181384279/10000000000 : ℝ), (5403468253/10000000000 : ℝ), (5255937157/10000000000 : ℝ)] ![(2650032155913/20000000000000 : ℝ), (883435365923/2000000000000 : ℝ), (42578070915031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181384279/10000000000 : ℝ)|^8303 ≤ (2650032155913/20000000000000 : ℝ)^6255
        have hw : |(-2181384279/10000000000 : ℝ)|=(2181384279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403468253/10000000000 : ℝ)|^8303 ≤ (883435365923/2000000000000 : ℝ)^6255
        have hw : |(5403468253/10000000000 : ℝ)|=(5403468253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255937157/10000000000 : ℝ)|^8303 ≤ (42578070915031/100000000000000 : ℝ)^6255
        have hw : |(5255937157/10000000000 : ℝ)|=(5255937157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673666841/5000000000 : ℝ)*x 0 + (-2256382319/10000000000 : ℝ)*x 1 + (164248051/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673666841/5000000000 : ℝ)^8303 ≤ (43563676220059/100000000000000 : ℝ)^6255 := by
    have hnat : (2673666841 : ℕ)^8303*100000000000000^6255 ≤ 43563676220059^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673666841 5000000000 43563676220059 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256382319/10000000000 : ℝ)^8303 ≤ (13858247745971/100000000000000 : ℝ)^6255 := by
    have hnat : (2256382319 : ℕ)^8303*100000000000000^6255 ≤ 13858247745971^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256382319 10000000000 13858247745971 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164248051/312500000 : ℝ)^8303 ≤ (42578076022869/100000000000000 : ℝ)^6255 := by
    have hnat : (164248051 : ℕ)^8303*100000000000000^6255 ≤ 42578076022869^6255*312500000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164248051 312500000 42578076022869 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673666841/5000000000 : ℝ), (-2256382319/10000000000 : ℝ), (164248051/312500000 : ℝ)] ![(43563676220059/100000000000000 : ℝ), (13858247745971/100000000000000 : ℝ), (42578076022869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673666841/5000000000 : ℝ)|^8303 ≤ (43563676220059/100000000000000 : ℝ)^6255
        have hw : |(2673666841/5000000000 : ℝ)|=(2673666841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2256382319/10000000000 : ℝ)|^8303 ≤ (13858247745971/100000000000000 : ℝ)^6255
        have hw : |(-2256382319/10000000000 : ℝ)|=(2256382319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164248051/312500000 : ℝ)|^8303 ≤ (42578076022869/100000000000000 : ℝ)^6255
        have hw : |(164248051/312500000 : ℝ)|=(164248051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336833317/2500000000 : ℝ)*x 0 + (5255937401/10000000000 : ℝ)*x 1 + (-564095793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336833317/2500000000 : ℝ)^8303 ≤ (1742546869719/4000000000000 : ℝ)^6255 := by
    have hnat : (1336833317 : ℕ)^8303*4000000000000^6255 ≤ 1742546869719^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336833317 2500000000 1742546869719 4000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255937401/10000000000 : ℝ)^8303 ≤ (42578073538847/100000000000000 : ℝ)^6255 := by
    have hnat : (5255937401 : ℕ)^8303*100000000000000^6255 ≤ 42578073538847^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255937401 10000000000 42578073538847 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564095793/2500000000 : ℝ)^8303 ≤ (2771650940051/20000000000000 : ℝ)^6255 := by
    have hnat : (564095793 : ℕ)^8303*20000000000000^6255 ≤ 2771650940051^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564095793 2500000000 2771650940051 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336833317/2500000000 : ℝ), (5255937401/10000000000 : ℝ), (-564095793/2500000000 : ℝ)] ![(1742546869719/4000000000000 : ℝ), (42578073538847/100000000000000 : ℝ), (2771650940051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336833317/2500000000 : ℝ)|^8303 ≤ (1742546869719/4000000000000 : ℝ)^6255
        have hw : |(1336833317/2500000000 : ℝ)|=(1336833317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255937401/10000000000 : ℝ)|^8303 ≤ (42578073538847/100000000000000 : ℝ)^6255
        have hw : |(5255937401/10000000000 : ℝ)|=(5255937401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564095793/2500000000 : ℝ)|^8303 ≤ (2771650940051/20000000000000 : ℝ)^6255
        have hw : |(-564095793/2500000000 : ℝ)|=(564095793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368678263/10000000000 : ℝ)*x 0 + (169011307/400000000 : ℝ)*x 1 + (2258475747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368678263/10000000000 : ℝ)^8303 ≤ (16655749441651/50000000000000 : ℝ)^6255 := by
    have hnat : (4368678263 : ℕ)^8303*50000000000000^6255 ≤ 16655749441651^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368678263 10000000000 16655749441651 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169011307/400000000 : ℝ)^8303 ≤ (31867954509611/100000000000000 : ℝ)^6255 := by
    have hnat : (169011307 : ℕ)^8303*100000000000000^6255 ≤ 31867954509611^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169011307 400000000 31867954509611 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258475747/5000000000 : ℝ)^8303 ≤ (34820546596887/100000000000000 : ℝ)^6255 := by
    have hnat : (2258475747 : ℕ)^8303*100000000000000^6255 ≤ 34820546596887^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258475747 5000000000 34820546596887 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368678263/10000000000 : ℝ), (169011307/400000000 : ℝ), (2258475747/5000000000 : ℝ)] ![(16655749441651/50000000000000 : ℝ), (31867954509611/100000000000000 : ℝ), (34820546596887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368678263/10000000000 : ℝ)|^8303 ≤ (16655749441651/50000000000000 : ℝ)^6255
        have hw : |(4368678263/10000000000 : ℝ)|=(4368678263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169011307/400000000 : ℝ)|^8303 ≤ (31867954509611/100000000000000 : ℝ)^6255
        have hw : |(169011307/400000000 : ℝ)|=(169011307/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258475747/5000000000 : ℝ)|^8303 ≤ (34820546596887/100000000000000 : ℝ)^6255
        have hw : |(2258475747/5000000000 : ℝ)|=(2258475747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109069557/500000000 : ℝ)*x 0 + (5256362467/10000000000 : ℝ)*x 1 + (5403041671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109069557/500000000 : ℝ)^8303 ≤ (13250216099841/100000000000000 : ℝ)^6255 := by
    have hnat : (109069557 : ℕ)^8303*100000000000000^6255 ≤ 13250216099841^6255*500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109069557 500000000 13250216099841 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256362467/10000000000 : ℝ)^8303 ≤ (10645661120093/25000000000000 : ℝ)^6255 := by
    have hnat : (5256362467 : ℕ)^8303*25000000000000^6255 ≤ 10645661120093^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256362467 10000000000 10645661120093 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403041671/10000000000 : ℝ)^8303 ≤ (44167139406601/100000000000000 : ℝ)^6255 := by
    have hnat : (5403041671 : ℕ)^8303*100000000000000^6255 ≤ 44167139406601^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403041671 10000000000 44167139406601 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109069557/500000000 : ℝ), (5256362467/10000000000 : ℝ), (5403041671/10000000000 : ℝ)] ![(13250216099841/100000000000000 : ℝ), (10645661120093/25000000000000 : ℝ), (44167139406601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109069557/500000000 : ℝ)|^8303 ≤ (13250216099841/100000000000000 : ℝ)^6255
        have hw : |(-109069557/500000000 : ℝ)|=(109069557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256362467/10000000000 : ℝ)|^8303 ≤ (10645661120093/25000000000000 : ℝ)^6255
        have hw : |(5256362467/10000000000 : ℝ)|=(5256362467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403041671/10000000000 : ℝ)|^8303 ≤ (44167139406601/100000000000000 : ℝ)^6255
        have hw : |(5403041671/10000000000 : ℝ)|=(5403041671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655023613/5000000000 : ℝ)*x 0 + (-2109278991/10000000000 : ℝ)*x 1 + (5403041811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655023613/5000000000 : ℝ)^8303 ≤ (10790228379487/25000000000000 : ℝ)^6255 := by
    have hnat : (2655023613 : ℕ)^8303*25000000000000^6255 ≤ 10790228379487^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655023613 5000000000 10790228379487 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109278991/10000000000 : ℝ)^8303 ≤ (12671945532411/100000000000000 : ℝ)^6255 := by
    have hnat : (2109278991 : ℕ)^8303*100000000000000^6255 ≤ 12671945532411^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109278991 10000000000 12671945532411 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403041811/10000000000 : ℝ)^8303 ≤ (44167140925737/100000000000000 : ℝ)^6255 := by
    have hnat : (5403041811 : ℕ)^8303*100000000000000^6255 ≤ 44167140925737^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403041811 10000000000 44167140925737 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655023613/5000000000 : ℝ), (-2109278991/10000000000 : ℝ), (5403041811/10000000000 : ℝ)] ![(10790228379487/25000000000000 : ℝ), (12671945532411/100000000000000 : ℝ), (44167140925737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655023613/5000000000 : ℝ)|^8303 ≤ (10790228379487/25000000000000 : ℝ)^6255
        have hw : |(2655023613/5000000000 : ℝ)|=(2655023613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109278991/10000000000 : ℝ)|^8303 ≤ (12671945532411/100000000000000 : ℝ)^6255
        have hw : |(-2109278991/10000000000 : ℝ)|=(2109278991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403041811/10000000000 : ℝ)|^8303 ≤ (44167140925737/100000000000000 : ℝ)^6255
        have hw : |(5403041811/10000000000 : ℝ)|=(5403041811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062009489/2000000000 : ℝ)*x 0 + (5403041737/10000000000 : ℝ)*x 1 + (-527319699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062009489/2000000000 : ℝ)^8303 ≤ (21580457940421/50000000000000 : ℝ)^6255 := by
    have hnat : (1062009489 : ℕ)^8303*50000000000000^6255 ≤ 21580457940421^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062009489 2000000000 21580457940421 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403041737/10000000000 : ℝ)^8303 ≤ (8833428024553/20000000000000 : ℝ)^6255 := by
    have hnat : (5403041737 : ℕ)^8303*20000000000000^6255 ≤ 8833428024553^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403041737 10000000000 8833428024553 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527319699/2500000000 : ℝ)^8303 ≤ (2534388795467/20000000000000 : ℝ)^6255 := by
    have hnat : (527319699 : ℕ)^8303*20000000000000^6255 ≤ 2534388795467^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527319699 2500000000 2534388795467 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062009489/2000000000 : ℝ), (5403041737/10000000000 : ℝ), (-527319699/2500000000 : ℝ)] ![(21580457940421/50000000000000 : ℝ), (8833428024553/20000000000000 : ℝ), (2534388795467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062009489/2000000000 : ℝ)|^8303 ≤ (21580457940421/50000000000000 : ℝ)^6255
        have hw : |(1062009489/2000000000 : ℝ)|=(1062009489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403041737/10000000000 : ℝ)|^8303 ≤ (8833428024553/20000000000000 : ℝ)^6255
        have hw : |(5403041737/10000000000 : ℝ)|=(5403041737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527319699/2500000000 : ℝ)|^8303 ≤ (2534388795467/20000000000000 : ℝ)^6255
        have hw : |(-527319699/2500000000 : ℝ)|=(527319699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s4_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368693087/10000000000 : ℝ)*x 0 + (4516110801/10000000000 : ℝ)*x 1 + (4226126903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368693087/10000000000 : ℝ)^8303 ≤ (6662329785381/20000000000000 : ℝ)^6255 := by
    have hnat : (4368693087 : ℕ)^8303*20000000000000^6255 ≤ 6662329785381^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368693087 10000000000 6662329785381 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516110801/10000000000 : ℝ)^8303 ≤ (2175746509277/6250000000000 : ℝ)^6255 := by
    have hnat : (4516110801 : ℕ)^8303*6250000000000^6255 ≤ 2175746509277^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516110801 10000000000 2175746509277 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226126903/10000000000 : ℝ)^8303 ≤ (31876406910759/100000000000000 : ℝ)^6255 := by
    have hnat : (4226126903 : ℕ)^8303*100000000000000^6255 ≤ 31876406910759^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226126903 10000000000 31876406910759 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368693087/10000000000 : ℝ), (4516110801/10000000000 : ℝ), (4226126903/10000000000 : ℝ)] ![(6662329785381/20000000000000 : ℝ), (2175746509277/6250000000000 : ℝ), (31876406910759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368693087/10000000000 : ℝ)|^8303 ≤ (6662329785381/20000000000000 : ℝ)^6255
        have hw : |(4368693087/10000000000 : ℝ)|=(4368693087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516110801/10000000000 : ℝ)|^8303 ≤ (2175746509277/6250000000000 : ℝ)^6255
        have hw : |(4516110801/10000000000 : ℝ)|=(4516110801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226126903/10000000000 : ℝ)|^8303 ≤ (31876406910759/100000000000000 : ℝ)^6255
        have hw : |(4226126903/10000000000 : ℝ)|=(4226126903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2969/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5269/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11113/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2969/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5269/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2969/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5269/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2969/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5269/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2969/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5269/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2969/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5269/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2969/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5269/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5269/50000 : ℝ) ^ (4151/1024 : ℝ) ≤ (5464044249427279/50000000000000000000 : ℝ) := by
    have hpowers : (5269/50000 : ℝ)^4151 ≤ (5464044249427279/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5269 : ℕ)^4151*50000000000000000000^1024 ≤ 5464044249427279^1024*50000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5269 50000 5464044249427279 50000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5269/50000 : ℝ)) (X := (5464044249427279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2969/20000 : ℝ) ^ (4151/1024 : ℝ) ≤ (175341854301347/400000000000000000 : ℝ) := by
    have hpowers : (2969/20000 : ℝ)^4151 ≤ (175341854301347/400000000000000000 : ℝ)^1024 := by
      have hnat : (2969 : ℕ)^4151*400000000000000000^1024 ≤ 175341854301347^1024*20000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2969 20000 175341854301347 400000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2969/20000 : ℝ)) (X := (175341854301347/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005464044249427279/25000000000000000000 : ℝ) ≤ (10000539120285241/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (25005464044249427279/25000000000000000000 : ℝ)^1024 ≤ (10000539120285241/10000000000000000 : ℝ)^4151 := by
      have hnat : (25005464044249427279 : ℕ)^1024*10000000000000000^4151 ≤ 10000539120285241^4151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005464044249427279 25000000000000000000 10000539120285241 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539120285241/10000000000000000 : ℝ)) (X := (25005464044249427279/25000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013690888018547827/25000000000000000000 : ℝ) ≤ (5000675335025567/5000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (25013690888018547827/25000000000000000000 : ℝ)^1024 ≤ (5000675335025567/5000000000000000 : ℝ)^4151 := by
      have hnat : (25013690888018547827 : ℕ)^1024*5000000000000000^4151 ≤ 5000675335025567^4151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013690888018547827 25000000000000000000 5000675335025567 5000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000675335025567/5000000000000000 : ℝ)) (X := (25013690888018547827/25000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (200175341854301347/200000000000000000 : ℝ) ≤ (10002162219817027/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (200175341854301347/200000000000000000 : ℝ)^1024 ≤ (10002162219817027/10000000000000000 : ℝ)^4151 := by
      have hnat : (200175341854301347 : ℕ)^1024*10000000000000000^4151 ≤ 10002162219817027^4151*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200175341854301347 200000000000000000 10002162219817027 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002162219817027/10000000000000000 : ℝ)) (X := (200175341854301347/200000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5464044249427279/50000000000000000000 : ℝ) ≤ ((43055217768202572119/43070000000000000000 : ℝ)+2*(811549765893/430700000000000 : ℝ)*(5269/50000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (43055217768202572119/43070000000000000000 : ℝ)+2*(811549765893/430700000000000 : ℝ)*(5269/50000 : ℝ)=(10000539120285241/10000000000000000 : ℝ) by norm_num, show 1+2*(5464044249427279/50000000000000000000 : ℝ)=(25005464044249427279/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(175341854301347/400000000000000000 : ℝ)+(5464044249427279/50000000000000000000 : ℝ) ≤ ((43055217768202572119/43070000000000000000 : ℝ)+(811549765893/430700000000000 : ℝ)*((2969/20000 : ℝ)+(5269/50000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (43055217768202572119/43070000000000000000 : ℝ)+(811549765893/430700000000000 : ℝ)*((2969/20000 : ℝ)+(5269/50000 : ℝ))=(5000675335025567/5000000000000000 : ℝ) by norm_num, show 1+(175341854301347/400000000000000000 : ℝ)+(5464044249427279/50000000000000000000 : ℝ)=(25013690888018547827/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(175341854301347/400000000000000000 : ℝ) ≤ ((43055217768202572119/43070000000000000000 : ℝ)+2*(811549765893/430700000000000 : ℝ)*(2969/20000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (43055217768202572119/43070000000000000000 : ℝ)+2*(811549765893/430700000000000 : ℝ)*(2969/20000 : ℝ)=(10002162219817027/10000000000000000 : ℝ) by norm_num, show 1+2*(175341854301347/400000000000000000 : ℝ)=(200175341854301347/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43055217768202572119/43070000000000000000 : ℝ)*(X 1 0+X 2 0)+(811549765893/430700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5269/50000 : ℝ)) (hi := (2969/20000 : ℝ)) (c := (43055217768202572119/43070000000000000000 : ℝ)) (alpha := (811549765893/430700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43055217768202572119/43070000000000000000 : ℝ)*(X 0 1+X 2 1)+(811549765893/430700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5269/50000 : ℝ)) (hi := (2969/20000 : ℝ)) (c := (43055217768202572119/43070000000000000000 : ℝ)) (alpha := (811549765893/430700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43055217768202572119/43070000000000000000 : ℝ)*(X 0 2+X 1 2)+(811549765893/430700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5269/50000 : ℝ)) (hi := (2969/20000 : ℝ)) (c := (43055217768202572119/43070000000000000000 : ℝ)) (alpha := (811549765893/430700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2181384279/10000000000 : ℝ)*X 0 0+(5403468253/10000000000 : ℝ)*X 0 1+(5255937157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673666841/5000000000 : ℝ)*X 1 0+(-2256382319/10000000000 : ℝ)*X 1 1+(164248051/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336833317/2500000000 : ℝ)*X 2 0+(5255937401/10000000000 : ℝ)*X 2 1+(-564095793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368678263/10000000000 : ℝ)*X 0 0+(169011307/400000000 : ℝ)*X 0 1+(2258475747/5000000000 : ℝ)*X 0 2+(4368678263/10000000000 : ℝ)*X 1 0+(169011307/400000000 : ℝ)*X 1 1+(2258475747/5000000000 : ℝ)*X 1 2+(4368678263/10000000000 : ℝ)*X 2 0+(169011307/400000000 : ℝ)*X 2 1+(2258475747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109069557/500000000 : ℝ)*X 0 0+(5256362467/10000000000 : ℝ)*X 0 1+(5403041671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655023613/5000000000 : ℝ)*X 1 0+(-2109278991/10000000000 : ℝ)*X 1 1+(5403041811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062009489/2000000000 : ℝ)*X 2 0+(5403041737/10000000000 : ℝ)*X 2 1+(-527319699/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368693087/10000000000 : ℝ)*X 0 0+(4516110801/10000000000 : ℝ)*X 0 1+(4226126903/10000000000 : ℝ)*X 0 2+(4368693087/10000000000 : ℝ)*X 1 0+(4516110801/10000000000 : ℝ)*X 1 1+(4226126903/10000000000 : ℝ)*X 1 2+(4368693087/10000000000 : ℝ)*X 2 0+(4516110801/10000000000 : ℝ)*X 2 1+(4226126903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5083502888064348344077544703/2153500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (272303819/10000000000000 : ℝ)*(base19) + (1421469463/50000000000000 : ℝ)*(base23) + (1348921/390625000000 : ℝ)*(upper2) + (409546651/50000000000000 : ℝ)*(upper3) + (5103510785382579/100000000000000 : ℝ)*(major0) + (5103510785382579/100000000000000 : ℝ)*(major1) + (255175539269129/5000000000000 : ℝ)*(major2) + (6778334657382261/100000000000000 : ℝ)*(sp0) + (6778385957598533/100000000000000 : ℝ)*(sp1) + (3389192840578133/50000000000000 : ℝ)*(sp2) + (1714292348894031/50000000000000 : ℝ)*(sp3) + (27011627231/50000000000000 : ℝ)*(sp4) + (156541531/100000000000000 : ℝ)*(sp6) + (9622730891/20000000000000 : ℝ)*(sp7) + (857158202860629/25000000000000 : ℝ)*(f.failure) + (1694597170159181/25000000000000 : ℝ)*(f.sum) + (226861204548547/43070000000000000000000000000 : ℝ)*base65 + (30014644410596285099/4307000000000000000000000000000000 : ℝ)*base68 + (1750521274667849351/215350000000000000000000000000000 : ℝ)*base69 + (40771830459231285099/4307000000000000000000000000000000 : ℝ)*base72 + (192715919971473/43070000000000000000000000000 : ℝ)*base74 + (1431799541444100649/215350000000000000000000000000000 : ℝ)*base76 + (37694692816459585099/4307000000000000000000000000000000 : ℝ)*base78 + (28841850917432414901/4307000000000000000000000000000000 : ℝ)*base79 + (31487119159/2691875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12137943/2500000000000000000000 : ℝ)*base90 + (12137943/2500000000000000000000 : ℝ)*base92 + (37137943/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105630733635602655475233/21535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (645705131/100000000000000 : ℝ)*(base19) + (613902357/50000000000000 : ℝ)*(base23) + (25221141/12500000000000 : ℝ)*(upper3) + (105498221/100000000000000 : ℝ)*(lower4) + (60225517/25000000000000 : ℝ)*(upper5) + (5133034543263111/100000000000000 : ℝ)*(major0) + (5133034543263111/100000000000000 : ℝ)*(major1) + (5133034543263111/100000000000000 : ℝ)*(major2) + (6475181183/50000000000000 : ℝ)*(sp1) + (1719508637/6250000000000 : ℝ)*(sp2) + (6817601505710323/100000000000000 : ℝ)*(sp4) + (272703516385713/4000000000000 : ℝ)*(sp5) + (6817572765767417/100000000000000 : ℝ)*(sp6) + (86211685432837/2500000000000 : ℝ)*(sp7) + (86211685432837/2500000000000 : ℝ)*(f.failure) + (6817601505710323/100000000000000 : ℝ)*(f.sum) + (124678479154223/21535000000000000000000000000 : ℝ)*base65 + (44071234150335102209/4307000000000000000000000000000000 : ℝ)*base67 + (7068696358228897791/4307000000000000000000000000000000 : ℝ)*base70 + (1757112938471897791/4307000000000000000000000000000000 : ℝ)*base72 + (52972304793169/10767500000000000000000000000 : ℝ)*base73 + (29871393223993102209/4307000000000000000000000000000000 : ℝ)*base75 + (4096074396115102209/4307000000000000000000000000000000 : ℝ)*base77 + (23580345902024897791/4307000000000000000000000000000000 : ℝ)*base80 + (122303535955183/21535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (617479/250000000000000000000 : ℝ)*base90 + (617479/250000000000000000000 : ℝ)*base92 + (617479/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1110_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2969/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5269/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11113/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_s5_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182096001/10000000000 : ℝ)*x 0 + (33723541/62500000 : ℝ)*x 1 + (2631585921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182096001/10000000000 : ℝ)^8303 ≤ (3313974925247/25000000000000 : ℝ)^6255 := by
    have hnat : (2182096001 : ℕ)^8303*25000000000000^6255 ≤ 3313974925247^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182096001 10000000000 3313974925247 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33723541/62500000 : ℝ)^8303 ≤ (4408821478087/10000000000000 : ℝ)^6255 := by
    have hnat : (33723541 : ℕ)^8303*10000000000000^6255 ≤ 4408821478087^6255*62500000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33723541 62500000 4408821478087 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631585921/5000000000 : ℝ)^8303 ≤ (4265588549743/10000000000000 : ℝ)^6255 := by
    have hnat : (2631585921 : ℕ)^8303*10000000000000^6255 ≤ 4265588549743^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631585921 5000000000 4265588549743 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182096001/10000000000 : ℝ), (33723541/62500000 : ℝ), (2631585921/5000000000 : ℝ)] ![(3313974925247/25000000000000 : ℝ), (4408821478087/10000000000000 : ℝ), (4265588549743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182096001/10000000000 : ℝ)|^8303 ≤ (3313974925247/25000000000000 : ℝ)^6255
        have hw : |(-2182096001/10000000000 : ℝ)|=(2182096001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33723541/62500000 : ℝ)|^8303 ≤ (4408821478087/10000000000000 : ℝ)^6255
        have hw : |(33723541/62500000 : ℝ)|=(33723541/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631585921/5000000000 : ℝ)|^8303 ≤ (4265588549743/10000000000000 : ℝ)^6255
        have hw : |(2631585921/5000000000 : ℝ)|=(2631585921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345407809/10000000000 : ℝ)*x 0 + (-2249389527/10000000000 : ℝ)*x 1 + (5263171613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345407809/10000000000 : ℝ)^8303 ≤ (21771425322673/50000000000000 : ℝ)^6255 := by
    have hnat : (5345407809 : ℕ)^8303*50000000000000^6255 ≤ 21771425322673^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345407809 10000000000 21771425322673 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249389527/10000000000 : ℝ)^8303 ≤ (13801266306361/100000000000000 : ℝ)^6255 := by
    have hnat : (2249389527 : ℕ)^8303*100000000000000^6255 ≤ 13801266306361^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249389527 10000000000 13801266306361 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263171613/10000000000 : ℝ)^8303 ≤ (8531176606761/20000000000000 : ℝ)^6255 := by
    have hnat : (5263171613 : ℕ)^8303*20000000000000^6255 ≤ 8531176606761^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263171613 10000000000 8531176606761 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345407809/10000000000 : ℝ), (-2249389527/10000000000 : ℝ), (5263171613/10000000000 : ℝ)] ![(21771425322673/50000000000000 : ℝ), (13801266306361/100000000000000 : ℝ), (8531176606761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345407809/10000000000 : ℝ)|^8303 ≤ (21771425322673/50000000000000 : ℝ)^6255
        have hw : |(5345407809/10000000000 : ℝ)|=(5345407809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249389527/10000000000 : ℝ)|^8303 ≤ (13801266306361/100000000000000 : ℝ)^6255
        have hw : |(-2249389527/10000000000 : ℝ)|=(2249389527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263171613/10000000000 : ℝ)|^8303 ≤ (8531176606761/20000000000000 : ℝ)^6255
        have hw : |(5263171613/10000000000 : ℝ)|=(5263171613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336351627/2500000000 : ℝ)*x 0 + (5263172261/10000000000 : ℝ)*x 1 + (-2249390399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336351627/2500000000 : ℝ)^8303 ≤ (43542836577713/100000000000000 : ℝ)^6255 := by
    have hnat : (1336351627 : ℕ)^8303*100000000000000^6255 ≤ 43542836577713^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336351627 2500000000 43542836577713 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263172261/10000000000 : ℝ)^8303 ≤ (42655890005111/100000000000000 : ℝ)^6255 := by
    have hnat : (5263172261 : ℕ)^8303*100000000000000^6255 ≤ 42655890005111^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263172261 10000000000 42655890005111 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249390399/10000000000 : ℝ)^8303 ≤ (6900636704163/50000000000000 : ℝ)^6255 := by
    have hnat : (2249390399 : ℕ)^8303*50000000000000^6255 ≤ 6900636704163^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249390399 10000000000 6900636704163 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336351627/2500000000 : ℝ), (5263172261/10000000000 : ℝ), (-2249390399/10000000000 : ℝ)] ![(43542836577713/100000000000000 : ℝ), (42655890005111/100000000000000 : ℝ), (6900636704163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336351627/2500000000 : ℝ)|^8303 ≤ (43542836577713/100000000000000 : ℝ)^6255
        have hw : |(1336351627/2500000000 : ℝ)|=(1336351627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263172261/10000000000 : ℝ)|^8303 ≤ (42655890005111/100000000000000 : ℝ)^6255
        have hw : |(5263172261/10000000000 : ℝ)|=(5263172261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2249390399/10000000000 : ℝ)|^8303 ≤ (6900636704163/50000000000000 : ℝ)^6255
        have hw : |(-2249390399/10000000000 : ℝ)|=(2249390399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092273049/2500000000 : ℝ)*x 0 + (2119996919/5000000000 : ℝ)*x 1 + (4502132761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092273049/2500000000 : ℝ)^8303 ≤ (16657844319133/50000000000000 : ℝ)^6255 := by
    have hnat : (1092273049 : ℕ)^8303*50000000000000^6255 ≤ 16657844319133^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092273049 2500000000 16657844319133 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119996919/5000000000 : ℝ)^8303 ≤ (2000957598311/6250000000000 : ℝ)^6255 := by
    have hnat : (2119996919 : ℕ)^8303*6250000000000^6255 ≤ 2000957598311^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119996919 5000000000 2000957598311 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502132761/10000000000 : ℝ)^8303 ≤ (4333623722763/12500000000000 : ℝ)^6255 := by
    have hnat : (4502132761 : ℕ)^8303*12500000000000^6255 ≤ 4333623722763^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502132761 10000000000 4333623722763 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092273049/2500000000 : ℝ), (2119996919/5000000000 : ℝ), (4502132761/10000000000 : ℝ)] ![(16657844319133/50000000000000 : ℝ), (2000957598311/6250000000000 : ℝ), (4333623722763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092273049/2500000000 : ℝ)|^8303 ≤ (16657844319133/50000000000000 : ℝ)^6255
        have hw : |(1092273049/2500000000 : ℝ)|=(1092273049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119996919/5000000000 : ℝ)|^8303 ≤ (2000957598311/6250000000000 : ℝ)^6255
        have hw : |(2119996919/5000000000 : ℝ)|=(2119996919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502132761/10000000000 : ℝ)|^8303 ≤ (4333623722763/12500000000000 : ℝ)^6255
        have hw : |(4502132761/10000000000 : ℝ)|=(4502132761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182100733/10000000000 : ℝ)*x 0 + (2631757951/5000000000 : ℝ)*x 1 + (2697710883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182100733/10000000000 : ℝ)^8303 ≤ (3313984464799/25000000000000 : ℝ)^6255 := by
    have hnat : (2182100733 : ℕ)^8303*25000000000000^6255 ≤ 3313984464799^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182100733 10000000000 3313984464799 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631757951/5000000000 : ℝ)^8303 ≤ (42659586999261/100000000000000 : ℝ)^6255 := by
    have hnat : (2631757951 : ℕ)^8303*100000000000000^6255 ≤ 42659586999261^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631757951 5000000000 42659586999261 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697710883/5000000000 : ℝ)^8303 ≤ (22042237559907/50000000000000 : ℝ)^6255 := by
    have hnat : (2697710883 : ℕ)^8303*50000000000000^6255 ≤ 22042237559907^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697710883 5000000000 22042237559907 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182100733/10000000000 : ℝ), (2631757951/5000000000 : ℝ), (2697710883/5000000000 : ℝ)] ![(3313984464799/25000000000000 : ℝ), (42659586999261/100000000000000 : ℝ), (22042237559907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182100733/10000000000 : ℝ)|^8303 ≤ (3313984464799/25000000000000 : ℝ)^6255
        have hw : |(-2182100733/10000000000 : ℝ)|=(2182100733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631757951/5000000000 : ℝ)|^8303 ≤ (42659586999261/100000000000000 : ℝ)^6255
        have hw : |(2631757951/5000000000 : ℝ)|=(2631757951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697710883/5000000000 : ℝ)|^8303 ≤ (22042237559907/50000000000000 : ℝ)^6255
        have hw : |(2697710883/5000000000 : ℝ)|=(2697710883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327973721/2500000000 : ℝ)*x 0 + (-423428161/2000000000 : ℝ)*x 1 + (215816853/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327973721/2500000000 : ℝ)^8303 ≤ (43180849897419/100000000000000 : ℝ)^6255 := by
    have hnat : (1327973721 : ℕ)^8303*100000000000000^6255 ≤ 43180849897419^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327973721 2500000000 43180849897419 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423428161/2000000000 : ℝ)^8303 ≤ (12734679745871/100000000000000 : ℝ)^6255 := by
    have hnat : (423428161 : ℕ)^8303*100000000000000^6255 ≤ 12734679745871^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423428161 2000000000 12734679745871 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215816853/400000000 : ℝ)^8303 ≤ (22042235168373/50000000000000 : ℝ)^6255 := by
    have hnat : (215816853 : ℕ)^8303*50000000000000^6255 ≤ 22042235168373^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215816853 400000000 22042235168373 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327973721/2500000000 : ℝ), (-423428161/2000000000 : ℝ), (215816853/400000000 : ℝ)] ![(43180849897419/100000000000000 : ℝ), (12734679745871/100000000000000 : ℝ), (22042235168373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327973721/2500000000 : ℝ)|^8303 ≤ (43180849897419/100000000000000 : ℝ)^6255
        have hw : |(1327973721/2500000000 : ℝ)|=(1327973721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-423428161/2000000000 : ℝ)|^8303 ≤ (12734679745871/100000000000000 : ℝ)^6255
        have hw : |(-423428161/2000000000 : ℝ)|=(423428161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215816853/400000000 : ℝ)|^8303 ≤ (22042235168373/50000000000000 : ℝ)^6255
        have hw : |(215816853/400000000 : ℝ)|=(215816853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663986867/1250000000 : ℝ)*x 0 + (1348855429/2500000000 : ℝ)*x 1 + (-529285051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663986867/1250000000 : ℝ)^8303 ≤ (8636170091707/20000000000000 : ℝ)^6255 := by
    have hnat : (663986867 : ℕ)^8303*20000000000000^6255 ≤ 8636170091707^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663986867 1250000000 8636170091707 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348855429/2500000000 : ℝ)^8303 ≤ (11021118644379/25000000000000 : ℝ)^6255 := by
    have hnat : (1348855429 : ℕ)^8303*25000000000000^6255 ≤ 11021118644379^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348855429 2500000000 11021118644379 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529285051/2500000000 : ℝ)^8303 ≤ (6367337473603/50000000000000 : ℝ)^6255 := by
    have hnat : (529285051 : ℕ)^8303*50000000000000^6255 ≤ 6367337473603^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529285051 2500000000 6367337473603 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663986867/1250000000 : ℝ), (1348855429/2500000000 : ℝ), (-529285051/2500000000 : ℝ)] ![(8636170091707/20000000000000 : ℝ), (11021118644379/25000000000000 : ℝ), (6367337473603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663986867/1250000000 : ℝ)|^8303 ≤ (8636170091707/20000000000000 : ℝ)^6255
        have hw : |(663986867/1250000000 : ℝ)|=(663986867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348855429/2500000000 : ℝ)|^8303 ≤ (11021118644379/25000000000000 : ℝ)^6255
        have hw : |(1348855429/2500000000 : ℝ)|=(1348855429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529285051/2500000000 : ℝ)|^8303 ≤ (6367337473603/50000000000000 : ℝ)^6255
        have hw : |(-529285051/2500000000 : ℝ)|=(529285051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s5_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369103301/10000000000 : ℝ)*x 0 + (900290681/2000000000 : ℝ)*x 1 + (4240675419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369103301/10000000000 : ℝ)^8303 ≤ (16657900521429/50000000000000 : ℝ)^6255 := by
    have hnat : (4369103301 : ℕ)^8303*50000000000000^6255 ≤ 16657900521429^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369103301 10000000000 16657900521429 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900290681/2000000000 : ℝ)^8303 ≤ (34662045660783/100000000000000 : ℝ)^6255 := by
    have hnat : (900290681 : ℕ)^8303*100000000000000^6255 ≤ 34662045660783^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900290681 2000000000 34662045660783 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240675419/10000000000 : ℝ)^8303 ≤ (6404430656117/20000000000000 : ℝ)^6255 := by
    have hnat : (4240675419 : ℕ)^8303*20000000000000^6255 ≤ 6404430656117^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240675419 10000000000 6404430656117 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369103301/10000000000 : ℝ), (900290681/2000000000 : ℝ), (4240675419/10000000000 : ℝ)] ![(16657900521429/50000000000000 : ℝ), (34662045660783/100000000000000 : ℝ), (6404430656117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369103301/10000000000 : ℝ)|^8303 ≤ (16657900521429/50000000000000 : ℝ)^6255
        have hw : |(4369103301/10000000000 : ℝ)|=(4369103301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900290681/2000000000 : ℝ)|^8303 ≤ (34662045660783/100000000000000 : ℝ)^6255
        have hw : |(900290681/2000000000 : ℝ)|=(900290681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240675419/10000000000 : ℝ)|^8303 ≤ (6404430656117/20000000000000 : ℝ)^6255
        have hw : |(4240675419/10000000000 : ℝ)|=(4240675419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11267/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11113/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11113/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11113/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11113/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (6777132351050439/50000000000000000000 : ℝ) := by
    have hpowers : (11113/100000 : ℝ)^4151 ≤ (6777132351050439/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11113 : ℕ)^4151*50000000000000000000^1024 ≤ 6777132351050439^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11113 100000 6777132351050439 50000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11113/100000 : ℝ)) (X := (6777132351050439/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (9250032571313337/25000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^4151 ≤ (9250032571313337/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14237 : ℕ)^4151*25000000000000000000^1024 ≤ 9250032571313337^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 9250032571313337 25000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (9250032571313337/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006777132351050439/25000000000000000000 : ℝ) ≤ (1000066866538631/1000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (25006777132351050439/25000000000000000000 : ℝ)^1024 ≤ (1000066866538631/1000000000000000 : ℝ)^4151 := by
      have hnat : (25006777132351050439 : ℕ)^1024*1000000000000000^4151 ≤ 1000066866538631^4151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006777132351050439 25000000000000000000 1000066866538631 1000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066866538631/1000000000000000 : ℝ)) (X := (25006777132351050439/25000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025277197493677113/50000000000000000000 : ℝ) ≤ (10001246876559039/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50025277197493677113/50000000000000000000 : ℝ)^1024 ≤ (10001246876559039/10000000000000000 : ℝ)^4151 := by
      have hnat : (50025277197493677113 : ℕ)^1024*10000000000000000^4151 ≤ 10001246876559039^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025277197493677113 50000000000000000000 10001246876559039 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001246876559039/10000000000000000 : ℝ)) (X := (50025277197493677113/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509250032571313337/12500000000000000000 : ℝ) ≤ (1250228135966471/1250000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (12509250032571313337/12500000000000000000 : ℝ)^1024 ≤ (1250228135966471/1250000000000000 : ℝ)^4151 := by
      have hnat : (12509250032571313337 : ℕ)^1024*1250000000000000^4151 ≤ 1250228135966471^4151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509250032571313337 12500000000000000000 1250228135966471 1250000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250228135966471/1250000000000000 : ℝ)) (X := (12509250032571313337/12500000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6777132351050439/50000000000000000000 : ℝ) ≤ ((15614618794570878843/15620000000000000000 : ℝ)+2*(578211172729/312400000000000 : ℝ)*(11113/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (15614618794570878843/15620000000000000000 : ℝ)+2*(578211172729/312400000000000 : ℝ)*(11113/100000 : ℝ)=(1000066866538631/1000000000000000 : ℝ) by norm_num, show 1+2*(6777132351050439/50000000000000000000 : ℝ)=(25006777132351050439/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9250032571313337/25000000000000000000 : ℝ)+(6777132351050439/50000000000000000000 : ℝ) ≤ ((15614618794570878843/15620000000000000000 : ℝ)+(578211172729/312400000000000 : ℝ)*((14237/100000 : ℝ)+(11113/100000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (15614618794570878843/15620000000000000000 : ℝ)+(578211172729/312400000000000 : ℝ)*((14237/100000 : ℝ)+(11113/100000 : ℝ))=(10001246876559039/10000000000000000 : ℝ) by norm_num, show 1+(9250032571313337/25000000000000000000 : ℝ)+(6777132351050439/50000000000000000000 : ℝ)=(50025277197493677113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9250032571313337/25000000000000000000 : ℝ) ≤ ((15614618794570878843/15620000000000000000 : ℝ)+2*(578211172729/312400000000000 : ℝ)*(14237/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (15614618794570878843/15620000000000000000 : ℝ)+2*(578211172729/312400000000000 : ℝ)*(14237/100000 : ℝ)=(1250228135966471/1250000000000000 : ℝ) by norm_num, show 1+2*(9250032571313337/25000000000000000000 : ℝ)=(12509250032571313337/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15614618794570878843/15620000000000000000 : ℝ)*(X 1 0+X 2 0)+(578211172729/312400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (11113/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15614618794570878843/15620000000000000000 : ℝ)) (alpha := (578211172729/312400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15614618794570878843/15620000000000000000 : ℝ)*(X 0 1+X 2 1)+(578211172729/312400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (11113/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15614618794570878843/15620000000000000000 : ℝ)) (alpha := (578211172729/312400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15614618794570878843/15620000000000000000 : ℝ)*(X 0 2+X 1 2)+(578211172729/312400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (11113/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15614618794570878843/15620000000000000000 : ℝ)) (alpha := (578211172729/312400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2182096001/10000000000 : ℝ)*X 0 0+(33723541/62500000 : ℝ)*X 0 1+(2631585921/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345407809/10000000000 : ℝ)*X 1 0+(-2249389527/10000000000 : ℝ)*X 1 1+(5263171613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336351627/2500000000 : ℝ)*X 2 0+(5263172261/10000000000 : ℝ)*X 2 1+(-2249390399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092273049/2500000000 : ℝ)*X 0 0+(2119996919/5000000000 : ℝ)*X 0 1+(4502132761/10000000000 : ℝ)*X 0 2+(1092273049/2500000000 : ℝ)*X 1 0+(2119996919/5000000000 : ℝ)*X 1 1+(4502132761/10000000000 : ℝ)*X 1 2+(1092273049/2500000000 : ℝ)*X 2 0+(2119996919/5000000000 : ℝ)*X 2 1+(4502132761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2182100733/10000000000 : ℝ)*X 0 0+(2631757951/5000000000 : ℝ)*X 0 1+(2697710883/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327973721/2500000000 : ℝ)*X 1 0+(-423428161/2000000000 : ℝ)*X 1 1+(215816853/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663986867/1250000000 : ℝ)*X 2 0+(1348855429/2500000000 : ℝ)*X 2 1+(-529285051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369103301/10000000000 : ℝ)*X 0 0+(900290681/2000000000 : ℝ)*X 0 1+(4240675419/10000000000 : ℝ)*X 0 2+(4369103301/10000000000 : ℝ)*X 1 0+(900290681/2000000000 : ℝ)*X 1 1+(4240675419/10000000000 : ℝ)*X 1 2+(4369103301/10000000000 : ℝ)*X 2 0+(900290681/2000000000 : ℝ)*X 2 1+(4240675419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6353120525355545986892305317/781000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3314694031/100000000000000 : ℝ)*(base19) + (293575627/25000000000000 : ℝ)*(base23) + (12543237/100000000000000 : ℝ)*(upper2) + (327871269/100000000000000 : ℝ)*(upper3) + (1419605927697531/25000000000000 : ℝ)*(major0) + (1419605927697531/25000000000000 : ℝ)*(major1) + (45427389686321/800000000000 : ℝ)*(major2) + (377094817232011/5000000000000 : ℝ)*(sp0) + (7541973901911769/100000000000000 : ℝ)*(sp1) + (235685115145467/3125000000000 : ℝ)*(sp2) + (1907411342046827/50000000000000 : ℝ)*(sp3) + (80871965579/100000000000000 : ℝ)*(sp4) + (13089412087/25000000000000 : ℝ)*(sp6) + (47249727541/100000000000000 : ℝ)*(sp7) + (1907434966910597/50000000000000 : ℝ)*(f.failure) + (37709886083029/500000000000 : ℝ)*(f.sum) + (112801549283999/31240000000000000000000000000 : ℝ)*base66 + (2168642782242200867/390500000000000000000000000000000 : ℝ)*base68 + (32008952726226997/12496000000000000000000000000000 : ℝ)*base70 + (4624977414097700867/390500000000000000000000000000000 : ℝ)*base72 + (104654452020961/31240000000000000000000000000 : ℝ)*base73 + (174055178921154997/12496000000000000000000000000000 : ℝ)*base76 + (3835716714346313367/390500000000000000000000000000000 : ℝ)*base78 + (3245002055108313367/390500000000000000000000000000000 : ℝ)*base80 + (2872802982987/1952500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1679399/5000000000000000000000 : ℝ)*base90 + (1679399/5000000000000000000000 : ℝ)*base92 + (51679399/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8127338194486590228115372119/781000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (726079831/100000000000000 : ℝ)*(base19) + (1592396063/100000000000000 : ℝ)*(base23) + (105203501/50000000000000 : ℝ)*(lower2) + (464198611/100000000000000 : ℝ)*(lower4) + (2622201/20000000000000 : ℝ)*(lower5) + (713490637337589/12500000000000 : ℝ)*(major0) + (713490637337589/12500000000000 : ℝ)*(major1) + (5707925098700713/100000000000000 : ℝ)*(major2) + (49822921633/100000000000000 : ℝ)*(sp2) + (639499263/12500000000000 : ℝ)*(sp3) + (7581160339390823/100000000000000 : ℝ)*(sp4) + (473822475831937/6250000000000 : ℝ)*(sp5) + (3790554462036563/50000000000000 : ℝ)*(sp6) + (239667774696191/6250000000000 : ℝ)*(sp7) + (3834689511133159/100000000000000 : ℝ)*(f.failure) + (7581160339390823/100000000000000 : ℝ)*(f.sum) + (77436917957523/6248000000000000000000000000 : ℝ)*base66 + (1333617638997164223/195250000000000000000000000000000 : ℝ)*base68 + (8098600411381115059/1562000000000000000000000000000000 : ℝ)*base69 + (3039676406294664223/195250000000000000000000000000000 : ℝ)*base72 + (40670719975691/6248000000000000000000000000 : ℝ)*base74 + (13567395177497115059/1562000000000000000000000000000000 : ℝ)*base75 + (3902295055807220473/195250000000000000000000000000000 : ℝ)*base78 + (2532446344782470473/195250000000000000000000000000000 : ℝ)*base80 + (8744329625223/3905000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (44596547/10000000000000000000000 : ℝ)*base89 + (44596547/10000000000000000000000 : ℝ)*base91 + (55403453/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1110_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11113/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1110_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (83/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1110_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1110_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1110_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (83/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
