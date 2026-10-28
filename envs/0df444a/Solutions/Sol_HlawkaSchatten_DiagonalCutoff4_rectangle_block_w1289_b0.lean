-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1289_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:09.966196+00:00
-- url     : https://prove2.me/submissions/dc6b1db2-e212-4727-8ad9-98be445f1569

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
theorem support_rectangle_w1289_s0_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-460224337/2500000000 : ℝ)*x 0 + (150503099/250000000 : ℝ)*x 1 + (4798107151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460224337/2500000000 : ℝ)^4249 ≤ (5378141469313/50000000000000 : ℝ)^3225 := by
    have hnat : (460224337 : ℕ)^4249*50000000000000^3225 ≤ 5378141469313^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460224337 2500000000 5378141469313 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150503099/250000000 : ℝ)^4249 ≤ (51241978266247/100000000000000 : ℝ)^3225 := by
    have hnat : (150503099 : ℕ)^4249*100000000000000^3225 ≤ 51241978266247^3225*250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150503099 250000000 51241978266247 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4798107151/10000000000 : ℝ)^4249 ≤ (9500434693443/25000000000000 : ℝ)^3225 := by
    have hnat : (4798107151 : ℕ)^4249*25000000000000^3225 ≤ 9500434693443^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798107151 10000000000 9500434693443 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460224337/2500000000 : ℝ), (150503099/250000000 : ℝ), (4798107151/10000000000 : ℝ)] ![(5378141469313/50000000000000 : ℝ), (51241978266247/100000000000000 : ℝ), (9500434693443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460224337/2500000000 : ℝ)|^4249 ≤ (5378141469313/50000000000000 : ℝ)^3225
        have hw : |(-460224337/2500000000 : ℝ)|=(460224337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150503099/250000000 : ℝ)|^4249 ≤ (51241978266247/100000000000000 : ℝ)^3225
        have hw : |(150503099/250000000 : ℝ)|=(150503099/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4798107151/10000000000 : ℝ)|^4249 ≤ (9500434693443/25000000000000 : ℝ)^3225
        have hw : |(4798107151/10000000000 : ℝ)|=(4798107151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5507755501/10000000000 : ℝ)*x 0 + (-63455161/250000000 : ℝ)*x 1 + (4798107197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507755501/10000000000 : ℝ)^4249 ≤ (45575252698569/100000000000000 : ℝ)^3225 := by
    have hnat : (5507755501 : ℕ)^4249*100000000000000^3225 ≤ 45575252698569^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507755501 10000000000 45575252698569 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63455161/250000000 : ℝ)^4249 ≤ (4105752009903/25000000000000 : ℝ)^3225 := by
    have hnat : (63455161 : ℕ)^4249*25000000000000^3225 ≤ 4105752009903^3225*250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63455161 250000000 4105752009903 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4798107197/10000000000 : ℝ)^4249 ≤ (1900086962689/5000000000000 : ℝ)^3225 := by
    have hnat : (4798107197 : ℕ)^4249*5000000000000^3225 ≤ 1900086962689^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798107197 10000000000 1900086962689 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507755501/10000000000 : ℝ), (-63455161/250000000 : ℝ), (4798107197/10000000000 : ℝ)] ![(45575252698569/100000000000000 : ℝ), (4105752009903/25000000000000 : ℝ), (1900086962689/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507755501/10000000000 : ℝ)|^4249 ≤ (45575252698569/100000000000000 : ℝ)^3225
        have hw : |(5507755501/10000000000 : ℝ)|=(5507755501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63455161/250000000 : ℝ)|^4249 ≤ (4105752009903/25000000000000 : ℝ)^3225
        have hw : |(-63455161/250000000 : ℝ)|=(63455161/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4798107197/10000000000 : ℝ)|^4249 ≤ (1900086962689/5000000000000 : ℝ)^3225
        have hw : |(4798107197/10000000000 : ℝ)|=(4798107197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753877581/5000000000 : ℝ)*x 0 + (2399053841/5000000000 : ℝ)*x 1 + (-2538206279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753877581/5000000000 : ℝ)^4249 ≤ (22787624501373/50000000000000 : ℝ)^3225 := by
    have hnat : (2753877581 : ℕ)^4249*50000000000000^3225 ≤ 22787624501373^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753877581 5000000000 22787624501373 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2399053841/5000000000 : ℝ)^4249 ≤ (38001744314733/100000000000000 : ℝ)^3225 := by
    have hnat : (2399053841 : ℕ)^4249*100000000000000^3225 ≤ 38001744314733^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399053841 5000000000 38001744314733 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538206279/10000000000 : ℝ)^4249 ≤ (4105751666781/25000000000000 : ℝ)^3225 := by
    have hnat : (2538206279 : ℕ)^4249*25000000000000^3225 ≤ 4105751666781^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538206279 10000000000 4105751666781 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753877581/5000000000 : ℝ), (2399053841/5000000000 : ℝ), (-2538206279/10000000000 : ℝ)] ![(22787624501373/50000000000000 : ℝ), (38001744314733/100000000000000 : ℝ), (4105751666781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753877581/5000000000 : ℝ)|^4249 ≤ (22787624501373/50000000000000 : ℝ)^3225
        have hw : |(2753877581/5000000000 : ℝ)|=(2753877581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2399053841/5000000000 : ℝ)|^4249 ≤ (38001744314733/100000000000000 : ℝ)^3225
        have hw : |(2399053841/5000000000 : ℝ)|=(2399053841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2538206279/10000000000 : ℝ)|^4249 ≤ (4105751666781/25000000000000 : ℝ)^3225
        have hw : |(-2538206279/10000000000 : ℝ)|=(2538206279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186793787/10000000000 : ℝ)*x 0 + (777407823/2500000000 : ℝ)*x 1 + (351142831/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186793787/10000000000 : ℝ)^4249 ≤ (992365514153/3125000000000 : ℝ)^3225 := by
    have hnat : (4186793787 : ℕ)^4249*3125000000000^3225 ≤ 992365514153^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186793787 10000000000 992365514153 3125000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777407823/2500000000 : ℝ)^4249 ≤ (21460218614071/100000000000000 : ℝ)^3225 := by
    have hnat : (777407823 : ℕ)^4249*100000000000000^3225 ≤ 21460218614071^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777407823 2500000000 21460218614071 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351142831/625000000 : ℝ)^4249 ≤ (9356816982503/20000000000000 : ℝ)^3225 := by
    have hnat : (351142831 : ℕ)^4249*20000000000000^3225 ≤ 9356816982503^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351142831 625000000 9356816982503 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186793787/10000000000 : ℝ), (777407823/2500000000 : ℝ), (351142831/625000000 : ℝ)] ![(992365514153/3125000000000 : ℝ), (21460218614071/100000000000000 : ℝ), (9356816982503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186793787/10000000000 : ℝ)|^4249 ≤ (992365514153/3125000000000 : ℝ)^3225
        have hw : |(4186793787/10000000000 : ℝ)|=(4186793787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777407823/2500000000 : ℝ)|^4249 ≤ (21460218614071/100000000000000 : ℝ)^3225
        have hw : |(777407823/2500000000 : ℝ)|=(777407823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(351142831/625000000 : ℝ)|^4249 ≤ (9356816982503/20000000000000 : ℝ)^3225
        have hw : |(351142831/625000000 : ℝ)|=(351142831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-922818833/5000000000 : ℝ)*x 0 + (4829651609/10000000000 : ℝ)*x 1 + (1197491591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (922818833/5000000000 : ℝ)^4249 ≤ (5396394901693/50000000000000 : ℝ)^3225 := by
    have hnat : (922818833 : ℕ)^4249*50000000000000^3225 ≤ 5396394901693^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922818833 5000000000 5396394901693 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4829651609/10000000000 : ℝ)^4249 ≤ (7666249358461/20000000000000 : ℝ)^3225 := by
    have hnat : (4829651609 : ℕ)^4249*20000000000000^3225 ≤ 7666249358461^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829651609 10000000000 7666249358461 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197491591/2000000000 : ℝ)^4249 ≤ (12718990846431/25000000000000 : ℝ)^3225 := by
    have hnat : (1197491591 : ℕ)^4249*25000000000000^3225 ≤ 12718990846431^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197491591 2000000000 12718990846431 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-922818833/5000000000 : ℝ), (4829651609/10000000000 : ℝ), (1197491591/2000000000 : ℝ)] ![(5396394901693/50000000000000 : ℝ), (7666249358461/20000000000000 : ℝ), (12718990846431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-922818833/5000000000 : ℝ)|^4249 ≤ (5396394901693/50000000000000 : ℝ)^3225
        have hw : |(-922818833/5000000000 : ℝ)|=(922818833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4829651609/10000000000 : ℝ)|^4249 ≤ (7666249358461/20000000000000 : ℝ)^3225
        have hw : |(4829651609/10000000000 : ℝ)|=(4829651609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1197491591/2000000000 : ℝ)|^4249 ≤ (12718990846431/25000000000000 : ℝ)^3225
        have hw : |(1197491591/2000000000 : ℝ)|=(1197491591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587546337/5000000000 : ℝ)*x 0 + (-1348853439/10000000000 : ℝ)*x 1 + (5987460559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587546337/5000000000 : ℝ)^4249 ≤ (1679351417719/4000000000000 : ℝ)^3225 := by
    have hnat : (2587546337 : ℕ)^4249*4000000000000^3225 ≤ 1679351417719^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587546337 5000000000 1679351417719 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348853439/10000000000 : ℝ)^4249 ≤ (1785055499903/25000000000000 : ℝ)^3225 := by
    have hnat : (1348853439 : ℕ)^4249*25000000000000^3225 ≤ 1785055499903^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348853439 10000000000 1785055499903 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5987460559/10000000000 : ℝ)^4249 ≤ (50875992537713/100000000000000 : ℝ)^3225 := by
    have hnat : (5987460559 : ℕ)^4249*100000000000000^3225 ≤ 50875992537713^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987460559 10000000000 50875992537713 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587546337/5000000000 : ℝ), (-1348853439/10000000000 : ℝ), (5987460559/10000000000 : ℝ)] ![(1679351417719/4000000000000 : ℝ), (1785055499903/25000000000000 : ℝ), (50875992537713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587546337/5000000000 : ℝ)|^4249 ≤ (1679351417719/4000000000000 : ℝ)^3225
        have hw : |(2587546337/5000000000 : ℝ)|=(2587546337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1348853439/10000000000 : ℝ)|^4249 ≤ (1785055499903/25000000000000 : ℝ)^3225
        have hw : |(-1348853439/10000000000 : ℝ)|=(1348853439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5987460559/10000000000 : ℝ)|^4249 ≤ (50875992537713/100000000000000 : ℝ)^3225
        have hw : |(5987460559/10000000000 : ℝ)|=(5987460559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103501879/200000000 : ℝ)*x 0 + (149686459/250000000 : ℝ)*x 1 + (-269771003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103501879/200000000 : ℝ)^4249 ≤ (20991899540809/50000000000000 : ℝ)^3225 := by
    have hnat : (103501879 : ℕ)^4249*50000000000000^3225 ≤ 20991899540809^3225*200000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103501879 200000000 20991899540809 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149686459/250000000 : ℝ)^4249 ≤ (50875967919731/100000000000000 : ℝ)^3225 := by
    have hnat : (149686459 : ℕ)^4249*100000000000000^3225 ≤ 50875967919731^3225*250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149686459 250000000 50875967919731 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269771003/2000000000 : ℝ)^4249 ≤ (1428046598239/20000000000000 : ℝ)^3225 := by
    have hnat : (269771003 : ℕ)^4249*20000000000000^3225 ≤ 1428046598239^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269771003 2000000000 1428046598239 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103501879/200000000 : ℝ), (149686459/250000000 : ℝ), (-269771003/2000000000 : ℝ)] ![(20991899540809/50000000000000 : ℝ), (50875967919731/100000000000000 : ℝ), (1428046598239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103501879/200000000 : ℝ)|^4249 ≤ (20991899540809/50000000000000 : ℝ)^3225
        have hw : |(103501879/200000000 : ℝ)|=(103501879/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149686459/250000000 : ℝ)|^4249 ≤ (50875967919731/100000000000000 : ℝ)^3225
        have hw : |(149686459/250000000 : ℝ)|=(149686459/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269771003/2000000000 : ℝ)|^4249 ≤ (1428046598239/20000000000000 : ℝ)^3225
        have hw : |(-269771003/2000000000 : ℝ)|=(269771003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s0_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419652903/1000000000 : ℝ)*x 0 + (694192061/1250000000 : ℝ)*x 1 + (3176683101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419652903/1000000000 : ℝ)^4249 ≤ (31853016897851/100000000000000 : ℝ)^3225 := by
    have hnat : (419652903 : ℕ)^4249*100000000000000^3225 ≤ 31853016897851^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419652903 1000000000 31853016897851 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694192061/1250000000 : ℝ)^4249 ≤ (4607502046943/10000000000000 : ℝ)^3225 := by
    have hnat : (694192061 : ℕ)^4249*10000000000000^3225 ≤ 4607502046943^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694192061 1250000000 4607502046943 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3176683101/10000000000 : ℝ)^4249 ≤ (11035981310279/50000000000000 : ℝ)^3225 := by
    have hnat : (3176683101 : ℕ)^4249*50000000000000^3225 ≤ 11035981310279^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3176683101 10000000000 11035981310279 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419652903/1000000000 : ℝ), (694192061/1250000000 : ℝ), (3176683101/10000000000 : ℝ)] ![(31853016897851/100000000000000 : ℝ), (4607502046943/10000000000000 : ℝ), (11035981310279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419652903/1000000000 : ℝ)|^4249 ≤ (31853016897851/100000000000000 : ℝ)^3225
        have hw : |(419652903/1000000000 : ℝ)|=(419652903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(694192061/1250000000 : ℝ)|^4249 ≤ (4607502046943/10000000000000 : ℝ)^3225
        have hw : |(694192061/1250000000 : ℝ)|=(694192061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3176683101/10000000000 : ℝ)|^4249 ≤ (11035981310279/50000000000000 : ℝ)^3225
        have hw : |(3176683101/10000000000 : ℝ)|=(3176683101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1009/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27257/100000 : ℝ)*pair X 0 0 := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (531/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^531 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^531*1^128 ≤ 0^128*1^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (531/128 : ℝ) ≤ (1117225268366906033/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^531 ≤ (1117225268366906033/50000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^531*50000000000000000000^128 ≤ 1117225268366906033^128*5^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1117225268366906033 50000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1117225268366906033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^531 := by
      have hnat : (1 : ℕ)^128*1^531 ≤ 1^531*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (51117225268366906033/50000000000000000000 : ℝ) ≤ (10053411646947749/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (51117225268366906033/50000000000000000000 : ℝ)^128 ≤ (10053411646947749/10000000000000000 : ℝ)^531 := by
      have hnat : (51117225268366906033 : ℕ)^128*10000000000000000^531 ≤ 10053411646947749^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51117225268366906033 50000000000000000000 10053411646947749 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053411646947749/10000000000000000 : ℝ)) (X := (51117225268366906033/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (26117225268366906033/25000000000000000000 : ℝ) ≤ (5053411646947749/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (26117225268366906033/25000000000000000000 : ℝ)^128 ≤ (5053411646947749/5000000000000000 : ℝ)^531 := by
      have hnat : (26117225268366906033 : ℕ)^128*5000000000000000^531 ≤ 5053411646947749^531*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26117225268366906033 25000000000000000000 5053411646947749 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5053411646947749/5000000000000000 : ℝ)) (X := (26117225268366906033/25000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(53411646947749/4000000000000000 : ℝ)*(0 : ℝ))^(531/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(53411646947749/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1117225268366906033/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(53411646947749/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(531/128 : ℝ) := by
    rw [show (1 : ℝ)+(53411646947749/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10053411646947749/10000000000000000 : ℝ) by norm_num, show 1+(1117225268366906033/50000000000000000000 : ℝ)+(0 : ℝ)=(51117225268366906033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1117225268366906033/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(53411646947749/4000000000000000 : ℝ)*(2/5 : ℝ))^(531/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(53411646947749/4000000000000000 : ℝ)*(2/5 : ℝ)=(5053411646947749/5000000000000000 : ℝ) by norm_num, show 1+2*(1117225268366906033/50000000000000000000 : ℝ)=(26117225268366906033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(53411646947749/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53411646947749/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(53411646947749/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53411646947749/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(53411646947749/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53411646947749/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-460224337/2500000000 : ℝ)*X 0 0+(150503099/250000000 : ℝ)*X 0 1+(4798107151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5507755501/10000000000 : ℝ)*X 1 0+(-63455161/250000000 : ℝ)*X 1 1+(4798107197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2753877581/5000000000 : ℝ)*X 2 0+(2399053841/5000000000 : ℝ)*X 2 1+(-2538206279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186793787/10000000000 : ℝ)*X 0 0+(777407823/2500000000 : ℝ)*X 0 1+(351142831/625000000 : ℝ)*X 0 2+(4186793787/10000000000 : ℝ)*X 1 0+(777407823/2500000000 : ℝ)*X 1 1+(351142831/625000000 : ℝ)*X 1 2+(4186793787/10000000000 : ℝ)*X 2 0+(777407823/2500000000 : ℝ)*X 2 1+(351142831/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-922818833/5000000000 : ℝ)*X 0 0+(4829651609/10000000000 : ℝ)*X 0 1+(1197491591/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587546337/5000000000 : ℝ)*X 1 0+(-1348853439/10000000000 : ℝ)*X 1 1+(5987460559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103501879/200000000 : ℝ)*X 2 0+(149686459/250000000 : ℝ)*X 2 1+(-269771003/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((419652903/1000000000 : ℝ)*X 0 0+(694192061/1250000000 : ℝ)*X 0 1+(3176683101/10000000000 : ℝ)*X 0 2+(419652903/1000000000 : ℝ)*X 1 0+(694192061/1250000000 : ℝ)*X 1 1+(3176683101/10000000000 : ℝ)*X 1 2+(419652903/1000000000 : ℝ)*X 2 0+(694192061/1250000000 : ℝ)*X 2 1+(3176683101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (220105718776131160337733/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120137261/100000000000000 : ℝ)*(base1) + (72356313/6250000000000 : ℝ)*(base19) + (553666723/50000000000000 : ℝ)*(base23) + (1160313/1000000000000 : ℝ)*(upper3) + (2783253/2000000000000 : ℝ)*(upper5) + (608474834391339/100000000000000 : ℝ)*(major0) + (608474834391339/100000000000000 : ℝ)*(major1) + (608474834391339/100000000000000 : ℝ)*(major2) + (409161357142441/50000000000000 : ℝ)*(sp0) + (204581267829057/25000000000000 : ℝ)*(sp1) + (818325121683789/100000000000000 : ℝ)*(sp2) + (199310829988381/50000000000000 : ℝ)*(sp3) + (726973923/20000000000000 : ℝ)*(sp4) + (1512914267/100000000000000 : ℝ)*(sp7) + (39862329302829/10000000000000 : ℝ)*(f.failure) + (204581557254309/25000000000000 : ℝ)*(f.sum) + (87933884454089/200000000000000000000000000000 : ℝ)*base66 + (1796944070854089/400000000000000000000000000000 : ℝ)*base68 + (4872815259254089/400000000000000000000000000000 : ℝ)*base70 + (2620134021654089/400000000000000000000000000000 : ℝ)*base72 + (455513055145911/200000000000000000000000000000 : ℝ)*base73 + (4046721022854089/400000000000000000000000000000 : ℝ)*base76 + (587693457654089/400000000000000000000000000000 : ℝ)*base78 + (113677608054089/400000000000000000000000000000 : ℝ)*base80 + (1078982926454089/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4142673/500000000000000000000 : ℝ)*base89 + (4142673/500000000000000000000 : ℝ)*base91 + (4142673/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131270525874443685365739/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205703389/100000000000000 : ℝ)*(base1) + (18038889/50000000000000 : ℝ)*(base19) + (24987073/6250000000000 : ℝ)*(base23) + (96344529/100000000000000 : ℝ)*(base59) + (642214299455163/100000000000000 : ℝ)*(major0) + (642214299455163/100000000000000 : ℝ)*(major1) + (642214299455163/100000000000000 : ℝ)*(major2) + (195434411/20000000000000 : ℝ)*(sp1) + (53282911/12500000000000 : ℝ)*(sp2) + (1082847851/100000000000000 : ℝ)*(sp3) + (863702110534917/100000000000000 : ℝ)*(sp4) + (431850445790847/50000000000000 : ℝ)*(sp5) + (863701078775071/100000000000000 : ℝ)*(sp6) + (52590670221339/12500000000000 : ℝ)*(sp7) + (420726650321953/100000000000000 : ℝ)*(f.failure) + (863701904831527/100000000000000 : ℝ)*(f.sum) + (774825154278087/200000000000000000000000000000 : ℝ)*base65 + (507287131121913/400000000000000000000000000000 : ℝ)*base68 + (649897987921913/400000000000000000000000000000 : ℝ)*base70 + (1444520466078087/400000000000000000000000000000 : ℝ)*base71 + (271940012878087/200000000000000000000000000000 : ℝ)*base73 + (512806806321913/400000000000000000000000000000 : ℝ)*base76 + (137231051921913/400000000000000000000000000000 : ℝ)*base78 + (938236659678087/400000000000000000000000000000 : ℝ)*base79 + (590818551078087/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8778261/5000000000000000000000 : ℝ)*base89 + (8778261/5000000000000000000000 : ℝ)*base91 + (8778261/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1289_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27257/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1289_s1_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2033380581/10000000000 : ℝ)*x 0 + (5666741179/10000000000 : ℝ)*x 1 + (1005652201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033380581/10000000000 : ℝ)^4249 ≤ (12262095475657/100000000000000 : ℝ)^3225 := by
    have hnat : (2033380581 : ℕ)^4249*100000000000000^3225 ≤ 12262095475657^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033380581 10000000000 12262095475657 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5666741179/10000000000 : ℝ)^4249 ≤ (23658213598983/50000000000000 : ℝ)^3225 := by
    have hnat : (5666741179 : ℕ)^4249*50000000000000^3225 ≤ 23658213598983^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666741179 10000000000 23658213598983 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005652201/2000000000 : ℝ)^4249 ≤ (20210738653041/50000000000000 : ℝ)^3225 := by
    have hnat : (1005652201 : ℕ)^4249*50000000000000^3225 ≤ 20210738653041^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005652201 2000000000 20210738653041 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2033380581/10000000000 : ℝ), (5666741179/10000000000 : ℝ), (1005652201/2000000000 : ℝ)] ![(12262095475657/100000000000000 : ℝ), (23658213598983/50000000000000 : ℝ), (20210738653041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2033380581/10000000000 : ℝ)|^4249 ≤ (12262095475657/100000000000000 : ℝ)^3225
        have hw : |(-2033380581/10000000000 : ℝ)|=(2033380581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5666741179/10000000000 : ℝ)|^4249 ≤ (23658213598983/50000000000000 : ℝ)^3225
        have hw : |(5666741179/10000000000 : ℝ)|=(5666741179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005652201/2000000000 : ℝ)|^4249 ≤ (20210738653041/50000000000000 : ℝ)^3225
        have hw : |(1005652201/2000000000 : ℝ)|=(1005652201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352825547/2500000000 : ℝ)*x 0 + (-2375689547/10000000000 : ℝ)*x 1 + (125706523/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352825547/2500000000 : ℝ)^4249 ≤ (22263320608543/50000000000000 : ℝ)^3225 := by
    have hnat : (1352825547 : ℕ)^4249*50000000000000^3225 ≤ 22263320608543^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352825547 2500000000 22263320608543 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2375689547/10000000000 : ℝ)^4249 ≤ (602075294241/4000000000000 : ℝ)^3225 := by
    have hnat : (2375689547 : ℕ)^4249*4000000000000^3225 ≤ 602075294241^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375689547 10000000000 602075294241 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125706523/250000000 : ℝ)^4249 ≤ (40421476405817/100000000000000 : ℝ)^3225 := by
    have hnat : (125706523 : ℕ)^4249*100000000000000^3225 ≤ 40421476405817^3225*250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125706523 250000000 40421476405817 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352825547/2500000000 : ℝ), (-2375689547/10000000000 : ℝ), (125706523/250000000 : ℝ)] ![(22263320608543/50000000000000 : ℝ), (602075294241/4000000000000 : ℝ), (40421476405817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352825547/2500000000 : ℝ)|^4249 ≤ (22263320608543/50000000000000 : ℝ)^3225
        have hw : |(1352825547/2500000000 : ℝ)|=(1352825547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2375689547/10000000000 : ℝ)|^4249 ≤ (602075294241/4000000000000 : ℝ)^3225
        have hw : |(-2375689547/10000000000 : ℝ)|=(2375689547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125706523/250000000 : ℝ)|^4249 ≤ (40421476405817/100000000000000 : ℝ)^3225
        have hw : |(125706523/250000000 : ℝ)|=(125706523/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411302003/10000000000 : ℝ)*x 0 + (2514130509/5000000000 : ℝ)*x 1 + (-37120151/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411302003/10000000000 : ℝ)^4249 ≤ (1781065568459/4000000000000 : ℝ)^3225 := by
    have hnat : (5411302003 : ℕ)^4249*4000000000000^3225 ≤ 1781065568459^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411302003 10000000000 1781065568459 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2514130509/5000000000 : ℝ)^4249 ≤ (4042147744377/10000000000000 : ℝ)^3225 := by
    have hnat : (2514130509 : ℕ)^4249*10000000000000^3225 ≤ 4042147744377^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514130509 5000000000 4042147744377 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37120151/156250000 : ℝ)^4249 ≤ (7525941666343/50000000000000 : ℝ)^3225 := by
    have hnat : (37120151 : ℕ)^4249*50000000000000^3225 ≤ 7525941666343^3225*156250000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37120151 156250000 7525941666343 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411302003/10000000000 : ℝ), (2514130509/5000000000 : ℝ), (-37120151/156250000 : ℝ)] ![(1781065568459/4000000000000 : ℝ), (4042147744377/10000000000000 : ℝ), (7525941666343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411302003/10000000000 : ℝ)|^4249 ≤ (1781065568459/4000000000000 : ℝ)^3225
        have hw : |(5411302003/10000000000 : ℝ)|=(5411302003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2514130509/5000000000 : ℝ)|^4249 ≤ (4042147744377/10000000000000 : ℝ)^3225
        have hw : |(2514130509/5000000000 : ℝ)|=(2514130509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37120151/156250000 : ℝ)|^4249 ≤ (7525941666343/50000000000000 : ℝ)^3225
        have hw : |(-37120151/156250000 : ℝ)|=(37120151/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301667761/10000000000 : ℝ)*x 0 + (1846831853/5000000000 : ℝ)*x 1 + (5004387471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301667761/10000000000 : ℝ)^4249 ≤ (32908604713697/100000000000000 : ℝ)^3225 := by
    have hnat : (4301667761 : ℕ)^4249*100000000000000^3225 ≤ 32908604713697^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301667761 10000000000 32908604713697 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846831853/5000000000 : ℝ)^4249 ≤ (13461290079921/50000000000000 : ℝ)^3225 := by
    have hnat : (1846831853 : ℕ)^4249*50000000000000^3225 ≤ 13461290079921^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846831853 5000000000 13461290079921 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5004387471/10000000000 : ℝ)^4249 ≤ (2008440755773/5000000000000 : ℝ)^3225 := by
    have hnat : (5004387471 : ℕ)^4249*5000000000000^3225 ≤ 2008440755773^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004387471 10000000000 2008440755773 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301667761/10000000000 : ℝ), (1846831853/5000000000 : ℝ), (5004387471/10000000000 : ℝ)] ![(32908604713697/100000000000000 : ℝ), (13461290079921/50000000000000 : ℝ), (2008440755773/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301667761/10000000000 : ℝ)|^4249 ≤ (32908604713697/100000000000000 : ℝ)^3225
        have hw : |(4301667761/10000000000 : ℝ)|=(4301667761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846831853/5000000000 : ℝ)|^4249 ≤ (13461290079921/50000000000000 : ℝ)^3225
        have hw : |(1846831853/5000000000 : ℝ)|=(1846831853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5004387471/10000000000 : ℝ)|^4249 ≤ (2008440755773/5000000000000 : ℝ)^3225
        have hw : |(5004387471/10000000000 : ℝ)|=(5004387471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2034024137/10000000000 : ℝ)*x 0 + (629575513/1250000000 : ℝ)*x 1 + (1414559967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034024137/10000000000 : ℝ)^4249 ≤ (2453441778499/20000000000000 : ℝ)^3225 := by
    have hnat : (2034024137 : ℕ)^4249*20000000000000^3225 ≤ 2453441778499^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034024137 10000000000 2453441778499 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629575513/1250000000 : ℝ)^4249 ≤ (20254932634227/50000000000000 : ℝ)^3225 := by
    have hnat : (629575513 : ℕ)^4249*50000000000000^3225 ≤ 20254932634227^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629575513 1250000000 20254932634227 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414559967/2500000000 : ℝ)^4249 ≤ (23611462911409/50000000000000 : ℝ)^3225 := by
    have hnat : (1414559967 : ℕ)^4249*50000000000000^3225 ≤ 23611462911409^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414559967 2500000000 23611462911409 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2034024137/10000000000 : ℝ), (629575513/1250000000 : ℝ), (1414559967/2500000000 : ℝ)] ![(2453441778499/20000000000000 : ℝ), (20254932634227/50000000000000 : ℝ), (23611462911409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2034024137/10000000000 : ℝ)|^4249 ≤ (2453441778499/20000000000000 : ℝ)^3225
        have hw : |(-2034024137/10000000000 : ℝ)|=(2034024137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629575513/1250000000 : ℝ)|^4249 ≤ (20254932634227/50000000000000 : ℝ)^3225
        have hw : |(629575513/1250000000 : ℝ)|=(629575513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414559967/2500000000 : ℝ)|^4249 ≤ (23611462911409/50000000000000 : ℝ)^3225
        have hw : |(1414559967/2500000000 : ℝ)|=(1414559967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049277091/2000000000 : ℝ)*x 0 + (-436427589/2500000000 : ℝ)*x 1 + (707280059/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049277091/2000000000 : ℝ)^4249 ≤ (854949325269/2000000000000 : ℝ)^3225 := by
    have hnat : (1049277091 : ℕ)^4249*2000000000000^3225 ≤ 854949325269^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049277091 2000000000 854949325269 2000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436427589/2500000000 : ℝ)^4249 ≤ (10029601263809/100000000000000 : ℝ)^3225 := by
    have hnat : (436427589 : ℕ)^4249*100000000000000^3225 ≤ 10029601263809^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436427589 2500000000 10029601263809 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (707280059/1250000000 : ℝ)^4249 ≤ (11805733116077/25000000000000 : ℝ)^3225 := by
    have hnat : (707280059 : ℕ)^4249*25000000000000^3225 ≤ 11805733116077^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707280059 1250000000 11805733116077 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049277091/2000000000 : ℝ), (-436427589/2500000000 : ℝ), (707280059/1250000000 : ℝ)] ![(854949325269/2000000000000 : ℝ), (10029601263809/100000000000000 : ℝ), (11805733116077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049277091/2000000000 : ℝ)|^4249 ≤ (854949325269/2000000000000 : ℝ)^3225
        have hw : |(1049277091/2000000000 : ℝ)|=(1049277091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436427589/2500000000 : ℝ)|^4249 ≤ (10029601263809/100000000000000 : ℝ)^3225
        have hw : |(-436427589/2500000000 : ℝ)|=(436427589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(707280059/1250000000 : ℝ)|^4249 ≤ (11805733116077/25000000000000 : ℝ)^3225
        have hw : |(707280059/1250000000 : ℝ)|=(707280059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5246385361/10000000000 : ℝ)*x 0 + (176820003/312500000 : ℝ)*x 1 + (-1745711033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246385361/10000000000 : ℝ)^4249 ≤ (10686866313587/25000000000000 : ℝ)^3225 := by
    have hnat : (5246385361 : ℕ)^4249*25000000000000^3225 ≤ 10686866313587^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246385361 10000000000 10686866313587 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176820003/312500000 : ℝ)^4249 ≤ (4722292832987/10000000000000 : ℝ)^3225 := by
    have hnat : (176820003 : ℕ)^4249*10000000000000^3225 ≤ 4722292832987^3225*312500000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176820003 312500000 4722292832987 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1745711033/10000000000 : ℝ)^4249 ≤ (1253700798547/12500000000000 : ℝ)^3225 := by
    have hnat : (1745711033 : ℕ)^4249*12500000000000^3225 ≤ 1253700798547^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745711033 10000000000 1253700798547 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246385361/10000000000 : ℝ), (176820003/312500000 : ℝ), (-1745711033/10000000000 : ℝ)] ![(10686866313587/25000000000000 : ℝ), (4722292832987/10000000000000 : ℝ), (1253700798547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246385361/10000000000 : ℝ)|^4249 ≤ (10686866313587/25000000000000 : ℝ)^3225
        have hw : |(5246385361/10000000000 : ℝ)|=(5246385361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176820003/312500000 : ℝ)|^4249 ≤ (4722292832987/10000000000000 : ℝ)^3225
        have hw : |(176820003/312500000 : ℝ)|=(176820003/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1745711033/10000000000 : ℝ)|^4249 ≤ (1253700798547/12500000000000 : ℝ)^3225
        have hw : |(-1745711033/10000000000 : ℝ)|=(1745711033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s1_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302988247/10000000000 : ℝ)*x 0 + (2493630227/5000000000 : ℝ)*x 1 + (1855557587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302988247/10000000000 : ℝ)^4249 ≤ (8230478728421/25000000000000 : ℝ)^3225 := by
    have hnat : (4302988247 : ℕ)^4249*25000000000000^3225 ≤ 8230478728421^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302988247 10000000000 8230478728421 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493630227/5000000000 : ℝ)^4249 ≤ (39987789256597/100000000000000 : ℝ)^3225 := by
    have hnat : (2493630227 : ℕ)^4249*100000000000000^3225 ≤ 39987789256597^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493630227 5000000000 39987789256597 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855557587/5000000000 : ℝ)^4249 ≤ (27090295811427/100000000000000 : ℝ)^3225 := by
    have hnat : (1855557587 : ℕ)^4249*100000000000000^3225 ≤ 27090295811427^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855557587 5000000000 27090295811427 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302988247/10000000000 : ℝ), (2493630227/5000000000 : ℝ), (1855557587/5000000000 : ℝ)] ![(8230478728421/25000000000000 : ℝ), (39987789256597/100000000000000 : ℝ), (27090295811427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302988247/10000000000 : ℝ)|^4249 ≤ (8230478728421/25000000000000 : ℝ)^3225
        have hw : |(4302988247/10000000000 : ℝ)|=(4302988247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2493630227/5000000000 : ℝ)|^4249 ≤ (39987789256597/100000000000000 : ℝ)^3225
        have hw : |(2493630227/5000000000 : ℝ)|=(2493630227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855557587/5000000000 : ℝ)|^4249 ≤ (27090295811427/100000000000000 : ℝ)^3225
        have hw : |(1855557587/5000000000 : ℝ)|=(1855557587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9937/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1009/100000 : ℝ) ^ (531/128 : ℝ) ≤ (261961376783/50000000000000000000 : ℝ) := by
    have hpowers : (1009/100000 : ℝ)^531 ≤ (261961376783/50000000000000000000 : ℝ)^128 := by
      have hnat : (1009 : ℕ)^531*50000000000000000000^128 ≤ 261961376783^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009 100000 261961376783 50000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1009/100000 : ℝ)) (X := (261961376783/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (27257/100000 : ℝ) ^ (531/128 : ℝ) ≤ (455109593522435351/100000000000000000000 : ℝ) := by
    have hpowers : (27257/100000 : ℝ)^531 ≤ (455109593522435351/100000000000000000000 : ℝ)^128 := by
      have hnat : (27257 : ℕ)^531*100000000000000000000^128 ≤ 455109593522435351^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27257 100000 455109593522435351 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27257/100000 : ℝ)) (X := (455109593522435351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000261961376783/25000000000000000000 : ℝ) ≤ (25000000063147/25000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (25000000261961376783/25000000000000000000 : ℝ)^128 ≤ (25000000063147/25000000000000 : ℝ)^531 := by
      have hnat : (25000000261961376783 : ℕ)^128*25000000000000^531 ≤ 25000000063147^531*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000261961376783 25000000000000000000 25000000063147 25000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25000000063147/25000000000000 : ℝ)) (X := (25000000261961376783/25000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100455110117445188917/100000000000000000000 : ℝ) ≤ (10010951743265753/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (100455110117445188917/100000000000000000000 : ℝ)^128 ≤ (10010951743265753/10000000000000000 : ℝ)^531 := by
      have hnat : (100455110117445188917 : ℕ)^128*10000000000000000^531 ≤ 10010951743265753^531*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100455110117445188917 100000000000000000000 10010951743265753 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010951743265753/10000000000000000 : ℝ)) (X := (100455110117445188917/100000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50455109593522435351/50000000000000000000 : ℝ) ≤ (5010951730636353/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50455109593522435351/50000000000000000000 : ℝ)^128 ≤ (5010951730636353/5000000000000000 : ℝ)^531 := by
      have hnat : (50455109593522435351 : ℕ)^128*5000000000000000^531 ≤ 5010951730636353^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50455109593522435351 50000000000000000000 5010951730636353 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010951730636353/5000000000000000 : ℝ)) (X := (50455109593522435351/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(261961376783/50000000000000000000 : ℝ) ≤ ((131228950048027475623/131240000000000000000 : ℝ)+2*(10951718006953/2624800000000000 : ℝ)*(1009/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (131228950048027475623/131240000000000000000 : ℝ)+2*(10951718006953/2624800000000000 : ℝ)*(1009/100000 : ℝ)=(25000000063147/25000000000000 : ℝ) by norm_num, show 1+2*(261961376783/50000000000000000000 : ℝ)=(25000000261961376783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(455109593522435351/100000000000000000000 : ℝ)+(261961376783/50000000000000000000 : ℝ) ≤ ((131228950048027475623/131240000000000000000 : ℝ)+(10951718006953/2624800000000000 : ℝ)*((27257/100000 : ℝ)+(1009/100000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (131228950048027475623/131240000000000000000 : ℝ)+(10951718006953/2624800000000000 : ℝ)*((27257/100000 : ℝ)+(1009/100000 : ℝ))=(10010951743265753/10000000000000000 : ℝ) by norm_num, show 1+(455109593522435351/100000000000000000000 : ℝ)+(261961376783/50000000000000000000 : ℝ)=(100455110117445188917/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(455109593522435351/100000000000000000000 : ℝ) ≤ ((131228950048027475623/131240000000000000000 : ℝ)+2*(10951718006953/2624800000000000 : ℝ)*(27257/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (131228950048027475623/131240000000000000000 : ℝ)+2*(10951718006953/2624800000000000 : ℝ)*(27257/100000 : ℝ)=(5010951730636353/5000000000000000 : ℝ) by norm_num, show 1+2*(455109593522435351/100000000000000000000 : ℝ)=(50455109593522435351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (131228950048027475623/131240000000000000000 : ℝ)*(X 1 0+X 2 0)+(10951718006953/2624800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (1009/100000 : ℝ)) (hi := (27257/100000 : ℝ)) (c := (131228950048027475623/131240000000000000000 : ℝ)) (alpha := (10951718006953/2624800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (131228950048027475623/131240000000000000000 : ℝ)*(X 0 1+X 2 1)+(10951718006953/2624800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (1009/100000 : ℝ)) (hi := (27257/100000 : ℝ)) (c := (131228950048027475623/131240000000000000000 : ℝ)) (alpha := (10951718006953/2624800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (131228950048027475623/131240000000000000000 : ℝ)*(X 0 2+X 1 2)+(10951718006953/2624800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (1009/100000 : ℝ)) (hi := (27257/100000 : ℝ)) (c := (131228950048027475623/131240000000000000000 : ℝ)) (alpha := (10951718006953/2624800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2033380581/10000000000 : ℝ)*X 0 0+(5666741179/10000000000 : ℝ)*X 0 1+(1005652201/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1352825547/2500000000 : ℝ)*X 1 0+(-2375689547/10000000000 : ℝ)*X 1 1+(125706523/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5411302003/10000000000 : ℝ)*X 2 0+(2514130509/5000000000 : ℝ)*X 2 1+(-37120151/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301667761/10000000000 : ℝ)*X 0 0+(1846831853/5000000000 : ℝ)*X 0 1+(5004387471/10000000000 : ℝ)*X 0 2+(4301667761/10000000000 : ℝ)*X 1 0+(1846831853/5000000000 : ℝ)*X 1 1+(5004387471/10000000000 : ℝ)*X 1 2+(4301667761/10000000000 : ℝ)*X 2 0+(1846831853/5000000000 : ℝ)*X 2 1+(5004387471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2034024137/10000000000 : ℝ)*X 0 0+(629575513/1250000000 : ℝ)*X 0 1+(1414559967/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049277091/2000000000 : ℝ)*X 1 0+(-436427589/2500000000 : ℝ)*X 1 1+(707280059/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5246385361/10000000000 : ℝ)*X 2 0+(176820003/312500000 : ℝ)*X 2 1+(-1745711033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302988247/10000000000 : ℝ)*X 0 0+(2493630227/5000000000 : ℝ)*X 0 1+(1855557587/5000000000 : ℝ)*X 0 2+(4302988247/10000000000 : ℝ)*X 1 0+(2493630227/5000000000 : ℝ)*X 1 1+(1855557587/5000000000 : ℝ)*X 1 2+(4302988247/10000000000 : ℝ)*X 2 0+(2493630227/5000000000 : ℝ)*X 2 1+(1855557587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15221187893006722560645121959/3281000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45900903/100000000000000 : ℝ)*(base1) + (228490733/25000000000000 : ℝ)*(base19) + (430208589/50000000000000 : ℝ)*(base23) + (61586243/50000000000000 : ℝ)*(upper3) + (64997549/100000000000000 : ℝ)*(upper5) + (1164585693779389/100000000000000 : ℝ)*(major0) + (1164585693779389/100000000000000 : ℝ)*(major1) + (1164585693779389/100000000000000 : ℝ)*(major2) + (391556159074769/25000000000000 : ℝ)*(sp0) + (156622835647981/10000000000000 : ℝ)*(sp1) + (391557102506391/25000000000000 : ℝ)*(sp2) + (381469726554963/50000000000000 : ℝ)*(sp3) + (585005571/12500000000000 : ℝ)*(sp4) + (2463465479/100000000000000 : ℝ)*(sp7) + (762941962476309/100000000000000 : ℝ)*(f.failure) + (1566229270442741/100000000000000 : ℝ)*(f.sum) + (201755732948237/131240000000000000000000000000 : ℝ)*base65 + (44785234387171184347/13124000000000000000000000000000000 : ℝ)*base67 + (106469176201419184347/13124000000000000000000000000000000 : ℝ)*base69 + (20038956210927184347/13124000000000000000000000000000000 : ℝ)*base71 + (86825305063237/131240000000000000000000000000 : ℝ)*base73 + (10017530010715184347/13124000000000000000000000000000000 : ℝ)*base75 + (21041886883839184347/13124000000000000000000000000000000 : ℝ)*base77 + (2777539003852815653/13124000000000000000000000000000000 : ℝ)*base80 + (393956060816677/131240000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17121433/5000000000000000000000 : ℝ)*base89 + (17121433/5000000000000000000000 : ℝ)*base91 + (17121433/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1804658520338856906663385221/386000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (807781849/100000000000000 : ℝ)*(base19) + (391314777/50000000000000 : ℝ)*(base23) + (69789/312500000000 : ℝ)*(upper2) + (1473571/1000000000000 : ℝ)*(upper3) + (49702719/50000000000000 : ℝ)*(upper5) + (1196134136443647/100000000000000 : ℝ)*(major0) + (1196134136443647/100000000000000 : ℝ)*(major1) + (1196134136443647/100000000000000 : ℝ)*(major2) + (954079561/20000000000000 : ℝ)*(sp1) + (3532989603/100000000000000 : ℝ)*(sp2) + (160865817720267/10000000000000 : ℝ)*(sp4) + (201081574877877/12500000000000 : ℝ)*(sp5) + (201081732697939/12500000000000 : ℝ)*(sp6) + (391804969920957/50000000000000 : ℝ)*(sp7) + (391804969920957/50000000000000 : ℝ)*(f.failure) + (160865817720267/10000000000000 : ℝ)*(f.sum) + (281764840517271/131240000000000000000000000000 : ℝ)*base65 + (30557292624778732919/13124000000000000000000000000000000 : ℝ)*base68 + (67867143324181267081/13124000000000000000000000000000000 : ℝ)*base69 + (25877380649213267081/13124000000000000000000000000000000 : ℝ)*base71 + (80579869519409/131240000000000000000000000000 : ℝ)*base74 + (16335608509226732919/13124000000000000000000000000000000 : ℝ)*base76 + (94800520561609267081/13124000000000000000000000000000000 : ℝ)*base77 + (68485134556797267081/13124000000000000000000000000000000 : ℝ)*base79 + (211995979270071/131240000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7770591/2500000000000000000000 : ℝ)*base90 + (7770591/2500000000000000000000 : ℝ)*base92 + (7770591/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1289_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9937/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1289_s2_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1039178569/5000000000 : ℝ)*x 0 + (1373792777/2500000000 : ℝ)*x 1 + (10099821/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039178569/5000000000 : ℝ)^4249 ≤ (12620690343787/100000000000000 : ℝ)^3225 := by
    have hnat : (1039178569 : ℕ)^4249*100000000000000^3225 ≤ 12620690343787^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039178569 5000000000 12620690343787 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373792777/2500000000 : ℝ)^4249 ≤ (22719052887581/50000000000000 : ℝ)^3225 := by
    have hnat : (1373792777 : ℕ)^4249*50000000000000^3225 ≤ 22719052887581^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373792777 2500000000 22719052887581 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10099821/19531250 : ℝ)^4249 ≤ (2097060192973/5000000000000 : ℝ)^3225 := by
    have hnat : (10099821 : ℕ)^4249*5000000000000^3225 ≤ 2097060192973^3225*19531250^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10099821 19531250 2097060192973 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1039178569/5000000000 : ℝ), (1373792777/2500000000 : ℝ), (10099821/19531250 : ℝ)] ![(12620690343787/100000000000000 : ℝ), (22719052887581/50000000000000 : ℝ), (2097060192973/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1039178569/5000000000 : ℝ)|^4249 ≤ (12620690343787/100000000000000 : ℝ)^3225
        have hw : |(-1039178569/5000000000 : ℝ)|=(1039178569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373792777/2500000000 : ℝ)|^4249 ≤ (22719052887581/50000000000000 : ℝ)^3225
        have hw : |(1373792777/2500000000 : ℝ)|=(1373792777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10099821/19531250 : ℝ)|^4249 ≤ (2097060192973/5000000000000 : ℝ)^3225
        have hw : |(10099821/19531250 : ℝ)|=(10099821/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536980749/1000000000 : ℝ)*x 0 + (-2246323949/10000000000 : ℝ)*x 1 + (5171108681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536980749/1000000000 : ℝ)^4249 ≤ (22038669887121/50000000000000 : ℝ)^3225 := by
    have hnat : (536980749 : ℕ)^4249*50000000000000^3225 ≤ 22038669887121^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536980749 1000000000 22038669887121 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246323949/10000000000 : ℝ)^4249 ≤ (13981452833633/100000000000000 : ℝ)^3225 := by
    have hnat : (2246323949 : ℕ)^4249*100000000000000^3225 ≤ 13981452833633^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246323949 10000000000 13981452833633 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171108681/10000000000 : ℝ)^4249 ≤ (41941207375147/100000000000000 : ℝ)^3225 := by
    have hnat : (5171108681 : ℕ)^4249*100000000000000^3225 ≤ 41941207375147^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171108681 10000000000 41941207375147 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536980749/1000000000 : ℝ), (-2246323949/10000000000 : ℝ), (5171108681/10000000000 : ℝ)] ![(22038669887121/50000000000000 : ℝ), (13981452833633/100000000000000 : ℝ), (41941207375147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536980749/1000000000 : ℝ)|^4249 ≤ (22038669887121/50000000000000 : ℝ)^3225
        have hw : |(536980749/1000000000 : ℝ)|=(536980749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246323949/10000000000 : ℝ)|^4249 ≤ (13981452833633/100000000000000 : ℝ)^3225
        have hw : |(-2246323949/10000000000 : ℝ)|=(2246323949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171108681/10000000000 : ℝ)|^4249 ≤ (41941207375147/100000000000000 : ℝ)^3225
        have hw : |(5171108681/10000000000 : ℝ)|=(5171108681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369807651/10000000000 : ℝ)*x 0 + (41368867/80000000 : ℝ)*x 1 + (-449264827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369807651/10000000000 : ℝ)^4249 ≤ (22038670757703/50000000000000 : ℝ)^3225 := by
    have hnat : (5369807651 : ℕ)^4249*50000000000000^3225 ≤ 22038670757703^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369807651 10000000000 22038670757703 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41368867/80000000 : ℝ)^4249 ≤ (41941204105237/100000000000000 : ℝ)^3225 := by
    have hnat : (41368867 : ℕ)^4249*100000000000000^3225 ≤ 41941204105237^3225*80000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41368867 80000000 41941204105237 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449264827/2000000000 : ℝ)^4249 ≤ (6990727179457/50000000000000 : ℝ)^3225 := by
    have hnat : (449264827 : ℕ)^4249*50000000000000^3225 ≤ 6990727179457^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449264827 2000000000 6990727179457 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369807651/10000000000 : ℝ), (41368867/80000000 : ℝ), (-449264827/2000000000 : ℝ)] ![(22038670757703/50000000000000 : ℝ), (41941204105237/100000000000000 : ℝ), (6990727179457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369807651/10000000000 : ℝ)|^4249 ≤ (22038670757703/50000000000000 : ℝ)^3225
        have hw : |(5369807651/10000000000 : ℝ)|=(5369807651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41368867/80000000 : ℝ)|^4249 ≤ (41941204105237/100000000000000 : ℝ)^3225
        have hw : |(41368867/80000000 : ℝ)|=(41368867/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449264827/2000000000 : ℝ)|^4249 ≤ (6990727179457/50000000000000 : ℝ)^3225
        have hw : |(-449264827/2000000000 : ℝ)|=(449264827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270807583/625000000 : ℝ)*x 0 + (501558621/1250000000 : ℝ)*x 1 + (4677738513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270807583/625000000 : ℝ)^4249 ≤ (6644796200189/20000000000000 : ℝ)^3225 := by
    have hnat : (270807583 : ℕ)^4249*20000000000000^3225 ≤ 6644796200189^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270807583 625000000 6644796200189 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501558621/1250000000 : ℝ)^4249 ≤ (15012645020339/50000000000000 : ℝ)^3225 := by
    have hnat : (501558621 : ℕ)^4249*50000000000000^3225 ≤ 15012645020339^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501558621 1250000000 15012645020339 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4677738513/10000000000 : ℝ)^4249 ≤ (36750728935807/100000000000000 : ℝ)^3225 := by
    have hnat : (4677738513 : ℕ)^4249*100000000000000^3225 ≤ 36750728935807^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677738513 10000000000 36750728935807 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270807583/625000000 : ℝ), (501558621/1250000000 : ℝ), (4677738513/10000000000 : ℝ)] ![(6644796200189/20000000000000 : ℝ), (15012645020339/50000000000000 : ℝ), (36750728935807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270807583/625000000 : ℝ)|^4249 ≤ (6644796200189/20000000000000 : ℝ)^3225
        have hw : |(270807583/625000000 : ℝ)|=(270807583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501558621/1250000000 : ℝ)|^4249 ≤ (15012645020339/50000000000000 : ℝ)^3225
        have hw : |(501558621/1250000000 : ℝ)|=(501558621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4677738513/10000000000 : ℝ)|^4249 ≤ (36750728935807/100000000000000 : ℝ)^3225
        have hw : |(4677738513/10000000000 : ℝ)|=(4677738513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2078440469/10000000000 : ℝ)*x 0 + (5173267107/10000000000 : ℝ)*x 1 + (5492992143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078440469/10000000000 : ℝ)^4249 ≤ (631067852101/5000000000000 : ℝ)^3225 := by
    have hnat : (2078440469 : ℕ)^4249*5000000000000^3225 ≤ 631067852101^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078440469 10000000000 631067852101 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173267107/10000000000 : ℝ)^4249 ≤ (5245534224519/12500000000000 : ℝ)^3225 := by
    have hnat : (5173267107 : ℕ)^4249*12500000000000^3225 ≤ 5245534224519^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173267107 10000000000 5245534224519 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492992143/10000000000 : ℝ)^4249 ≤ (11353592288183/25000000000000 : ℝ)^3225 := by
    have hnat : (5492992143 : ℕ)^4249*25000000000000^3225 ≤ 11353592288183^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492992143 10000000000 11353592288183 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2078440469/10000000000 : ℝ), (5173267107/10000000000 : ℝ), (5492992143/10000000000 : ℝ)] ![(631067852101/5000000000000 : ℝ), (5245534224519/12500000000000 : ℝ), (11353592288183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2078440469/10000000000 : ℝ)|^4249 ≤ (631067852101/5000000000000 : ℝ)^3225
        have hw : |(-2078440469/10000000000 : ℝ)|=(2078440469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173267107/10000000000 : ℝ)|^4249 ≤ (5245534224519/12500000000000 : ℝ)^3225
        have hw : |(5173267107/10000000000 : ℝ)|=(5173267107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492992143/10000000000 : ℝ)|^4249 ≤ (11353592288183/25000000000000 : ℝ)^3225
        have hw : |(5492992143/10000000000 : ℝ)|=(5492992143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321694911/2500000000 : ℝ)*x 0 + (-1924439847/10000000000 : ℝ)*x 1 + (2746496143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321694911/2500000000 : ℝ)^4249 ≤ (21590816077689/50000000000000 : ℝ)^3225 := by
    have hnat : (1321694911 : ℕ)^4249*50000000000000^3225 ≤ 21590816077689^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321694911 2500000000 21590816077689 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924439847/10000000000 : ℝ)^4249 ≤ (712749819791/6250000000000 : ℝ)^3225 := by
    have hnat : (1924439847 : ℕ)^4249*6250000000000^3225 ≤ 712749819791^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924439847 10000000000 712749819791 6250000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746496143/5000000000 : ℝ)^4249 ≤ (5676796338801/12500000000000 : ℝ)^3225 := by
    have hnat : (2746496143 : ℕ)^4249*12500000000000^3225 ≤ 5676796338801^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746496143 5000000000 5676796338801 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321694911/2500000000 : ℝ), (-1924439847/10000000000 : ℝ), (2746496143/5000000000 : ℝ)] ![(21590816077689/50000000000000 : ℝ), (712749819791/6250000000000 : ℝ), (5676796338801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321694911/2500000000 : ℝ)|^4249 ≤ (21590816077689/50000000000000 : ℝ)^3225
        have hw : |(1321694911/2500000000 : ℝ)|=(1321694911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924439847/10000000000 : ℝ)|^4249 ≤ (712749819791/6250000000000 : ℝ)^3225
        have hw : |(-1924439847/10000000000 : ℝ)|=(1924439847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746496143/5000000000 : ℝ)|^4249 ≤ (5676796338801/12500000000000 : ℝ)^3225
        have hw : |(2746496143/5000000000 : ℝ)|=(2746496143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660847477/1250000000 : ℝ)*x 0 + (5492992151/10000000000 : ℝ)*x 1 + (-1924439799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660847477/1250000000 : ℝ)^4249 ≤ (21590817003161/50000000000000 : ℝ)^3225 := by
    have hnat : (660847477 : ℕ)^4249*50000000000000^3225 ≤ 21590817003161^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660847477 1250000000 21590817003161 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492992151/10000000000 : ℝ)^4249 ≤ (22707184619937/50000000000000 : ℝ)^3225 := by
    have hnat : (5492992151 : ℕ)^4249*50000000000000^3225 ≤ 22707184619937^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492992151 10000000000 22707184619937 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924439799/10000000000 : ℝ)^4249 ≤ (5701998370949/50000000000000 : ℝ)^3225 := by
    have hnat : (1924439799 : ℕ)^4249*50000000000000^3225 ≤ 5701998370949^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924439799 10000000000 5701998370949 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660847477/1250000000 : ℝ), (5492992151/10000000000 : ℝ), (-1924439799/10000000000 : ℝ)] ![(21590817003161/50000000000000 : ℝ), (22707184619937/50000000000000 : ℝ), (5701998370949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660847477/1250000000 : ℝ)|^4249 ≤ (21590817003161/50000000000000 : ℝ)^3225
        have hw : |(660847477/1250000000 : ℝ)|=(660847477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492992151/10000000000 : ℝ)|^4249 ≤ (22707184619937/50000000000000 : ℝ)^3225
        have hw : |(5492992151/10000000000 : ℝ)|=(5492992151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1924439799/10000000000 : ℝ)|^4249 ≤ (5701998370949/50000000000000 : ℝ)^3225
        have hw : |(-1924439799/10000000000 : ℝ)|=(1924439799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s2_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083273047/2500000000 : ℝ)*x 0 + (2336652679/5000000000 : ℝ)*x 1 + (2008473417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083273047/2500000000 : ℝ)^4249 ≤ (16612853560501/50000000000000 : ℝ)^3225 := by
    have hnat : (1083273047 : ℕ)^4249*50000000000000^3225 ≤ 16612853560501^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083273047 2500000000 16612853560501 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336652679/5000000000 : ℝ)^4249 ≤ (36704847755419/100000000000000 : ℝ)^3225 := by
    have hnat : (2336652679 : ℕ)^4249*100000000000000^3225 ≤ 36704847755419^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336652679 5000000000 36704847755419 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008473417/5000000000 : ℝ)^4249 ≤ (150347225539/500000000000 : ℝ)^3225 := by
    have hnat : (2008473417 : ℕ)^4249*500000000000^3225 ≤ 150347225539^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008473417 5000000000 150347225539 500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083273047/2500000000 : ℝ), (2336652679/5000000000 : ℝ), (2008473417/5000000000 : ℝ)] ![(16612853560501/50000000000000 : ℝ), (36704847755419/100000000000000 : ℝ), (150347225539/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083273047/2500000000 : ℝ)|^4249 ≤ (16612853560501/50000000000000 : ℝ)^3225
        have hw : |(1083273047/2500000000 : ℝ)|=(1083273047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2336652679/5000000000 : ℝ)|^4249 ≤ (36704847755419/100000000000000 : ℝ)^3225
        have hw : |(2336652679/5000000000 : ℝ)|=(2336652679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008473417/5000000000 : ℝ)|^4249 ≤ (150347225539/500000000000 : ℝ)^3225
        have hw : |(2008473417/5000000000 : ℝ)|=(2008473417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9483/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16331/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9937/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9937/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9937/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9937/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9937/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9937/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6379/100000 : ℝ) ^ (531/128 : ℝ) ≤ (275125523330109/25000000000000000000 : ℝ) := by
    have hpowers : (6379/100000 : ℝ)^531 ≤ (275125523330109/25000000000000000000 : ℝ)^128 := by
      have hnat : (6379 : ℕ)^531*25000000000000000000^128 ≤ 275125523330109^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6379 100000 275125523330109 25000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6379/100000 : ℝ)) (X := (275125523330109/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (9937/50000 : ℝ) ^ (531/128 : ℝ) ≤ (122738373551566047/100000000000000000000 : ℝ) := by
    have hpowers : (9937/50000 : ℝ)^531 ≤ (122738373551566047/100000000000000000000 : ℝ)^128 := by
      have hnat : (9937 : ℕ)^531*100000000000000000000^128 ≤ 122738373551566047^128*50000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9937 50000 122738373551566047 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9937/50000 : ℝ)) (X := (122738373551566047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500275125523330109/12500000000000000000 : ℝ) ≤ (5000026527889159/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (12500275125523330109/12500000000000000000 : ℝ)^128 ≤ (5000026527889159/5000000000000000 : ℝ)^531 := by
      have hnat : (12500275125523330109 : ℕ)^128*5000000000000000^531 ≤ 5000026527889159^531*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500275125523330109 12500000000000000000 5000026527889159 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000026527889159/5000000000000000 : ℝ)) (X := (12500275125523330109/12500000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100123838875644886483/100000000000000000000 : ℝ) ≤ (5001491895703833/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (100123838875644886483/100000000000000000000 : ℝ)^128 ≤ (5001491895703833/5000000000000000 : ℝ)^531 := by
      have hnat : (100123838875644886483 : ℕ)^128*5000000000000000^531 ≤ 5001491895703833^531*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100123838875644886483 100000000000000000000 5001491895703833 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001491895703833/5000000000000000 : ℝ)) (X := (100123838875644886483/100000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50122738373551566047/50000000000000000000 : ℝ) ≤ (5002957263518507/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50122738373551566047/50000000000000000000 : ℝ)^128 ≤ (5002957263518507/5000000000000000 : ℝ)^531 := by
      have hnat : (50122738373551566047 : ℕ)^128*5000000000000000^531 ≤ 5002957263518507^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50122738373551566047 50000000000000000000 5002957263518507 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002957263518507/5000000000000000 : ℝ)) (X := (50122738373551566047/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(275125523330109/25000000000000000000 : ℝ) ≤ ((67456662831284589813/67475000000000000000 : ℝ)+2*(732683907337/337375000000000 : ℝ)*(6379/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (67456662831284589813/67475000000000000000 : ℝ)+2*(732683907337/337375000000000 : ℝ)*(6379/100000 : ℝ)=(5000026527889159/5000000000000000 : ℝ) by norm_num, show 1+2*(275125523330109/25000000000000000000 : ℝ)=(12500275125523330109/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(122738373551566047/100000000000000000000 : ℝ)+(275125523330109/25000000000000000000 : ℝ) ≤ ((67456662831284589813/67475000000000000000 : ℝ)+(732683907337/337375000000000 : ℝ)*((9937/50000 : ℝ)+(6379/100000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (67456662831284589813/67475000000000000000 : ℝ)+(732683907337/337375000000000 : ℝ)*((9937/50000 : ℝ)+(6379/100000 : ℝ))=(5001491895703833/5000000000000000 : ℝ) by norm_num, show 1+(122738373551566047/100000000000000000000 : ℝ)+(275125523330109/25000000000000000000 : ℝ)=(100123838875644886483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(122738373551566047/100000000000000000000 : ℝ) ≤ ((67456662831284589813/67475000000000000000 : ℝ)+2*(732683907337/337375000000000 : ℝ)*(9937/50000 : ℝ))^(531/128 : ℝ) := by
    rw [show (67456662831284589813/67475000000000000000 : ℝ)+2*(732683907337/337375000000000 : ℝ)*(9937/50000 : ℝ)=(5002957263518507/5000000000000000 : ℝ) by norm_num, show 1+2*(122738373551566047/100000000000000000000 : ℝ)=(50122738373551566047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67456662831284589813/67475000000000000000 : ℝ)*(X 1 0+X 2 0)+(732683907337/337375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (6379/100000 : ℝ)) (hi := (9937/50000 : ℝ)) (c := (67456662831284589813/67475000000000000000 : ℝ)) (alpha := (732683907337/337375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67456662831284589813/67475000000000000000 : ℝ)*(X 0 1+X 2 1)+(732683907337/337375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (6379/100000 : ℝ)) (hi := (9937/50000 : ℝ)) (c := (67456662831284589813/67475000000000000000 : ℝ)) (alpha := (732683907337/337375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67456662831284589813/67475000000000000000 : ℝ)*(X 0 2+X 1 2)+(732683907337/337375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (6379/100000 : ℝ)) (hi := (9937/50000 : ℝ)) (c := (67456662831284589813/67475000000000000000 : ℝ)) (alpha := (732683907337/337375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1039178569/5000000000 : ℝ)*X 0 0+(1373792777/2500000000 : ℝ)*X 0 1+(10099821/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((536980749/1000000000 : ℝ)*X 1 0+(-2246323949/10000000000 : ℝ)*X 1 1+(5171108681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369807651/10000000000 : ℝ)*X 2 0+(41368867/80000000 : ℝ)*X 2 1+(-449264827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270807583/625000000 : ℝ)*X 0 0+(501558621/1250000000 : ℝ)*X 0 1+(4677738513/10000000000 : ℝ)*X 0 2+(270807583/625000000 : ℝ)*X 1 0+(501558621/1250000000 : ℝ)*X 1 1+(4677738513/10000000000 : ℝ)*X 1 2+(270807583/625000000 : ℝ)*X 2 0+(501558621/1250000000 : ℝ)*X 2 1+(4677738513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2078440469/10000000000 : ℝ)*X 0 0+(5173267107/10000000000 : ℝ)*X 0 1+(5492992143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321694911/2500000000 : ℝ)*X 1 0+(-1924439847/10000000000 : ℝ)*X 1 1+(2746496143/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660847477/1250000000 : ℝ)*X 2 0+(5492992151/10000000000 : ℝ)*X 2 1+(-1924439799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083273047/2500000000 : ℝ)*X 0 0+(2336652679/5000000000 : ℝ)*X 0 1+(2008473417/5000000000 : ℝ)*X 0 2+(1083273047/2500000000 : ℝ)*X 1 0+(2336652679/5000000000 : ℝ)*X 1 1+(2008473417/5000000000 : ℝ)*X 1 2+(1083273047/2500000000 : ℝ)*X 2 0+(2336652679/5000000000 : ℝ)*X 2 1+(2008473417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34960870514024463843513/33737500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1096726293/100000000000000 : ℝ)*(base19) + (1056741931/100000000000000 : ℝ)*(base23) + (71152803/100000000000000 : ℝ)*(lower2) + (107389619/25000000000000 : ℝ)*(upper3) + (210435939/100000000000000 : ℝ)*(upper5) + (2294505822450643/100000000000000 : ℝ)*(major0) + (2294505822450643/100000000000000 : ℝ)*(major1) + (2294505822450643/100000000000000 : ℝ)*(major2) + (1542915743130133/50000000000000 : ℝ)*(sp0) + (771459162877/25000000000 : ℝ)*(sp1) + (3085836691492363/100000000000000 : ℝ)*(sp2) + (75158037900971/5000000000000 : ℝ)*(sp3) + (6261974027/100000000000000 : ℝ)*(sp4) + (2620821103/20000000000000 : ℝ)*(sp7) + (751586931062467/50000000000000 : ℝ)*(f.failure) + (1542918874117147/50000000000000 : ℝ)*(f.sum) + (275442703606511/67475000000000000000000000000 : ℝ)*base66 + (10255920774651200241/6747500000000000000000000000000000 : ℝ)*base68 + (15379910980361200241/6747500000000000000000000000000000 : ℝ)*base70 + (32274961487681299759/6747500000000000000000000000000000 : ℝ)*base71 + (277842862552993/33737500000000000000000000000 : ℝ)*base74 + (12949221438656299759/6747500000000000000000000000000000 : ℝ)*base75 + (30143120001786200241/6747500000000000000000000000000000 : ℝ)*base78 + (2572321585118799759/6747500000000000000000000000000000 : ℝ)*base79 + (128495767092611/67475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (19314721/2500000000000000000000 : ℝ)*base90 + (19314721/2500000000000000000000 : ℝ)*base92 + (19314721/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2782235802268818535045166661/421718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (626147783/50000000000000 : ℝ)*(base19) + (391858201/25000000000000 : ℝ)*(base23) + (100032523/50000000000000 : ℝ)*(upper3) + (78583149/100000000000000 : ℝ)*(lower4) + (40795899/50000000000000 : ℝ)*(upper5) + (581405444601149/25000000000000 : ℝ)*(major0) + (581405444601149/25000000000000 : ℝ)*(major1) + (581405444601149/25000000000000 : ℝ)*(major2) + (12708675397/100000000000000 : ℝ)*(sp1) + (16831006929/100000000000000 : ℝ)*(sp2) + (1563842413786783/50000000000000 : ℝ)*(sp4) + (1563835433301301/50000000000000 : ℝ)*(sp5) + (3127666429133833/100000000000000 : ℝ)*(sp6) + (380889627330799/25000000000000 : ℝ)*(sp7) + (380889627330799/25000000000000 : ℝ)*(f.failure) + (1563842413786783/50000000000000 : ℝ)*(f.sum) + (16871463924129/33737500000000000000000000000 : ℝ)*base65 + (7357226320397654863/1686875000000000000000000000000000 : ℝ)*base68 + (12145886032102654863/1686875000000000000000000000000000 : ℝ)*base70 + (4362301779687654863/1686875000000000000000000000000000 : ℝ)*base72 + (139254141496067/67475000000000000000000000000 : ℝ)*base74 + (5635703569079220137/1686875000000000000000000000000000 : ℝ)*base75 + (10375962722819529863/1686875000000000000000000000000000 : ℝ)*base78 + (2333681525150154863/1686875000000000000000000000000000 : ℝ)*base80 + (8043706705229/33737500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2517563/1250000000000000000000 : ℝ)*base89 + (2517563/1250000000000000000000 : ℝ)*base91 + (2517563/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1289_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1289_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1289_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1289_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1289_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1289_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
