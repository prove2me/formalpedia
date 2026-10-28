-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:13.61832+00:00
-- url     : https://prove2.me/submissions/19a299b4-684e-418a-9bf3-d56e7f3356e4

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
theorem support_rectangle_w1223_s3_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-425147493/2000000000 : ℝ)*x 0 + (5421348377/10000000000 : ℝ)*x 1 + (5239127169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425147493/2000000000 : ℝ)^263 ≤ (3229767979279/25000000000000 : ℝ)^199 := by
    have hnat : (425147493 : ℕ)^263*25000000000000^199 ≤ 3229767979279^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425147493 2000000000 3229767979279 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421348377/10000000000 : ℝ)^263 ≤ (8904798297339/20000000000000 : ℝ)^199 := by
    have hnat : (5421348377 : ℕ)^263*20000000000000^199 ≤ 8904798297339^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421348377 10000000000 8904798297339 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239127169/10000000000 : ℝ)^263 ≤ (42556936578223/100000000000000 : ℝ)^199 := by
    have hnat : (5239127169 : ℕ)^263*100000000000000^199 ≤ 42556936578223^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239127169 10000000000 42556936578223 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425147493/2000000000 : ℝ), (5421348377/10000000000 : ℝ), (5239127169/10000000000 : ℝ)] ![(3229767979279/25000000000000 : ℝ), (8904798297339/20000000000000 : ℝ), (42556936578223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425147493/2000000000 : ℝ)|^263 ≤ (3229767979279/25000000000000 : ℝ)^199
        have hw : |(-425147493/2000000000 : ℝ)|=(425147493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421348377/10000000000 : ℝ)|^263 ≤ (8904798297339/20000000000000 : ℝ)^199
        have hw : |(5421348377/10000000000 : ℝ)|=(5421348377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239127169/10000000000 : ℝ)|^263 ≤ (42556936578223/100000000000000 : ℝ)^199
        have hw : |(5239127169/10000000000 : ℝ)|=(5239127169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2675955777/5000000000 : ℝ)*x 0 + (-443745689/2000000000 : ℝ)*x 1 + (5239127373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675955777/5000000000 : ℝ)^263 ≤ (10942970402933/25000000000000 : ℝ)^199 := by
    have hnat : (2675955777 : ℕ)^263*25000000000000^199 ≤ 10942970402933^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675955777 5000000000 10942970402933 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443745689/2000000000 : ℝ)^263 ≤ (13671179603209/100000000000000 : ℝ)^199 := by
    have hnat : (443745689 : ℕ)^263*100000000000000^199 ≤ 13671179603209^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443745689 2000000000 13671179603209 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239127373/10000000000 : ℝ)^263 ≤ (1329904336507/3125000000000 : ℝ)^199 := by
    have hnat : (5239127373 : ℕ)^263*3125000000000^199 ≤ 1329904336507^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239127373 10000000000 1329904336507 3125000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675955777/5000000000 : ℝ), (-443745689/2000000000 : ℝ), (5239127373/10000000000 : ℝ)] ![(10942970402933/25000000000000 : ℝ), (13671179603209/100000000000000 : ℝ), (1329904336507/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675955777/5000000000 : ℝ)|^263 ≤ (10942970402933/25000000000000 : ℝ)^199
        have hw : |(2675955777/5000000000 : ℝ)|=(2675955777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443745689/2000000000 : ℝ)|^263 ≤ (13671179603209/100000000000000 : ℝ)^199
        have hw : |(-443745689/2000000000 : ℝ)|=(443745689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239127373/10000000000 : ℝ)|^263 ≤ (1329904336507/3125000000000 : ℝ)^199
        have hw : |(5239127373/10000000000 : ℝ)|=(5239127373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5351911419/10000000000 : ℝ)*x 0 + (5239127769/10000000000 : ℝ)*x 1 + (-1109364051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351911419/10000000000 : ℝ)^263 ≤ (21885940076253/50000000000000 : ℝ)^199 := by
    have hnat : (5351911419 : ℕ)^263*50000000000000^199 ≤ 21885940076253^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351911419 10000000000 21885940076253 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239127769/10000000000 : ℝ)^263 ≤ (42556943019401/100000000000000 : ℝ)^199 := by
    have hnat : (5239127769 : ℕ)^263*100000000000000^199 ≤ 42556943019401^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239127769 10000000000 42556943019401 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109364051/5000000000 : ℝ)^263 ≤ (13671176810031/100000000000000 : ℝ)^199 := by
    have hnat : (1109364051 : ℕ)^263*100000000000000^199 ≤ 13671176810031^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109364051 5000000000 13671176810031 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351911419/10000000000 : ℝ), (5239127769/10000000000 : ℝ), (-1109364051/5000000000 : ℝ)] ![(21885940076253/50000000000000 : ℝ), (42556943019401/100000000000000 : ℝ), (13671176810031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351911419/10000000000 : ℝ)|^263 ≤ (21885940076253/50000000000000 : ℝ)^199
        have hw : |(5351911419/10000000000 : ℝ)|=(5351911419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239127769/10000000000 : ℝ)|^263 ≤ (42556943019401/100000000000000 : ℝ)^199
        have hw : |(5239127769/10000000000 : ℝ)|=(5239127769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1109364051/5000000000 : ℝ)|^263 ≤ (13671176810031/100000000000000 : ℝ)^199
        have hw : |(-1109364051/5000000000 : ℝ)|=(1109364051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4351592497/10000000000 : ℝ)*x 0 + (1042811831/2500000000 : ℝ)*x 1 + (1134884783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351592497/10000000000 : ℝ)^263 ≤ (16649629955619/50000000000000 : ℝ)^199 := by
    have hnat : (4351592497 : ℕ)^263*50000000000000^199 ≤ 16649629955619^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351592497 10000000000 16649629955619 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042811831/2500000000 : ℝ)^263 ≤ (31487661974569/100000000000000 : ℝ)^199 := by
    have hnat : (1042811831 : ℕ)^263*100000000000000^199 ≤ 31487661974569^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042811831 2500000000 31487661974569 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134884783/2500000000 : ℝ)^263 ≤ (4401634761461/12500000000000 : ℝ)^199 := by
    have hnat : (1134884783 : ℕ)^263*12500000000000^199 ≤ 4401634761461^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134884783 2500000000 4401634761461 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351592497/10000000000 : ℝ), (1042811831/2500000000 : ℝ), (1134884783/2500000000 : ℝ)] ![(16649629955619/50000000000000 : ℝ), (31487661974569/100000000000000 : ℝ), (4401634761461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351592497/10000000000 : ℝ)|^263 ≤ (16649629955619/50000000000000 : ℝ)^199
        have hw : |(4351592497/10000000000 : ℝ)|=(4351592497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042811831/2500000000 : ℝ)|^263 ≤ (31487661974569/100000000000000 : ℝ)^199
        have hw : |(1042811831/2500000000 : ℝ)|=(1042811831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134884783/2500000000 : ℝ)|^263 ≤ (4401634761461/12500000000000 : ℝ)^199
        have hw : |(1134884783/2500000000 : ℝ)|=(1134884783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125752323/10000000000 : ℝ)*x 0 + (2619898617/5000000000 : ℝ)*x 1 + (2710337309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125752323/10000000000 : ℝ)^263 ≤ (1614898907111/12500000000000 : ℝ)^199 := by
    have hnat : (2125752323 : ℕ)^263*12500000000000^199 ≤ 1614898907111^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125752323 10000000000 1614898907111 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619898617/5000000000 : ℝ)^263 ≤ (21282065036687/50000000000000 : ℝ)^199 := by
    have hnat : (2619898617 : ℕ)^263*50000000000000^199 ≤ 21282065036687^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619898617 5000000000 21282065036687 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710337309/5000000000 : ℝ)^263 ≤ (44516678658893/100000000000000 : ℝ)^199 := by
    have hnat : (2710337309 : ℕ)^263*100000000000000^199 ≤ 44516678658893^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710337309 5000000000 44516678658893 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125752323/10000000000 : ℝ), (2619898617/5000000000 : ℝ), (2710337309/5000000000 : ℝ)] ![(1614898907111/12500000000000 : ℝ), (21282065036687/50000000000000 : ℝ), (44516678658893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125752323/10000000000 : ℝ)|^263 ≤ (1614898907111/12500000000000 : ℝ)^199
        have hw : |(-2125752323/10000000000 : ℝ)|=(2125752323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619898617/5000000000 : ℝ)|^263 ≤ (21282065036687/50000000000000 : ℝ)^199
        have hw : |(2619898617/5000000000 : ℝ)|=(2619898617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710337309/5000000000 : ℝ)|^263 ≤ (44516678658893/100000000000000 : ℝ)^199
        have hw : |(2710337309/5000000000 : ℝ)|=(2710337309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1061096509/2000000000 : ℝ)*x 0 + (-2037181139/10000000000 : ℝ)*x 1 + (2710337143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061096509/2000000000 : ℝ)^263 ≤ (8654145589143/20000000000000 : ℝ)^199 := by
    have hnat : (1061096509 : ℕ)^263*20000000000000^199 ≤ 8654145589143^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061096509 2000000000 8654145589143 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2037181139/10000000000 : ℝ)^263 ≤ (2442519396107/20000000000000 : ℝ)^199 := by
    have hnat : (2037181139 : ℕ)^263*20000000000000^199 ≤ 2442519396107^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037181139 10000000000 2442519396107 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710337143/5000000000 : ℝ)^263 ≤ (5564584381939/12500000000000 : ℝ)^199 := by
    have hnat : (2710337143 : ℕ)^263*12500000000000^199 ≤ 5564584381939^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710337143 5000000000 5564584381939 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061096509/2000000000 : ℝ), (-2037181139/10000000000 : ℝ), (2710337143/5000000000 : ℝ)] ![(8654145589143/20000000000000 : ℝ), (2442519396107/20000000000000 : ℝ), (5564584381939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061096509/2000000000 : ℝ)|^263 ≤ (8654145589143/20000000000000 : ℝ)^199
        have hw : |(1061096509/2000000000 : ℝ)|=(1061096509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2037181139/10000000000 : ℝ)|^263 ≤ (2442519396107/20000000000000 : ℝ)^199
        have hw : |(-2037181139/10000000000 : ℝ)|=(2037181139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710337143/5000000000 : ℝ)|^263 ≤ (5564584381939/12500000000000 : ℝ)^199
        have hw : |(2710337143/5000000000 : ℝ)|=(2710337143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305482289/10000000000 : ℝ)*x 0 + (5420674277/10000000000 : ℝ)*x 1 + (-4074363/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305482289/10000000000 : ℝ)^263 ≤ (10817681296583/25000000000000 : ℝ)^199 := by
    have hnat : (5305482289 : ℕ)^263*25000000000000^199 ≤ 10817681296583^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305482289 10000000000 10817681296583 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420674277/10000000000 : ℝ)^263 ≤ (4451667495783/10000000000000 : ℝ)^199 := by
    have hnat : (5420674277 : ℕ)^263*10000000000000^199 ≤ 4451667495783^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420674277 10000000000 4451667495783 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4074363/20000000 : ℝ)^263 ≤ (12212599840681/100000000000000 : ℝ)^199 := by
    have hnat : (4074363 : ℕ)^263*100000000000000^199 ≤ 12212599840681^199*20000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4074363 20000000 12212599840681 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305482289/10000000000 : ℝ), (5420674277/10000000000 : ℝ), (-4074363/20000000 : ℝ)] ![(10817681296583/25000000000000 : ℝ), (4451667495783/10000000000000 : ℝ), (12212599840681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305482289/10000000000 : ℝ)|^263 ≤ (10817681296583/25000000000000 : ℝ)^199
        have hw : |(5305482289/10000000000 : ℝ)|=(5305482289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420674277/10000000000 : ℝ)|^263 ≤ (4451667495783/10000000000000 : ℝ)^199
        have hw : |(5420674277/10000000000 : ℝ)|=(5420674277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4074363/20000000 : ℝ)|^263 ≤ (12212599840681/100000000000000 : ℝ)^199
        have hw : |(-4074363/20000000 : ℝ)|=(4074363/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s3_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (108790561/250000000 : ℝ)*x 0 + (907636897/2000000000 : ℝ)*x 1 + (4172608847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108790561/250000000 : ℝ)^263 ≤ (16649781365713/50000000000000 : ℝ)^199 := by
    have hnat : (108790561 : ℕ)^263*50000000000000^199 ≤ 16649781365713^199*250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108790561 250000000 16649781365713 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907636897/2000000000 : ℝ)^263 ≤ (1099974729849/3125000000000 : ℝ)^199 := by
    have hnat : (907636897 : ℕ)^263*3125000000000^199 ≤ 1099974729849^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907636897 2000000000 1099974729849 3125000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172608847/10000000000 : ℝ)^263 ≤ (196882786803/625000000000 : ℝ)^199 := by
    have hnat : (4172608847 : ℕ)^263*625000000000^199 ≤ 196882786803^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172608847 10000000000 196882786803 625000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108790561/250000000 : ℝ), (907636897/2000000000 : ℝ), (4172608847/10000000000 : ℝ)] ![(16649781365713/50000000000000 : ℝ), (1099974729849/3125000000000 : ℝ), (196882786803/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108790561/250000000 : ℝ)|^263 ≤ (16649781365713/50000000000000 : ℝ)^199
        have hw : |(108790561/250000000 : ℝ)|=(108790561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(907636897/2000000000 : ℝ)|^263 ≤ (1099974729849/3125000000000 : ℝ)^199
        have hw : |(907636897/2000000000 : ℝ)|=(907636897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172608847/10000000000 : ℝ)|^263 ≤ (196882786803/625000000000 : ℝ)^199
        have hw : |(4172608847/10000000000 : ℝ)|=(4172608847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5431/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16273/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16273/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16273/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16273/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16273/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16273/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9421/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (3045445335507529/50000000000000000000 : ℝ) := by
    have hpowers : (9421/100000 : ℝ)^8415 ≤ (3045445335507529/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9421 : ℕ)^8415*50000000000000000000^2048 ≤ 3045445335507529^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9421 100000 3045445335507529 50000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9421/100000 : ℝ)) (X := (3045445335507529/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16273/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (57545291552636589/100000000000000000000 : ℝ) := by
    have hpowers : (16273/100000 : ℝ)^8415 ≤ (57545291552636589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16273 : ℕ)^8415*100000000000000000000^2048 ≤ 57545291552636589^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16273 100000 57545291552636589 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16273/100000 : ℝ)) (X := (57545291552636589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003045445335507529/25000000000000000000 : ℝ) ≤ (2500074115087711/2500000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (25003045445335507529/25000000000000000000 : ℝ)^2048 ≤ (2500074115087711/2500000000000000 : ℝ)^8415 := by
      have hnat : (25003045445335507529 : ℕ)^2048*2500000000000000^8415 ≤ 2500074115087711^8415*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003045445335507529 25000000000000000000 2500074115087711 2500000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074115087711/2500000000000000 : ℝ)) (X := (25003045445335507529/25000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100063636182223651647/100000000000000000000 : ℝ) ≤ (10001548372400539/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (100063636182223651647/100000000000000000000 : ℝ)^2048 ≤ (10001548372400539/10000000000000000 : ℝ)^8415 := by
      have hnat : (100063636182223651647 : ℕ)^2048*10000000000000000^8415 ≤ 10001548372400539^8415*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100063636182223651647 100000000000000000000 10001548372400539 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001548372400539/10000000000000000 : ℝ)) (X := (100063636182223651647/100000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50057545291552636589/50000000000000000000 : ℝ) ≤ (5001400142225117/5000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50057545291552636589/50000000000000000000 : ℝ)^2048 ≤ (5001400142225117/5000000000000000 : ℝ)^8415 := by
      have hnat : (50057545291552636589 : ℕ)^2048*5000000000000000^8415 ≤ 5001400142225117^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057545291552636589 50000000000000000000 5001400142225117 5000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001400142225117/5000000000000000 : ℝ)) (X := (50057545291552636589/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3045445335507529/50000000000000000000 : ℝ) ≤ ((11416407136580604983/11420000000000000000 : ℝ)+2*(83460803313/45680000000000 : ℝ)*(9421/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (11416407136580604983/11420000000000000000 : ℝ)+2*(83460803313/45680000000000 : ℝ)*(9421/100000 : ℝ)=(2500074115087711/2500000000000000 : ℝ) by norm_num, show 1+2*(3045445335507529/50000000000000000000 : ℝ)=(25003045445335507529/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57545291552636589/100000000000000000000 : ℝ)+(3045445335507529/50000000000000000000 : ℝ) ≤ ((11416407136580604983/11420000000000000000 : ℝ)+(83460803313/45680000000000 : ℝ)*((16273/100000 : ℝ)+(9421/100000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (11416407136580604983/11420000000000000000 : ℝ)+(83460803313/45680000000000 : ℝ)*((16273/100000 : ℝ)+(9421/100000 : ℝ))=(10001548372400539/10000000000000000 : ℝ) by norm_num, show 1+(57545291552636589/100000000000000000000 : ℝ)+(3045445335507529/50000000000000000000 : ℝ)=(100063636182223651647/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57545291552636589/100000000000000000000 : ℝ) ≤ ((11416407136580604983/11420000000000000000 : ℝ)+2*(83460803313/45680000000000 : ℝ)*(16273/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (11416407136580604983/11420000000000000000 : ℝ)+2*(83460803313/45680000000000 : ℝ)*(16273/100000 : ℝ)=(5001400142225117/5000000000000000 : ℝ) by norm_num, show 1+2*(57545291552636589/100000000000000000000 : ℝ)=(50057545291552636589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11416407136580604983/11420000000000000000 : ℝ)*(X 1 0+X 2 0)+(83460803313/45680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (9421/100000 : ℝ)) (hi := (16273/100000 : ℝ)) (c := (11416407136580604983/11420000000000000000 : ℝ)) (alpha := (83460803313/45680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11416407136580604983/11420000000000000000 : ℝ)*(X 0 1+X 2 1)+(83460803313/45680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (9421/100000 : ℝ)) (hi := (16273/100000 : ℝ)) (c := (11416407136580604983/11420000000000000000 : ℝ)) (alpha := (83460803313/45680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11416407136580604983/11420000000000000000 : ℝ)*(X 0 2+X 1 2)+(83460803313/45680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (9421/100000 : ℝ)) (hi := (16273/100000 : ℝ)) (c := (11416407136580604983/11420000000000000000 : ℝ)) (alpha := (83460803313/45680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-425147493/2000000000 : ℝ)*X 0 0+(5421348377/10000000000 : ℝ)*X 0 1+(5239127169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675955777/5000000000 : ℝ)*X 1 0+(-443745689/2000000000 : ℝ)*X 1 1+(5239127373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351911419/10000000000 : ℝ)*X 2 0+(5239127769/10000000000 : ℝ)*X 2 1+(-1109364051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351592497/10000000000 : ℝ)*X 0 0+(1042811831/2500000000 : ℝ)*X 0 1+(1134884783/2500000000 : ℝ)*X 0 2+(4351592497/10000000000 : ℝ)*X 1 0+(1042811831/2500000000 : ℝ)*X 1 1+(1134884783/2500000000 : ℝ)*X 1 2+(4351592497/10000000000 : ℝ)*X 2 0+(1042811831/2500000000 : ℝ)*X 2 1+(1134884783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125752323/10000000000 : ℝ)*X 0 0+(2619898617/5000000000 : ℝ)*X 0 1+(2710337309/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061096509/2000000000 : ℝ)*X 1 0+(-2037181139/10000000000 : ℝ)*X 1 1+(2710337143/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305482289/10000000000 : ℝ)*X 2 0+(5420674277/10000000000 : ℝ)*X 2 1+(-4074363/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108790561/250000000 : ℝ)*X 0 0+(907636897/2000000000 : ℝ)*X 0 1+(4172608847/10000000000 : ℝ)*X 0 2+(108790561/250000000 : ℝ)*X 1 0+(907636897/2000000000 : ℝ)*X 1 1+(4172608847/10000000000 : ℝ)*X 1 2+(108790561/250000000 : ℝ)*X 2 0+(907636897/2000000000 : ℝ)*X 2 1+(4172608847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11631349369951767845133/2284000000000000000000000000 : ℝ) := by norm_num
    linear_combination (522140937/100000000000000 : ℝ)*(base19) + (4948759/2500000000000 : ℝ)*(base23) + (120470883/100000000000000 : ℝ)*(lower2) + (6207297/20000000000000 : ℝ)*(upper5) + (4101567088237911/100000000000000 : ℝ)*(major0) + (4101567088237911/100000000000000 : ℝ)*(major1) + (4101567088237911/100000000000000 : ℝ)*(major2) + (34299105446159/625000000000 : ℝ)*(sp0) + (5487876208360463/100000000000000 : ℝ)*(sp1) + (5487881067075613/100000000000000 : ℝ)*(sp2) + (543049084622009/20000000000000 : ℝ)*(sp3) + (24393640533/100000000000000 : ℝ)*(sp4) + (2267262287/50000000000000 : ℝ)*(sp5) + (1829647159/25000000000000 : ℝ)*(sp7) + (67881318542467/2500000000000 : ℝ)*(f.failure) + (5487881265025973/100000000000000 : ℝ)*(f.sum) + (6655635476479/2284000000000000000000000000 : ℝ)*base65 + (8163207028437860513/1142000000000000000000000000000000 : ℝ)*base67 + (4724695568789860513/1142000000000000000000000000000000 : ℝ)*base69 + (7380870043652139487/1142000000000000000000000000000000 : ℝ)*base72 + (7827884069053/2284000000000000000000000000 : ℝ)*base74 + (1495832229688139487/1142000000000000000000000000000000 : ℝ)*base76 + (4633303139782139487/1142000000000000000000000000000000 : ℝ)*base78 + (7247459160547860513/1142000000000000000000000000000000 : ℝ)*base79 + (119532270961/2284000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2533617/250000000000000000000 : ℝ)*base90 + (2533617/250000000000000000000 : ℝ)*base92 + (2533617/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6015486086080758454552980849/571000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122657119/5000000000000 : ℝ)*(base19) + (11532163/500000000000 : ℝ)*(base23) + (76508221/100000000000000 : ℝ)*(upper3) + (27177627/20000000000000 : ℝ)*(lower4) + (93819091/25000000000000 : ℝ)*(upper5) + (4132008858879101/100000000000000 : ℝ)*(major0) + (4132008858879101/100000000000000 : ℝ)*(major1) + (4132008858879101/100000000000000 : ℝ)*(major2) + (23776654789/50000000000000 : ℝ)*(sp1) + (32004252893/100000000000000 : ℝ)*(sp2) + (1382153014738647/25000000000000 : ℝ)*(sp4) + (552856205250263/10000000000000 : ℝ)*(sp5) + (1105715549653819/20000000000000 : ℝ)*(sp6) + (1367702653818439/50000000000000 : ℝ)*(sp7) + (1367702653818439/50000000000000 : ℝ)*(f.failure) + (1382153014738647/25000000000000 : ℝ)*(f.sum) + (2481929501149/2284000000000000000000000000 : ℝ)*base65 + (64954454685589717/1142000000000000000000000000000000 : ℝ)*base68 + (5300635749861589717/1142000000000000000000000000000000 : ℝ)*base70 + (9880892035994410283/1142000000000000000000000000000000 : ℝ)*base71 + (16443663716587/2284000000000000000000000000 : ℝ)*base74 + (17228829621241589717/1142000000000000000000000000000000 : ℝ)*base76 + (1619488844525589717/1142000000000000000000000000000000 : ℝ)*base78 + (14528154852834410283/1142000000000000000000000000000000 : ℝ)*base79 + (11114228433107/2284000000000000000000000000 : ℝ)*base82 + (17907011/5000000000000000000000 : ℝ)*base89 + (17907011/5000000000000000000000 : ℝ)*base91 + (17907011/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1223_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5431/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1223_s4_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128146519/10000000000 : ℝ)*x 0 + (5398275543/10000000000 : ℝ)*x 1 + (1315155551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128146519/10000000000 : ℝ)^263 ≤ (12938424993587/100000000000000 : ℝ)^199 := by
    have hnat : (2128146519 : ℕ)^263*100000000000000^199 ≤ 12938424993587^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128146519 10000000000 12938424993587 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398275543/10000000000 : ℝ)^263 ≤ (22136865356673/50000000000000 : ℝ)^199 := by
    have hnat : (5398275543 : ℕ)^263*50000000000000^199 ≤ 22136865356673^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398275543 10000000000 22136865356673 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315155551/2500000000 : ℝ)^263 ≤ (668560066807/1562500000000 : ℝ)^199 := by
    have hnat : (1315155551 : ℕ)^263*1562500000000^199 ≤ 668560066807^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315155551 2500000000 668560066807 1562500000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128146519/10000000000 : ℝ), (5398275543/10000000000 : ℝ), (1315155551/2500000000 : ℝ)] ![(12938424993587/100000000000000 : ℝ), (22136865356673/50000000000000 : ℝ), (668560066807/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128146519/10000000000 : ℝ)|^263 ≤ (12938424993587/100000000000000 : ℝ)^199
        have hw : |(-2128146519/10000000000 : ℝ)|=(2128146519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398275543/10000000000 : ℝ)|^263 ≤ (22136865356673/50000000000000 : ℝ)^199
        have hw : |(5398275543/10000000000 : ℝ)|=(5398275543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315155551/2500000000 : ℝ)|^263 ≤ (668560066807/1562500000000 : ℝ)^199
        have hw : |(1315155551/2500000000 : ℝ)|=(1315155551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (83532913/156250000 : ℝ)*x 0 + (-549511633/2500000000 : ℝ)*x 1 + (1315155533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83532913/156250000 : ℝ)^263 ≤ (8741828899557/20000000000000 : ℝ)^199 := by
    have hnat : (83532913 : ℕ)^263*20000000000000^199 ≤ 8741828899557^199*156250000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83532913 156250000 8741828899557 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549511633/2500000000 : ℝ)^263 ≤ (1687876498361/12500000000000 : ℝ)^199 := by
    have hnat : (549511633 : ℕ)^263*12500000000000^199 ≤ 1687876498361^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549511633 2500000000 1687876498361 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315155533/2500000000 : ℝ)^263 ≤ (5348480437711/12500000000000 : ℝ)^199 := by
    have hnat : (1315155533 : ℕ)^263*12500000000000^199 ≤ 5348480437711^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315155533 2500000000 5348480437711 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83532913/156250000 : ℝ), (-549511633/2500000000 : ℝ), (1315155533/2500000000 : ℝ)] ![(8741828899557/20000000000000 : ℝ), (1687876498361/12500000000000 : ℝ), (5348480437711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83532913/156250000 : ℝ)|^263 ≤ (8741828899557/20000000000000 : ℝ)^199
        have hw : |(83532913/156250000 : ℝ)|=(83532913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549511633/2500000000 : ℝ)|^263 ≤ (1687876498361/12500000000000 : ℝ)^199
        have hw : |(-549511633/2500000000 : ℝ)|=(549511633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315155533/2500000000 : ℝ)|^263 ≤ (5348480437711/12500000000000 : ℝ)^199
        have hw : |(1315155533/2500000000 : ℝ)|=(1315155533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5346106187/10000000000 : ℝ)*x 0 + (1315155541/2500000000 : ℝ)*x 1 + (-68688963/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346106187/10000000000 : ℝ)^263 ≤ (10927285462621/25000000000000 : ℝ)^199 := by
    have hnat : (5346106187 : ℕ)^263*25000000000000^199 ≤ 10927285462621^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346106187 10000000000 10927285462621 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315155541/2500000000 : ℝ)^263 ≤ (4278784384567/10000000000000 : ℝ)^199 := by
    have hnat : (1315155541 : ℕ)^263*10000000000000^199 ≤ 4278784384567^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315155541 2500000000 4278784384567 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68688963/312500000 : ℝ)^263 ≤ (13503014292651/100000000000000 : ℝ)^199 := by
    have hnat : (68688963 : ℕ)^263*100000000000000^199 ≤ 13503014292651^199*312500000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68688963 312500000 13503014292651 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346106187/10000000000 : ℝ), (1315155541/2500000000 : ℝ), (-68688963/312500000 : ℝ)] ![(10927285462621/25000000000000 : ℝ), (4278784384567/10000000000000 : ℝ), (13503014292651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346106187/10000000000 : ℝ)|^263 ≤ (10927285462621/25000000000000 : ℝ)^199
        have hw : |(5346106187/10000000000 : ℝ)|=(5346106187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315155541/2500000000 : ℝ)|^263 ≤ (4278784384567/10000000000000 : ℝ)^199
        have hw : |(1315155541/2500000000 : ℝ)|=(1315155541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68688963/312500000 : ℝ)|^263 ≤ (13503014292651/100000000000000 : ℝ)^199
        have hw : |(-68688963/312500000 : ℝ)|=(68688963/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1088259479/2500000000 : ℝ)*x 0 + (2108050327/5000000000 : ℝ)*x 1 + (898863199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088259479/2500000000 : ℝ)^263 ≤ (33313878518129/100000000000000 : ℝ)^199 := by
    have hnat : (1088259479 : ℕ)^263*100000000000000^199 ≤ 33313878518129^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088259479 2500000000 33313878518129 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108050327/5000000000 : ℝ)^263 ≤ (31935911999157/100000000000000 : ℝ)^199 := by
    have hnat : (2108050327 : ℕ)^263*100000000000000^199 ≤ 31935911999157^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108050327 5000000000 31935911999157 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898863199/2000000000 : ℝ)^263 ≤ (34750209475539/100000000000000 : ℝ)^199 := by
    have hnat : (898863199 : ℕ)^263*100000000000000^199 ≤ 34750209475539^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898863199 2000000000 34750209475539 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088259479/2500000000 : ℝ), (2108050327/5000000000 : ℝ), (898863199/2000000000 : ℝ)] ![(33313878518129/100000000000000 : ℝ), (31935911999157/100000000000000 : ℝ), (34750209475539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088259479/2500000000 : ℝ)|^263 ≤ (33313878518129/100000000000000 : ℝ)^199
        have hw : |(1088259479/2500000000 : ℝ)|=(1088259479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2108050327/5000000000 : ℝ)|^263 ≤ (31935911999157/100000000000000 : ℝ)^199
        have hw : |(2108050327/5000000000 : ℝ)|=(2108050327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898863199/2000000000 : ℝ)|^263 ≤ (34750209475539/100000000000000 : ℝ)^199
        have hw : |(898863199/2000000000 : ℝ)|=(898863199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128152777/10000000000 : ℝ)*x 0 + (5261005319/10000000000 : ℝ)*x 1 + (107957819/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128152777/10000000000 : ℝ)^263 ≤ (404327352383/3125000000000 : ℝ)^199 := by
    have hnat : (2128152777 : ℕ)^263*3125000000000^199 ≤ 404327352383^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128152777 10000000000 404327352383 3125000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261005319/10000000000 : ℝ)^263 ≤ (21395981298383/50000000000000 : ℝ)^199 := by
    have hnat : (5261005319 : ℕ)^263*50000000000000^199 ≤ 21395981298383^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261005319 10000000000 21395981298383 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107957819/200000000 : ℝ)^263 ≤ (44269562114127/100000000000000 : ℝ)^199 := by
    have hnat : (107957819 : ℕ)^263*100000000000000^199 ≤ 44269562114127^199*200000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107957819 200000000 44269562114127 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128152777/10000000000 : ℝ), (5261005319/10000000000 : ℝ), (107957819/200000000 : ℝ)] ![(404327352383/3125000000000 : ℝ), (21395981298383/50000000000000 : ℝ), (44269562114127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128152777/10000000000 : ℝ)|^263 ≤ (404327352383/3125000000000 : ℝ)^199
        have hw : |(-2128152777/10000000000 : ℝ)|=(2128152777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261005319/10000000000 : ℝ)|^263 ≤ (21395981298383/50000000000000 : ℝ)^199
        have hw : |(5261005319/10000000000 : ℝ)|=(5261005319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107957819/200000000 : ℝ)|^263 ≤ (44269562114127/100000000000000 : ℝ)^199
        have hw : |(107957819/200000000 : ℝ)|=(107957819/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5311030587/10000000000 : ℝ)*x 0 + (-1030388959/5000000000 : ℝ)*x 1 + (5397891001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311030587/10000000000 : ℝ)^263 ≤ (43330539450559/100000000000000 : ℝ)^199 := by
    have hnat : (5311030587 : ℕ)^263*100000000000000^199 ≤ 43330539450559^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311030587 10000000000 43330539450559 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030388959/5000000000 : ℝ)^263 ≤ (1239989786861/10000000000000 : ℝ)^199 := by
    have hnat : (1030388959 : ℕ)^263*10000000000000^199 ≤ 1239989786861^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030388959 5000000000 1239989786861 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397891001/10000000000 : ℝ)^263 ≤ (44269562666909/100000000000000 : ℝ)^199 := by
    have hnat : (5397891001 : ℕ)^263*100000000000000^199 ≤ 44269562666909^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397891001 10000000000 44269562666909 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311030587/10000000000 : ℝ), (-1030388959/5000000000 : ℝ), (5397891001/10000000000 : ℝ)] ![(43330539450559/100000000000000 : ℝ), (1239989786861/10000000000000 : ℝ), (44269562666909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311030587/10000000000 : ℝ)|^263 ≤ (43330539450559/100000000000000 : ℝ)^199
        have hw : |(5311030587/10000000000 : ℝ)|=(5311030587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030388959/5000000000 : ℝ)|^263 ≤ (1239989786861/10000000000000 : ℝ)^199
        have hw : |(-1030388959/5000000000 : ℝ)|=(1030388959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397891001/10000000000 : ℝ)|^263 ≤ (44269562666909/100000000000000 : ℝ)^199
        have hw : |(5397891001/10000000000 : ℝ)|=(5397891001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5311030467/10000000000 : ℝ)*x 0 + (1349472781/2500000000 : ℝ)*x 1 + (-1030388957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311030467/10000000000 : ℝ)^263 ≤ (43330538156663/100000000000000 : ℝ)^199 := by
    have hnat : (5311030467 : ℕ)^263*100000000000000^199 ≤ 43330538156663^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311030467 10000000000 43330538156663 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349472781/2500000000 : ℝ)^263 ≤ (4426956400009/10000000000000 : ℝ)^199 := by
    have hnat : (1349472781 : ℕ)^263*10000000000000^199 ≤ 4426956400009^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349472781 2500000000 4426956400009 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030388957/5000000000 : ℝ)^263 ≤ (12399897836801/100000000000000 : ℝ)^199 := by
    have hnat : (1030388957 : ℕ)^263*100000000000000^199 ≤ 12399897836801^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030388957 5000000000 12399897836801 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311030467/10000000000 : ℝ), (1349472781/2500000000 : ℝ), (-1030388957/5000000000 : ℝ)] ![(43330538156663/100000000000000 : ℝ), (4426956400009/10000000000000 : ℝ), (12399897836801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311030467/10000000000 : ℝ)|^263 ≤ (43330538156663/100000000000000 : ℝ)^199
        have hw : |(5311030467/10000000000 : ℝ)|=(5311030467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349472781/2500000000 : ℝ)|^263 ≤ (4426956400009/10000000000000 : ℝ)^199
        have hw : |(1349472781/2500000000 : ℝ)|=(1349472781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030388957/5000000000 : ℝ)|^263 ≤ (12399897836801/100000000000000 : ℝ)^199
        have hw : |(-1030388957/5000000000 : ℝ)|=(1030388957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s4_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2176525497/5000000000 : ℝ)*x 0 + (2246770907/5000000000 : ℝ)*x 1 + (1054219413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176525497/5000000000 : ℝ)^263 ≤ (33314010792883/100000000000000 : ℝ)^199 := by
    have hnat : (2176525497 : ℕ)^263*100000000000000^199 ≤ 33314010792883^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176525497 5000000000 33314010792883 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246770907/5000000000 : ℝ)^263 ≤ (34742298555903/100000000000000 : ℝ)^199 := by
    have hnat : (2246770907 : ℕ)^263*100000000000000^199 ≤ 34742298555903^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246770907 5000000000 34742298555903 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054219413/2500000000 : ℝ)^263 ≤ (31943690641349/100000000000000 : ℝ)^199 := by
    have hnat : (1054219413 : ℕ)^263*100000000000000^199 ≤ 31943690641349^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054219413 2500000000 31943690641349 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176525497/5000000000 : ℝ), (2246770907/5000000000 : ℝ), (1054219413/2500000000 : ℝ)] ![(33314010792883/100000000000000 : ℝ), (34742298555903/100000000000000 : ℝ), (31943690641349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176525497/5000000000 : ℝ)|^263 ≤ (33314010792883/100000000000000 : ℝ)^199
        have hw : |(2176525497/5000000000 : ℝ)|=(2176525497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246770907/5000000000 : ℝ)|^263 ≤ (34742298555903/100000000000000 : ℝ)^199
        have hw : |(2246770907/5000000000 : ℝ)|=(2246770907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054219413/2500000000 : ℝ)|^263 ≤ (31943690641349/100000000000000 : ℝ)^199
        have hw : |(1054219413/2500000000 : ℝ)|=(1054219413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (283/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5431/50000 : ℝ) ^ (8415/2048 : ℝ) ≤ (1366383434655813/12500000000000000000 : ℝ) := by
    have hpowers : (5431/50000 : ℝ)^8415 ≤ (1366383434655813/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5431 : ℕ)^8415*12500000000000000000^2048 ≤ 1366383434655813^2048*50000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5431 50000 1366383434655813 12500000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5431/50000 : ℝ)) (X := (1366383434655813/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14719/100000 : ℝ) ^ (8415/2048 : ℝ) ≤ (38098354650797793/100000000000000000000 : ℝ) := by
    have hpowers : (14719/100000 : ℝ)^8415 ≤ (38098354650797793/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14719 : ℕ)^8415*100000000000000000000^2048 ≤ 38098354650797793^2048*100000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14719 100000 38098354650797793 100000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14719/100000 : ℝ)) (X := (38098354650797793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251366383434655813/6250000000000000000 : ℝ) ≤ (2500133006386683/2500000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (6251366383434655813/6250000000000000000 : ℝ)^2048 ≤ (2500133006386683/2500000000000000 : ℝ)^8415 := by
      have hnat : (6251366383434655813 : ℕ)^2048*2500000000000000^8415 ≤ 2500133006386683^8415*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251366383434655813 6250000000000000000 2500133006386683 2500000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500133006386683/2500000000000000 : ℝ)) (X := (6251366383434655813/6250000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049029422128044297/100000000000000000000 : ℝ) ≤ (78134320561957/78125000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (100049029422128044297/100000000000000000000 : ℝ)^2048 ≤ (78134320561957/78125000000000 : ℝ)^8415 := by
      have hnat : (100049029422128044297 : ℕ)^2048*78125000000000^8415 ≤ 78134320561957^8415*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049029422128044297 100000000000000000000 78134320561957 78125000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78134320561957/78125000000000 : ℝ)) (X := (100049029422128044297/100000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038098354650797793/50000000000000000000 : ℝ) ≤ (500092701915713/500000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50038098354650797793/50000000000000000000 : ℝ)^2048 ≤ (500092701915713/500000000000000 : ℝ)^8415 := by
      have hnat : (50038098354650797793 : ℕ)^2048*500000000000000^8415 ≤ 500092701915713^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038098354650797793 50000000000000000000 500092701915713 500000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500092701915713/500000000000000 : ℝ)) (X := (50038098354650797793/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1366383434655813/12500000000000000000 : ℝ) ≤ ((9639423079963214047/9642500000000000000 : ℝ)+2*(165251595941/96425000000000 : ℝ)*(5431/50000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (9639423079963214047/9642500000000000000 : ℝ)+2*(165251595941/96425000000000 : ℝ)*(5431/50000 : ℝ)=(2500133006386683/2500000000000000 : ℝ) by norm_num, show 1+2*(1366383434655813/12500000000000000000 : ℝ)=(6251366383434655813/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38098354650797793/100000000000000000000 : ℝ)+(1366383434655813/12500000000000000000 : ℝ) ≤ ((9639423079963214047/9642500000000000000 : ℝ)+(165251595941/96425000000000 : ℝ)*((14719/100000 : ℝ)+(5431/50000 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (9639423079963214047/9642500000000000000 : ℝ)+(165251595941/96425000000000 : ℝ)*((14719/100000 : ℝ)+(5431/50000 : ℝ))=(78134320561957/78125000000000 : ℝ) by norm_num, show 1+(38098354650797793/100000000000000000000 : ℝ)+(1366383434655813/12500000000000000000 : ℝ)=(100049029422128044297/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38098354650797793/100000000000000000000 : ℝ) ≤ ((9639423079963214047/9642500000000000000 : ℝ)+2*(165251595941/96425000000000 : ℝ)*(14719/100000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (9639423079963214047/9642500000000000000 : ℝ)+2*(165251595941/96425000000000 : ℝ)*(14719/100000 : ℝ)=(500092701915713/500000000000000 : ℝ) by norm_num, show 1+2*(38098354650797793/100000000000000000000 : ℝ)=(50038098354650797793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9639423079963214047/9642500000000000000 : ℝ)*(X 1 0+X 2 0)+(165251595941/96425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (5431/50000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (9639423079963214047/9642500000000000000 : ℝ)) (alpha := (165251595941/96425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9639423079963214047/9642500000000000000 : ℝ)*(X 0 1+X 2 1)+(165251595941/96425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (5431/50000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (9639423079963214047/9642500000000000000 : ℝ)) (alpha := (165251595941/96425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9639423079963214047/9642500000000000000 : ℝ)*(X 0 2+X 1 2)+(165251595941/96425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (5431/50000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (9639423079963214047/9642500000000000000 : ℝ)) (alpha := (165251595941/96425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128146519/10000000000 : ℝ)*X 0 0+(5398275543/10000000000 : ℝ)*X 0 1+(1315155551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83532913/156250000 : ℝ)*X 1 0+(-549511633/2500000000 : ℝ)*X 1 1+(1315155533/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346106187/10000000000 : ℝ)*X 2 0+(1315155541/2500000000 : ℝ)*X 2 1+(-68688963/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088259479/2500000000 : ℝ)*X 0 0+(2108050327/5000000000 : ℝ)*X 0 1+(898863199/2000000000 : ℝ)*X 0 2+(1088259479/2500000000 : ℝ)*X 1 0+(2108050327/5000000000 : ℝ)*X 1 1+(898863199/2000000000 : ℝ)*X 1 2+(1088259479/2500000000 : ℝ)*X 2 0+(2108050327/5000000000 : ℝ)*X 2 1+(898863199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128152777/10000000000 : ℝ)*X 0 0+(5261005319/10000000000 : ℝ)*X 0 1+(107957819/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311030587/10000000000 : ℝ)*X 1 0+(-1030388959/5000000000 : ℝ)*X 1 1+(5397891001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311030467/10000000000 : ℝ)*X 2 0+(1349472781/2500000000 : ℝ)*X 2 1+(-1030388957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176525497/5000000000 : ℝ)*X 0 0+(2246770907/5000000000 : ℝ)*X 0 1+(1054219413/2500000000 : ℝ)*X 0 2+(2176525497/5000000000 : ℝ)*X 1 0+(2246770907/5000000000 : ℝ)*X 1 1+(1054219413/2500000000 : ℝ)*X 1 2+(2176525497/5000000000 : ℝ)*X 2 0+(2246770907/5000000000 : ℝ)*X 2 1+(1054219413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (932910522429263680652941527/120531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (478172793/25000000000000 : ℝ)*(base19) + (1809059681/100000000000000 : ℝ)*(base23) + (70352637/50000000000000 : ℝ)*(upper2) + (320127117/100000000000000 : ℝ)*(upper3) + (9061031/50000000000000 : ℝ)*(upper4) + (1357388889775053/25000000000000 : ℝ)*(major0) + (1357388889775053/25000000000000 : ℝ)*(major1) + (1357388889775053/25000000000000 : ℝ)*(major2) + (7264685881123049/100000000000000 : ℝ)*(sp0) + (454045179677961/6250000000000 : ℝ)*(sp1) + (1816180744619717/25000000000000 : ℝ)*(sp2) + (8985900946113/250000000000 : ℝ)*(sp3) + (77812831/200000000000 : ℝ)*(sp4) + (321177713/1250000000000 : ℝ)*(sp7) + (22464912954139/625000000000 : ℝ)*(f.failure) + (7264724787538549/100000000000000 : ℝ)*(f.sum) + (16414491886297/19285000000000000000000000000 : ℝ)*base66 + (35806913994118009/241062500000000000000000000000000 : ℝ)*base68 + (2638501262073819491/241062500000000000000000000000000 : ℝ)*base69 + (746448780226930509/241062500000000000000000000000000 : ℝ)*base72 + (2035102206407/1205312500000000000000000000 : ℝ)*base74 + (7003559612508069491/241062500000000000000000000000000 : ℝ)*base75 + (4988034226611319491/241062500000000000000000000000000 : ℝ)*base77 + (2738317376008069491/241062500000000000000000000000000 : ℝ)*base79 + (630407311539/602656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (106311/62500000000000000000 : ℝ)*base89 + (106311/62500000000000000000 : ℝ)*base91 + (106311/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (580920309031671062129366121/60265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472021793/25000000000000 : ℝ)*(base19) + (1766913363/100000000000000 : ℝ)*(base23) + (281534729/100000000000000 : ℝ)*(upper3) + (8778841/100000000000000 : ℝ)*(lower4) + (40294209/25000000000000 : ℝ)*(upper5) + (1364981739148969/25000000000000 : ℝ)*(major0) + (1364981739148969/25000000000000 : ℝ)*(major1) + (1364981739148969/25000000000000 : ℝ)*(major2) + (711014397/1562500000000 : ℝ)*(sp1) + (49647463487/100000000000000 : ℝ)*(sp2) + (7305361540565623/100000000000000 : ℝ)*(sp4) + (7305314147557043/100000000000000 : ℝ)*(sp5) + (7305310126188773/100000000000000 : ℝ)*(sp6) + (903623012828771/25000000000000 : ℝ)*(sp7) + (903623012828771/25000000000000 : ℝ)*(f.failure) + (7305361540565623/100000000000000 : ℝ)*(f.sum) + (100650921281139/19285000000000000000000000000 : ℝ)*base65 + (909287152321705043/241062500000000000000000000000000 : ℝ)*base67 + (1273449783647642543/241062500000000000000000000000000 : ℝ)*base69 + (1830726168686705043/241062500000000000000000000000000 : ℝ)*base71 + (56872906931077/9642500000000000000000000000 : ℝ)*base73 + (3093749366914419957/241062500000000000000000000000000 : ℝ)*base76 + (1580004158593517543/241062500000000000000000000000000 : ℝ)*base77 + (1645364750419767543/241062500000000000000000000000000 : ℝ)*base79 + (33112369406437/9642500000000000000000000000 : ℝ)*base81 + (24828721/2500000000000000000000 : ℝ)*base90 + (24828721/2500000000000000000000 : ℝ)*base92 + (24828721/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1223_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1223_s5_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064314131/5000000000 : ℝ)*x 0 + (337054517/625000000 : ℝ)*x 1 + (5265708777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064314131/5000000000 : ℝ)^263 ≤ (12942295909879/100000000000000 : ℝ)^199 := by
    have hnat : (1064314131 : ℕ)^263*100000000000000^199 ≤ 12942295909879^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064314131 5000000000 12942295909879 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337054517/625000000 : ℝ)^263 ≤ (44215173477147/100000000000000 : ℝ)^199 := by
    have hnat : (337054517 : ℕ)^263*100000000000000^199 ≤ 44215173477147^199*625000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337054517 625000000 44215173477147 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265708777/10000000000 : ℝ)^263 ≤ (10710632650577/25000000000000 : ℝ)^199 := by
    have hnat : (5265708777 : ℕ)^263*25000000000000^199 ≤ 10710632650577^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265708777 10000000000 10710632650577 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064314131/5000000000 : ℝ), (337054517/625000000 : ℝ), (5265708777/10000000000 : ℝ)] ![(12942295909879/100000000000000 : ℝ), (44215173477147/100000000000000 : ℝ), (10710632650577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064314131/5000000000 : ℝ)|^263 ≤ (12942295909879/100000000000000 : ℝ)^199
        have hw : |(-1064314131/5000000000 : ℝ)|=(1064314131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337054517/625000000 : ℝ)|^263 ≤ (44215173477147/100000000000000 : ℝ)^199
        have hw : |(337054517/625000000 : ℝ)|=(337054517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265708777/10000000000 : ℝ)|^263 ≤ (10710632650577/25000000000000 : ℝ)^199
        have hw : |(5265708777/10000000000 : ℝ)|=(5265708777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5344740847/10000000000 : ℝ)*x 0 + (-548281579/2500000000 : ℝ)*x 1 + (5265708791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344740847/10000000000 : ℝ)^263 ≤ (43694389529667/100000000000000 : ℝ)^199 := by
    have hnat : (5344740847 : ℕ)^263*100000000000000^199 ≤ 43694389529667^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344740847 10000000000 43694389529667 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548281579/2500000000 : ℝ)^263 ≤ (13463079700261/100000000000000 : ℝ)^199 := by
    have hnat : (548281579 : ℕ)^263*100000000000000^199 ≤ 13463079700261^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548281579 2500000000 13463079700261 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265708791/10000000000 : ℝ)^263 ≤ (42842530752847/100000000000000 : ℝ)^199 := by
    have hnat : (5265708791 : ℕ)^263*100000000000000^199 ≤ 42842530752847^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265708791 10000000000 42842530752847 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344740847/10000000000 : ℝ), (-548281579/2500000000 : ℝ), (5265708791/10000000000 : ℝ)] ![(43694389529667/100000000000000 : ℝ), (13463079700261/100000000000000 : ℝ), (42842530752847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344740847/10000000000 : ℝ)|^263 ≤ (43694389529667/100000000000000 : ℝ)^199
        have hw : |(5344740847/10000000000 : ℝ)|=(5344740847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548281579/2500000000 : ℝ)|^263 ≤ (13463079700261/100000000000000 : ℝ)^199
        have hw : |(-548281579/2500000000 : ℝ)|=(548281579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265708791/10000000000 : ℝ)|^263 ≤ (42842530752847/100000000000000 : ℝ)^199
        have hw : |(5265708791/10000000000 : ℝ)|=(5265708791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336185219/2500000000 : ℝ)*x 0 + (2632854431/5000000000 : ℝ)*x 1 + (-274140773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336185219/2500000000 : ℝ)^263 ≤ (8738877968599/20000000000000 : ℝ)^199 := by
    have hnat : (1336185219 : ℕ)^263*20000000000000^199 ≤ 8738877968599^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336185219 2500000000 8738877968599 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632854431/5000000000 : ℝ)^263 ≤ (8568506303259/20000000000000 : ℝ)^199 := by
    have hnat : (2632854431 : ℕ)^263*20000000000000^199 ≤ 8568506303259^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632854431 5000000000 8568506303259 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274140773/1250000000 : ℝ)^263 ≤ (673153931467/5000000000000 : ℝ)^199 := by
    have hnat : (274140773 : ℕ)^263*5000000000000^199 ≤ 673153931467^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274140773 1250000000 673153931467 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336185219/2500000000 : ℝ), (2632854431/5000000000 : ℝ), (-274140773/1250000000 : ℝ)] ![(8738877968599/20000000000000 : ℝ), (8568506303259/20000000000000 : ℝ), (673153931467/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336185219/2500000000 : ℝ)|^263 ≤ (8738877968599/20000000000000 : ℝ)^199
        have hw : |(1336185219/2500000000 : ℝ)|=(1336185219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632854431/5000000000 : ℝ)|^263 ≤ (8568506303259/20000000000000 : ℝ)^199
        have hw : |(2632854431/5000000000 : ℝ)|=(2632854431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274140773/1250000000 : ℝ)|^263 ≤ (673153931467/5000000000000 : ℝ)^199
        have hw : |(-274140773/1250000000 : ℝ)|=(274140773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (108832997/250000000 : ℝ)*x 0 + (4226665371/10000000000 : ℝ)*x 1 + (28022993/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108832997/250000000 : ℝ)^263 ≤ (16658365206809/50000000000000 : ℝ)^199 := by
    have hnat : (108832997 : ℕ)^263*50000000000000^199 ≤ 16658365206809^199*250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108832997 250000000 16658365206809 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226665371/10000000000 : ℝ)^263 ≤ (32041716405347/100000000000000 : ℝ)^199 := by
    have hnat : (4226665371 : ℕ)^263*100000000000000^199 ≤ 32041716405347^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226665371 10000000000 32041716405347 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28022993/62500000 : ℝ)^263 ≤ (2165097073021/6250000000000 : ℝ)^199 := by
    have hnat : (28022993 : ℕ)^263*6250000000000^199 ≤ 2165097073021^199*62500000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28022993 62500000 2165097073021 6250000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108832997/250000000 : ℝ), (4226665371/10000000000 : ℝ), (28022993/62500000 : ℝ)] ![(16658365206809/50000000000000 : ℝ), (32041716405347/100000000000000 : ℝ), (2165097073021/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108832997/250000000 : ℝ)|^263 ≤ (16658365206809/50000000000000 : ℝ)^199
        have hw : |(108832997/250000000 : ℝ)|=(108832997/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226665371/10000000000 : ℝ)|^263 ≤ (32041716405347/100000000000000 : ℝ)^199
        have hw : |(4226665371/10000000000 : ℝ)|=(4226665371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28022993/62500000 : ℝ)|^263 ≤ (2165097073021/6250000000000 : ℝ)^199
        have hw : |(28022993/62500000 : ℝ)|=(28022993/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064316553/5000000000 : ℝ)*x 0 + (1316508993/2500000000 : ℝ)*x 1 + (269627199/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064316553/5000000000 : ℝ)^263 ≤ (12942334833969/100000000000000 : ℝ)^199 := by
    have hnat : (1064316553 : ℕ)^263*100000000000000^199 ≤ 12942334833969^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064316553 5000000000 12942334833969 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316508993/2500000000 : ℝ)^263 ≤ (2142302444743/5000000000000 : ℝ)^199 := by
    have hnat : (1316508993 : ℕ)^263*5000000000000^199 ≤ 2142302444743^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316508993 2500000000 2142302444743 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269627199/500000000 : ℝ)^263 ≤ (44211616263749/100000000000000 : ℝ)^199 := by
    have hnat : (269627199 : ℕ)^263*100000000000000^199 ≤ 44211616263749^199*500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269627199 500000000 44211616263749 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064316553/5000000000 : ℝ), (1316508993/2500000000 : ℝ), (269627199/500000000 : ℝ)] ![(12942334833969/100000000000000 : ℝ), (2142302444743/5000000000000 : ℝ), (44211616263749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064316553/5000000000 : ℝ)|^263 ≤ (12942334833969/100000000000000 : ℝ)^199
        have hw : |(-1064316553/5000000000 : ℝ)|=(1064316553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316508993/2500000000 : ℝ)|^263 ≤ (2142302444743/5000000000000 : ℝ)^199
        have hw : |(1316508993/2500000000 : ℝ)|=(1316508993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269627199/500000000 : ℝ)|^263 ≤ (44211616263749/100000000000000 : ℝ)^199
        have hw : |(269627199/500000000 : ℝ)|=(269627199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656168347/5000000000 : ℝ)*x 0 + (-1033145603/5000000000 : ℝ)*x 1 + (1348136017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656168347/5000000000 : ℝ)^263 ≤ (43344623057489/100000000000000 : ℝ)^199 := by
    have hnat : (2656168347 : ℕ)^263*100000000000000^199 ≤ 43344623057489^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656168347 5000000000 43344623057489 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033145603/5000000000 : ℝ)^263 ≤ (6221879859573/50000000000000 : ℝ)^199 := by
    have hnat : (1033145603 : ℕ)^263*50000000000000^199 ≤ 6221879859573^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033145603 5000000000 6221879859573 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348136017/2500000000 : ℝ)^263 ≤ (8842323443453/20000000000000 : ℝ)^199 := by
    have hnat : (1348136017 : ℕ)^263*20000000000000^199 ≤ 8842323443453^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348136017 2500000000 8842323443453 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656168347/5000000000 : ℝ), (-1033145603/5000000000 : ℝ), (1348136017/2500000000 : ℝ)] ![(43344623057489/100000000000000 : ℝ), (6221879859573/50000000000000 : ℝ), (8842323443453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656168347/5000000000 : ℝ)|^263 ≤ (43344623057489/100000000000000 : ℝ)^199
        have hw : |(2656168347/5000000000 : ℝ)|=(2656168347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033145603/5000000000 : ℝ)|^263 ≤ (6221879859573/50000000000000 : ℝ)^199
        have hw : |(-1033145603/5000000000 : ℝ)|=(1033145603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348136017/2500000000 : ℝ)|^263 ≤ (8842323443453/20000000000000 : ℝ)^199
        have hw : |(1348136017/2500000000 : ℝ)|=(1348136017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1062467377/2000000000 : ℝ)*x 0 + (2696271981/5000000000 : ℝ)*x 1 + (-206629109/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062467377/2000000000 : ℝ)^263 ≤ (21672312558551/50000000000000 : ℝ)^199 := by
    have hnat : (1062467377 : ℕ)^263*50000000000000^199 ≤ 21672312558551^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062467377 2000000000 21672312558551 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696271981/5000000000 : ℝ)^263 ≤ (44211616068711/100000000000000 : ℝ)^199 := by
    have hnat : (2696271981 : ℕ)^263*100000000000000^199 ≤ 44211616068711^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696271981 5000000000 44211616068711 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206629109/1000000000 : ℝ)^263 ≤ (12443758795893/100000000000000 : ℝ)^199 := by
    have hnat : (206629109 : ℕ)^263*100000000000000^199 ≤ 12443758795893^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206629109 1000000000 12443758795893 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062467377/2000000000 : ℝ), (2696271981/5000000000 : ℝ), (-206629109/1000000000 : ℝ)] ![(21672312558551/50000000000000 : ℝ), (44211616068711/100000000000000 : ℝ), (12443758795893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062467377/2000000000 : ℝ)|^263 ≤ (21672312558551/50000000000000 : ℝ)^199
        have hw : |(1062467377/2000000000 : ℝ)|=(1062467377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696271981/5000000000 : ℝ)|^263 ≤ (44211616068711/100000000000000 : ℝ)^199
        have hw : |(2696271981/5000000000 : ℝ)|=(2696271981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206629109/1000000000 : ℝ)|^263 ≤ (12443758795893/100000000000000 : ℝ)^199
        have hw : |(-206629109/1000000000 : ℝ)|=(206629109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_s5_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2176664971/5000000000 : ℝ)*x 0 + (2241509021/5000000000 : ℝ)*x 1 + (1056832171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176664971/5000000000 : ℝ)^263 ≤ (16658416092883/50000000000000 : ℝ)^199 := by
    have hnat : (2176664971 : ℕ)^263*50000000000000^199 ≤ 16658416092883^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176664971 5000000000 16658416092883 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241509021/5000000000 : ℝ)^263 ≤ (34634805554169/100000000000000 : ℝ)^199 := by
    have hnat : (2241509021 : ℕ)^263*100000000000000^199 ≤ 34634805554169^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241509021 5000000000 34634805554169 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056832171/2500000000 : ℝ)^263 ≤ (32048362247879/100000000000000 : ℝ)^199 := by
    have hnat : (1056832171 : ℕ)^263*100000000000000^199 ≤ 32048362247879^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056832171 2500000000 32048362247879 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176664971/5000000000 : ℝ), (2241509021/5000000000 : ℝ), (1056832171/2500000000 : ℝ)] ![(16658416092883/50000000000000 : ℝ), (34634805554169/100000000000000 : ℝ), (32048362247879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176664971/5000000000 : ℝ)|^263 ≤ (16658416092883/50000000000000 : ℝ)^199
        have hw : |(2176664971/5000000000 : ℝ)|=(2176664971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241509021/5000000000 : ℝ)|^263 ≤ (34634805554169/100000000000000 : ℝ)^199
        have hw : |(2241509021/5000000000 : ℝ)|=(2241509021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056832171/2500000000 : ℝ)|^263 ≤ (32048362247879/100000000000000 : ℝ)^199
        have hw : |(1056832171/2500000000 : ℝ)|=(1056832171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (283/2500 : ℝ) ^ (8415/2048 : ℝ) ≤ (3238188738266479/25000000000000000000 : ℝ) := by
    have hpowers : (283/2500 : ℝ)^8415 ≤ (3238188738266479/25000000000000000000 : ℝ)^2048 := by
      have hnat : (283 : ℕ)^8415*25000000000000000000^2048 ≤ 3238188738266479^2048*2500^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        283 2500 3238188738266479 25000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (283/2500 : ℝ)) (X := (3238188738266479/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8415/2048 : ℝ) ≤ (16608756450301713/50000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8415 ≤ (16608756450301713/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8415*50000000000000000000^2048 ≤ 16608756450301713^2048*25000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 16608756450301713 50000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (16608756450301713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503238188738266479/12500000000000000000 : ℝ) ≤ (200012608267507/200000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (12503238188738266479/12500000000000000000 : ℝ)^2048 ≤ (200012608267507/200000000000000 : ℝ)^8415 := by
      have hnat : (12503238188738266479 : ℕ)^2048*200000000000000^8415 ≤ 200012608267507^8415*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503238188738266479 12500000000000000000 200012608267507 200000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200012608267507/200000000000000 : ℝ)) (X := (12503238188738266479/12500000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023085133926834671/50000000000000000000 : ℝ) ≤ (10001123472335177/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (50023085133926834671/50000000000000000000 : ℝ)^2048 ≤ (10001123472335177/10000000000000000 : ℝ)^8415 := by
      have hnat : (50023085133926834671 : ℕ)^2048*10000000000000000^8415 ≤ 10001123472335177^8415*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023085133926834671 50000000000000000000 10001123472335177 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001123472335177/10000000000000000 : ℝ)) (X := (50023085133926834671/50000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016608756450301713/25000000000000000000 : ℝ) ≤ (2500404132823751/2500000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (25016608756450301713/25000000000000000000 : ℝ)^2048 ≤ (2500404132823751/2500000000000000 : ℝ)^8415 := by
      have hnat : (25016608756450301713 : ℕ)^2048*2500000000000000^8415 ≤ 2500404132823751^8415*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016608756450301713 25000000000000000000 2500404132823751 2500000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500404132823751/2500000000000000 : ℝ)) (X := (25016608756450301713/25000000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3238188738266479/25000000000000000000 : ℝ) ≤ ((242922295254600311/243000000000000000 : ℝ)+2*(164352986609/97200000000000 : ℝ)*(283/2500 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (242922295254600311/243000000000000000 : ℝ)+2*(164352986609/97200000000000 : ℝ)*(283/2500 : ℝ)=(200012608267507/200000000000000 : ℝ) by norm_num, show 1+2*(3238188738266479/25000000000000000000 : ℝ)=(12503238188738266479/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16608756450301713/50000000000000000000 : ℝ)+(3238188738266479/25000000000000000000 : ℝ) ≤ ((242922295254600311/243000000000000000 : ℝ)+(164352986609/97200000000000 : ℝ)*((3559/25000 : ℝ)+(283/2500 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (242922295254600311/243000000000000000 : ℝ)+(164352986609/97200000000000 : ℝ)*((3559/25000 : ℝ)+(283/2500 : ℝ))=(10001123472335177/10000000000000000 : ℝ) by norm_num, show 1+(16608756450301713/50000000000000000000 : ℝ)+(3238188738266479/25000000000000000000 : ℝ)=(50023085133926834671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16608756450301713/50000000000000000000 : ℝ) ≤ ((242922295254600311/243000000000000000 : ℝ)+2*(164352986609/97200000000000 : ℝ)*(3559/25000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (242922295254600311/243000000000000000 : ℝ)+2*(164352986609/97200000000000 : ℝ)*(3559/25000 : ℝ)=(2500404132823751/2500000000000000 : ℝ) by norm_num, show 1+2*(16608756450301713/50000000000000000000 : ℝ)=(25016608756450301713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (242922295254600311/243000000000000000 : ℝ)*(X 1 0+X 2 0)+(164352986609/97200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (242922295254600311/243000000000000000 : ℝ)) (alpha := (164352986609/97200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (242922295254600311/243000000000000000 : ℝ)*(X 0 1+X 2 1)+(164352986609/97200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (242922295254600311/243000000000000000 : ℝ)) (alpha := (164352986609/97200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (242922295254600311/243000000000000000 : ℝ)*(X 0 2+X 1 2)+(164352986609/97200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (242922295254600311/243000000000000000 : ℝ)) (alpha := (164352986609/97200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064314131/5000000000 : ℝ)*X 0 0+(337054517/625000000 : ℝ)*X 0 1+(5265708777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344740847/10000000000 : ℝ)*X 1 0+(-548281579/2500000000 : ℝ)*X 1 1+(5265708791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336185219/2500000000 : ℝ)*X 2 0+(2632854431/5000000000 : ℝ)*X 2 1+(-274140773/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108832997/250000000 : ℝ)*X 0 0+(4226665371/10000000000 : ℝ)*X 0 1+(28022993/62500000 : ℝ)*X 0 2+(108832997/250000000 : ℝ)*X 1 0+(4226665371/10000000000 : ℝ)*X 1 1+(28022993/62500000 : ℝ)*X 1 2+(108832997/250000000 : ℝ)*X 2 0+(4226665371/10000000000 : ℝ)*X 2 1+(28022993/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064316553/5000000000 : ℝ)*X 0 0+(1316508993/2500000000 : ℝ)*X 0 1+(269627199/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656168347/5000000000 : ℝ)*X 1 0+(-1033145603/5000000000 : ℝ)*X 1 1+(1348136017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062467377/2000000000 : ℝ)*X 2 0+(2696271981/5000000000 : ℝ)*X 2 1+(-206629109/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176664971/5000000000 : ℝ)*X 0 0+(2241509021/5000000000 : ℝ)*X 0 1+(1056832171/2500000000 : ℝ)*X 0 2+(2176664971/5000000000 : ℝ)*X 1 0+(2241509021/5000000000 : ℝ)*X 1 1+(1056832171/2500000000 : ℝ)*X 1 2+(2176664971/5000000000 : ℝ)*X 2 0+(2241509021/5000000000 : ℝ)*X 2 1+(1056832171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23106097302089087242211/9000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (340264581/50000000000000 : ℝ)*(base19) + (160988323/25000000000000 : ℝ)*(base23) + (2474291/5000000000000 : ℝ)*(upper4) + (99712181/100000000000000 : ℝ)*(upper5) + (235096080996141/4000000000000 : ℝ)*(major0) + (235096080996141/4000000000000 : ℝ)*(major1) + (235096080996141/4000000000000 : ℝ)*(major2) + (7863913386937107/100000000000000 : ℝ)*(sp0) + (393196948803753/5000000000000 : ℝ)*(sp1) + (1965985303365137/25000000000000 : ℝ)*(sp2) + (972713671501211/25000000000000 : ℝ)*(sp3) + (28470476733/100000000000000 : ℝ)*(sp4) + (2200809619/100000000000000 : ℝ)*(sp5) + (927601277/12500000000000 : ℝ)*(sp7) + (3890862106815061/100000000000000 : ℝ)*(f.failure) + (98299273217673/1250000000000 : ℝ)*(f.sum) + (43824347521/4320000000000000000000000 : ℝ)*base65 + (724582778200039/108000000000000000000000000000 : ℝ)*base67 + (466913660164039/108000000000000000000000000000 : ℝ)*base69 + (2620910409424039/108000000000000000000000000000 : ℝ)*base71 + (77034847729/108000000000000000000000000 : ℝ)*base73 + (1920700343719961/108000000000000000000000000000 : ℝ)*base76 + (1771260948088039/108000000000000000000000000000 : ℝ)*base77 + (295202880232039/108000000000000000000000000000 : ℝ)*base79 + (357191501449/108000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4115511/10000000000000000000000 : ℝ)*base90 + (4115511/10000000000000000000000 : ℝ)*base92 + (4115511/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15248120478528066238516889/4050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24169123/50000000000000 : ℝ)*(base19) + (268111269/50000000000000 : ℝ)*(base23) + (7447527/50000000000000 : ℝ)*(upper3) + (64906477/100000000000000 : ℝ)*(lower4) + (5907818550193267/100000000000000 : ℝ)*(major0) + (5907818550193267/100000000000000 : ℝ)*(major1) + (5907818550193267/100000000000000 : ℝ)*(major2) + (6065931007/100000000000000 : ℝ)*(sp1) + (4856780343/25000000000000 : ℝ)*(sp2) + (13907489/4000000000000 : ℝ)*(sp3) + (7904639014651347/100000000000000 : ℝ)*(sp4) + (3952316450191047/50000000000000 : ℝ)*(sp5) + (3952309525653719/50000000000000 : ℝ)*(sp6) + (1955498806274511/50000000000000 : ℝ)*(sp7) + (3910997960236247/100000000000000 : ℝ)*(f.failure) + (7904639014651347/100000000000000 : ℝ)*(f.sum) + (33119510916517/4860000000000000000000000000 : ℝ)*base66 + (421398731495413537/24300000000000000000000000000000 : ℝ)*base67 + (5506626867913537/24300000000000000000000000000000 : ℝ)*base69 + (196488739989613537/24300000000000000000000000000000 : ℝ)*base71 + (1096644121823/4860000000000000000000000000 : ℝ)*base73 + (199207762051213537/24300000000000000000000000000000 : ℝ)*base75 + (13501178200513537/24300000000000000000000000000000 : ℝ)*base77 + (24280021710613537/24300000000000000000000000000000 : ℝ)*base79 + (29267801693197/4860000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3468397/10000000000000000000000 : ℝ)*base90 + (3468397/10000000000000000000000 : ℝ)*base92 + (3468397/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1223_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1223_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1223_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1223_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1223_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1223_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
