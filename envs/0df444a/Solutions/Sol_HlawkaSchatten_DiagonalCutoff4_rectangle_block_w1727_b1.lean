-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1727_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:01:28.453678+00:00
-- url     : https://prove2.me/submissions/c1b955ae-d454-4a2e-893d-f5d14ffcd59e

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
theorem support_rectangle_w1727_s3_0 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1352948647/10000000000 : ℝ)*x 0 + (682424459/1250000000 : ℝ)*x 1 + (5140101257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352948647/10000000000 : ℝ)^5439 ≤ (4253668839841/50000000000000 : ℝ)^4415 := by
    have hnat : (1352948647 : ℕ)^5439*50000000000000^4415 ≤ 4253668839841^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352948647 10000000000 4253668839841 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682424459/1250000000 : ℝ)^5439 ≤ (47443725222051/100000000000000 : ℝ)^4415 := by
    have hnat : (682424459 : ℕ)^5439*100000000000000^4415 ≤ 47443725222051^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682424459 1250000000 47443725222051 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140101257/10000000000 : ℝ)^5439 ≤ (22024468537841/50000000000000 : ℝ)^4415 := by
    have hnat : (5140101257 : ℕ)^5439*50000000000000^4415 ≤ 22024468537841^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140101257 10000000000 22024468537841 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1352948647/10000000000 : ℝ), (682424459/1250000000 : ℝ), (5140101257/10000000000 : ℝ)] ![(4253668839841/50000000000000 : ℝ), (47443725222051/100000000000000 : ℝ), (22024468537841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1352948647/10000000000 : ℝ)|^5439 ≤ (4253668839841/50000000000000 : ℝ)^4415
        have hw : |(-1352948647/10000000000 : ℝ)|=(1352948647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682424459/1250000000 : ℝ)|^5439 ≤ (47443725222051/100000000000000 : ℝ)^4415
        have hw : |(682424459/1250000000 : ℝ)|=(682424459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140101257/10000000000 : ℝ)|^5439 ≤ (22024468537841/50000000000000 : ℝ)^4415
        have hw : |(5140101257/10000000000 : ℝ)|=(5140101257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_1 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337801409/10000000000 : ℝ)*x 0 + (-151828713/1000000000 : ℝ)*x 1 + (5140101257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337801409/10000000000 : ℝ)^5439 ≤ (23072666390139/50000000000000 : ℝ)^4415 := by
    have hnat : (5337801409 : ℕ)^5439*50000000000000^4415 ≤ 23072666390139^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337801409 10000000000 23072666390139 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151828713/1000000000 : ℝ)^5439 ≤ (612858133199/6250000000000 : ℝ)^4415 := by
    have hnat : (151828713 : ℕ)^5439*6250000000000^4415 ≤ 612858133199^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151828713 1000000000 612858133199 6250000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140101257/10000000000 : ℝ)^5439 ≤ (22024468537841/50000000000000 : ℝ)^4415 := by
    have hnat : (5140101257 : ℕ)^5439*50000000000000^4415 ≤ 22024468537841^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140101257 10000000000 22024468537841 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337801409/10000000000 : ℝ), (-151828713/1000000000 : ℝ), (5140101257/10000000000 : ℝ)] ![(23072666390139/50000000000000 : ℝ), (612858133199/6250000000000 : ℝ), (22024468537841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337801409/10000000000 : ℝ)|^5439 ≤ (23072666390139/50000000000000 : ℝ)^4415
        have hw : |(5337801409/10000000000 : ℝ)|=(5337801409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-151828713/1000000000 : ℝ)|^5439 ≤ (612858133199/6250000000000 : ℝ)^4415
        have hw : |(-151828713/1000000000 : ℝ)|=(151828713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140101257/10000000000 : ℝ)|^5439 ≤ (22024468537841/50000000000000 : ℝ)^4415
        have hw : |(5140101257/10000000000 : ℝ)|=(5140101257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_2 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83403147/156250000 : ℝ)*x 0 + (642512657/1250000000 : ℝ)*x 1 + (-379571783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83403147/156250000 : ℝ)^5439 ≤ (11536333192407/25000000000000 : ℝ)^4415 := by
    have hnat : (83403147 : ℕ)^5439*25000000000000^4415 ≤ 11536333192407^4415*156250000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83403147 156250000 11536333192407 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642512657/1250000000 : ℝ)^5439 ≤ (352391496521/800000000000 : ℝ)^4415 := by
    have hnat : (642512657 : ℕ)^5439*800000000000^4415 ≤ 352391496521^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642512657 1250000000 352391496521 800000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379571783/2500000000 : ℝ)^5439 ≤ (1225716268387/12500000000000 : ℝ)^4415 := by
    have hnat : (379571783 : ℕ)^5439*12500000000000^4415 ≤ 1225716268387^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379571783 2500000000 1225716268387 12500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83403147/156250000 : ℝ), (642512657/1250000000 : ℝ), (-379571783/2500000000 : ℝ)] ![(11536333192407/25000000000000 : ℝ), (352391496521/800000000000 : ℝ), (1225716268387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83403147/156250000 : ℝ)|^5439 ≤ (11536333192407/25000000000000 : ℝ)^4415
        have hw : |(83403147/156250000 : ℝ)|=(83403147/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642512657/1250000000 : ℝ)|^5439 ≤ (352391496521/800000000000 : ℝ)^4415
        have hw : |(642512657/1250000000 : ℝ)|=(642512657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379571783/2500000000 : ℝ)|^5439 ≤ (1225716268387/12500000000000 : ℝ)^4415
        have hw : |(-379571783/2500000000 : ℝ)|=(379571783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_3 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083471531/10000000000 : ℝ)*x 0 + (3619769129/10000000000 : ℝ)*x 1 + (2290728621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083471531/10000000000 : ℝ)^5439 ≤ (33175161991201/100000000000000 : ℝ)^4415 := by
    have hnat : (4083471531 : ℕ)^5439*100000000000000^4415 ≤ 33175161991201^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083471531 10000000000 33175161991201 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3619769129/10000000000 : ℝ)^5439 ≤ (1787322160137/6250000000000 : ℝ)^4415 := by
    have hnat : (3619769129 : ℕ)^5439*6250000000000^4415 ≤ 1787322160137^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619769129 10000000000 1787322160137 6250000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2290728621/5000000000 : ℝ)^5439 ≤ (764553668581/2000000000000 : ℝ)^4415 := by
    have hnat : (2290728621 : ℕ)^5439*2000000000000^4415 ≤ 764553668581^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290728621 5000000000 764553668581 2000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083471531/10000000000 : ℝ), (3619769129/10000000000 : ℝ), (2290728621/5000000000 : ℝ)] ![(33175161991201/100000000000000 : ℝ), (1787322160137/6250000000000 : ℝ), (764553668581/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083471531/10000000000 : ℝ)|^5439 ≤ (33175161991201/100000000000000 : ℝ)^4415
        have hw : |(4083471531/10000000000 : ℝ)|=(4083471531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3619769129/10000000000 : ℝ)|^5439 ≤ (1787322160137/6250000000000 : ℝ)^4415
        have hw : |(3619769129/10000000000 : ℝ)|=(3619769129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2290728621/5000000000 : ℝ)|^5439 ≤ (764553668581/2000000000000 : ℝ)^4415
        have hw : |(2290728621/5000000000 : ℝ)|=(2290728621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_4 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-270618097/2000000000 : ℝ)*x 0 + (514368987/1000000000 : ℝ)*x 1 + (5455753673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270618097/2000000000 : ℝ)^5439 ≤ (8508436428923/100000000000000 : ℝ)^4415 := by
    have hnat : (270618097 : ℕ)^5439*100000000000000^4415 ≤ 8508436428923^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270618097 2000000000 8508436428923 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514368987/1000000000 : ℝ)^5439 ≤ (4408682614087/10000000000000 : ℝ)^4415 := by
    have hnat : (514368987 : ℕ)^5439*10000000000000^4415 ≤ 4408682614087^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514368987 1000000000 4408682614087 10000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455753673/10000000000 : ℝ)^5439 ≤ (23702368708829/50000000000000 : ℝ)^4415 := by
    have hnat : (5455753673 : ℕ)^5439*50000000000000^4415 ≤ 23702368708829^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455753673 10000000000 23702368708829 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270618097/2000000000 : ℝ), (514368987/1000000000 : ℝ), (5455753673/10000000000 : ℝ)] ![(8508436428923/100000000000000 : ℝ), (4408682614087/10000000000000 : ℝ), (23702368708829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270618097/2000000000 : ℝ)|^5439 ≤ (8508436428923/100000000000000 : ℝ)^4415
        have hw : |(-270618097/2000000000 : ℝ)|=(270618097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514368987/1000000000 : ℝ)|^5439 ≤ (4408682614087/10000000000000 : ℝ)^4415
        have hw : |(514368987/1000000000 : ℝ)|=(514368987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455753673/10000000000 : ℝ)|^5439 ≤ (23702368708829/50000000000000 : ℝ)^4415
        have hw : |(5455753673/10000000000 : ℝ)|=(5455753673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_5 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525234099/1000000000 : ℝ)*x 0 + (-1202634743/10000000000 : ℝ)*x 1 + (340984603/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525234099/1000000000 : ℝ)^5439 ≤ (45236867572131/100000000000000 : ℝ)^4415 := by
    have hnat : (525234099 : ℕ)^5439*100000000000000^4415 ≤ 45236867572131^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525234099 1000000000 45236867572131 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202634743/10000000000 : ℝ)^5439 ≤ (7358395272353/100000000000000 : ℝ)^4415 := by
    have hnat : (1202634743 : ℕ)^5439*100000000000000^4415 ≤ 7358395272353^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202634743 10000000000 7358395272353 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340984603/625000000 : ℝ)^5439 ≤ (11851184287513/25000000000000 : ℝ)^4415 := by
    have hnat : (340984603 : ℕ)^5439*25000000000000^4415 ≤ 11851184287513^4415*625000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340984603 625000000 11851184287513 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525234099/1000000000 : ℝ), (-1202634743/10000000000 : ℝ), (340984603/625000000 : ℝ)] ![(45236867572131/100000000000000 : ℝ), (7358395272353/100000000000000 : ℝ), (11851184287513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525234099/1000000000 : ℝ)|^5439 ≤ (45236867572131/100000000000000 : ℝ)^4415
        have hw : |(525234099/1000000000 : ℝ)|=(525234099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1202634743/10000000000 : ℝ)|^5439 ≤ (7358395272353/100000000000000 : ℝ)^4415
        have hw : |(-1202634743/10000000000 : ℝ)|=(1202634743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340984603/625000000 : ℝ)|^5439 ≤ (11851184287513/25000000000000 : ℝ)^4415
        have hw : |(340984603/625000000 : ℝ)|=(340984603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_6 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252340971/10000000000 : ℝ)*x 0 + (1363938423/2500000000 : ℝ)*x 1 + (-1202634707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252340971/10000000000 : ℝ)^5439 ≤ (9047373474107/20000000000000 : ℝ)^4415 := by
    have hnat : (5252340971 : ℕ)^5439*20000000000000^4415 ≤ 9047373474107^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252340971 10000000000 9047373474107 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363938423/2500000000 : ℝ)^5439 ≤ (23702368810519/50000000000000 : ℝ)^4415 := by
    have hnat : (1363938423 : ℕ)^5439*50000000000000^4415 ≤ 23702368810519^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363938423 2500000000 23702368810519 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202634707/10000000000 : ℝ)^5439 ≤ (1839598750249/25000000000000 : ℝ)^4415 := by
    have hnat : (1202634707 : ℕ)^5439*25000000000000^4415 ≤ 1839598750249^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202634707 10000000000 1839598750249 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252340971/10000000000 : ℝ), (1363938423/2500000000 : ℝ), (-1202634707/10000000000 : ℝ)] ![(9047373474107/20000000000000 : ℝ), (23702368810519/50000000000000 : ℝ), (1839598750249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252340971/10000000000 : ℝ)|^5439 ≤ (9047373474107/20000000000000 : ℝ)^4415
        have hw : |(5252340971/10000000000 : ℝ)|=(5252340971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363938423/2500000000 : ℝ)|^5439 ≤ (23702368810519/50000000000000 : ℝ)^4415
        have hw : |(1363938423/2500000000 : ℝ)|=(1363938423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1202634707/10000000000 : ℝ)|^5439 ≤ (1839598750249/25000000000000 : ℝ)^4415
        have hw : |(-1202634707/10000000000 : ℝ)|=(1202634707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s3_7 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (510487341/1250000000 : ℝ)*x 0 + (4570648599/10000000000 : ℝ)*x 1 + (726147713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510487341/1250000000 : ℝ)^5439 ≤ (16589718836287/50000000000000 : ℝ)^4415 := by
    have hnat : (510487341 : ℕ)^5439*50000000000000^4415 ≤ 16589718836287^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510487341 1250000000 16589718836287 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570648599/10000000000 : ℝ)^5439 ≤ (19058304388913/50000000000000 : ℝ)^4415 := by
    have hnat : (4570648599 : ℕ)^5439*50000000000000^4415 ≤ 19058304388913^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570648599 10000000000 19058304388913 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (726147713/2000000000 : ℝ)^5439 ≤ (112124818501/390625000000 : ℝ)^4415 := by
    have hnat : (726147713 : ℕ)^5439*390625000000^4415 ≤ 112124818501^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726147713 2000000000 112124818501 390625000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(510487341/1250000000 : ℝ), (4570648599/10000000000 : ℝ), (726147713/2000000000 : ℝ)] ![(16589718836287/50000000000000 : ℝ), (19058304388913/50000000000000 : ℝ), (112124818501/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(510487341/1250000000 : ℝ)|^5439 ≤ (16589718836287/50000000000000 : ℝ)^4415
        have hw : |(510487341/1250000000 : ℝ)|=(510487341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570648599/10000000000 : ℝ)|^5439 ≤ (19058304388913/50000000000000 : ℝ)^4415
        have hw : |(4570648599/10000000000 : ℝ)|=(4570648599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(726147713/2000000000 : ℝ)|^5439 ≤ (112124818501/390625000000 : ℝ)^4415
        have hw : |(726147713/2000000000 : ℝ)|=(726147713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1727_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2027/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16971/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10129/100000 : ℝ) ^ (5431/1024 : ℝ) ≤ (132969659111673/25000000000000000000 : ℝ) := by
    have hpowers : (10129/100000 : ℝ)^5431 ≤ (132969659111673/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10129 : ℕ)^5431*25000000000000000000^1024 ≤ 132969659111673^1024*100000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10129 100000 132969659111673 25000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10129/100000 : ℝ)) (X := (132969659111673/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16977/100000 : ℝ) ^ (5431/1024 : ℝ) ≤ (8230099580003741/100000000000000000000 : ℝ) := by
    have hpowers : (16977/100000 : ℝ)^5431 ≤ (8230099580003741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16977 : ℕ)^5431*100000000000000000000^1024 ≤ 8230099580003741^1024*100000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16977 100000 8230099580003741 100000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16977/100000 : ℝ)) (X := (8230099580003741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500132969659111673/12500000000000000000 : ℝ) ≤ (2500005014190509/2500000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (12500132969659111673/12500000000000000000 : ℝ)^1024 ≤ (2500005014190509/2500000000000000 : ℝ)^5431 := by
      have hnat : (12500132969659111673 : ℕ)^1024*2500000000000000^5431 ≤ 2500005014190509^5431*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500132969659111673 12500000000000000000 2500005014190509 2500000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500005014190509/2500000000000000 : ℝ)) (X := (12500132969659111673/12500000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008761978216450433/100000000000000000000 : ℝ) ≤ (2500041299699639/2500000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (100008761978216450433/100000000000000000000 : ℝ)^1024 ≤ (2500041299699639/2500000000000000 : ℝ)^5431 := by
      have hnat : (100008761978216450433 : ℕ)^1024*2500000000000000^5431 ≤ 2500041299699639^5431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008761978216450433 100000000000000000000 2500041299699639 2500000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500041299699639/2500000000000000 : ℝ)) (X := (100008761978216450433/100000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008230099580003741/50000000000000000000 : ℝ) ≤ (2500077585208769/2500000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (50008230099580003741/50000000000000000000 : ℝ)^1024 ≤ (2500077585208769/2500000000000000 : ℝ)^5431 := by
      have hnat : (50008230099580003741 : ℕ)^1024*2500000000000000^5431 ≤ 2500077585208769^5431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008230099580003741 50000000000000000000 2500077585208769 2500000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500077585208769/2500000000000000 : ℝ)) (X := (50008230099580003741/50000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(132969659111673/25000000000000000000 : ℝ) ≤ ((4279824816333162523/4280000000000000000 : ℝ)+2*(3628550913/17120000000000 : ℝ)*(10129/100000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (4279824816333162523/4280000000000000000 : ℝ)+2*(3628550913/17120000000000 : ℝ)*(10129/100000 : ℝ)=(2500005014190509/2500000000000000 : ℝ) by norm_num, show 1+2*(132969659111673/25000000000000000000 : ℝ)=(12500132969659111673/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8230099580003741/100000000000000000000 : ℝ)+(132969659111673/25000000000000000000 : ℝ) ≤ ((4279824816333162523/4280000000000000000 : ℝ)+(3628550913/17120000000000 : ℝ)*((16977/100000 : ℝ)+(10129/100000 : ℝ)))^(5431/1024 : ℝ) := by
    rw [show (4279824816333162523/4280000000000000000 : ℝ)+(3628550913/17120000000000 : ℝ)*((16977/100000 : ℝ)+(10129/100000 : ℝ))=(2500041299699639/2500000000000000 : ℝ) by norm_num, show 1+(8230099580003741/100000000000000000000 : ℝ)+(132969659111673/25000000000000000000 : ℝ)=(100008761978216450433/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8230099580003741/100000000000000000000 : ℝ) ≤ ((4279824816333162523/4280000000000000000 : ℝ)+2*(3628550913/17120000000000 : ℝ)*(16977/100000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (4279824816333162523/4280000000000000000 : ℝ)+2*(3628550913/17120000000000 : ℝ)*(16977/100000 : ℝ)=(2500077585208769/2500000000000000 : ℝ) by norm_num, show 1+2*(8230099580003741/100000000000000000000 : ℝ)=(50008230099580003741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4279824816333162523/4280000000000000000 : ℝ)*(X 1 0+X 2 0)+(3628550913/17120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (10129/100000 : ℝ)) (hi := (16977/100000 : ℝ)) (c := (4279824816333162523/4280000000000000000 : ℝ)) (alpha := (3628550913/17120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4279824816333162523/4280000000000000000 : ℝ)*(X 0 1+X 2 1)+(3628550913/17120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (10129/100000 : ℝ)) (hi := (16977/100000 : ℝ)) (c := (4279824816333162523/4280000000000000000 : ℝ)) (alpha := (3628550913/17120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4279824816333162523/4280000000000000000 : ℝ)*(X 0 2+X 1 2)+(3628550913/17120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (10129/100000 : ℝ)) (hi := (16977/100000 : ℝ)) (c := (4279824816333162523/4280000000000000000 : ℝ)) (alpha := (3628550913/17120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1352948647/10000000000 : ℝ)*X 0 0+(682424459/1250000000 : ℝ)*X 0 1+(5140101257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5337801409/10000000000 : ℝ)*X 1 0+(-151828713/1000000000 : ℝ)*X 1 1+(5140101257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83403147/156250000 : ℝ)*X 2 0+(642512657/1250000000 : ℝ)*X 2 1+(-379571783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4083471531/10000000000 : ℝ)*X 0 0+(3619769129/10000000000 : ℝ)*X 0 1+(2290728621/5000000000 : ℝ)*X 0 2+(4083471531/10000000000 : ℝ)*X 1 0+(3619769129/10000000000 : ℝ)*X 1 1+(2290728621/5000000000 : ℝ)*X 1 2+(4083471531/10000000000 : ℝ)*X 2 0+(3619769129/10000000000 : ℝ)*X 2 1+(2290728621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270618097/2000000000 : ℝ)*X 0 0+(514368987/1000000000 : ℝ)*X 0 1+(5455753673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525234099/1000000000 : ℝ)*X 1 0+(-1202634743/10000000000 : ℝ)*X 1 1+(340984603/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252340971/10000000000 : ℝ)*X 2 0+(1363938423/2500000000 : ℝ)*X 2 1+(-1202634707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((510487341/1250000000 : ℝ)*X 0 0+(4570648599/10000000000 : ℝ)*X 0 1+(726147713/2000000000 : ℝ)*X 0 2+(510487341/1250000000 : ℝ)*X 1 0+(4570648599/10000000000 : ℝ)*X 1 1+(726147713/2000000000 : ℝ)*X 1 2+(510487341/1250000000 : ℝ)*X 2 0+(4570648599/10000000000 : ℝ)*X 2 1+(726147713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1848294398432854135011/428000000000000000000000000 : ℝ) := by norm_num
    linear_combination (312131639/50000000000000 : ℝ)*(base19) + (587573309/100000000000000 : ℝ)*(base23) + (3854237/20000000000000 : ℝ)*(lower2) + (104714157/100000000000000 : ℝ)*(upper3) + (38873381/50000000000000 : ℝ)*(upper5) + (1042940250145653/50000000000000 : ℝ)*(major0) + (1042940250145653/50000000000000 : ℝ)*(major1) + (1042940250145653/50000000000000 : ℝ)*(major2) + (195744508316983/6250000000000 : ℝ)*(sp0) + (1565958901401749/50000000000000 : ℝ)*(sp1) + (1565958919746733/50000000000000 : ℝ)*(sp2) + (1039840162205089/100000000000000 : ℝ)*(sp3) + (6293995047/100000000000000 : ℝ)*(sp4) + (1133681289/50000000000000 : ℝ)*(sp7) + (259960607391917/25000000000000 : ℝ)*(f.failure) + (125276737082671/4000000000000 : ℝ)*(f.sum) + (2419094855893/428000000000000000000000000 : ℝ)*base65 + (577837355457787481/214000000000000000000000000000000 : ℝ)*base68 + (1076107862978212519/214000000000000000000000000000000 : ℝ)*base69 + (335651397481787481/214000000000000000000000000000000 : ℝ)*base72 + (43387011481/17120000000000000000000000 : ℝ)*base73 + (1559468470447787481/214000000000000000000000000000000 : ℝ)*base76 + (724275313074212519/214000000000000000000000000000000 : ℝ)*base77 + (278685191882212519/214000000000000000000000000000000 : ℝ)*base79 + (2673582216101/428000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1557861/100000000000000000000 : ℝ)*base89 + (1557861/100000000000000000000 : ℝ)*base91 + (1557861/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2877770832424951200172200717/214000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (903973621/50000000000000 : ℝ)*(base19) + (966712713/50000000000000 : ℝ)*(base23) + (106170579/20000000000000 : ℝ)*(lower1) + (7067793/2500000000000 : ℝ)*(upper3) + (59668291/100000000000000 : ℝ)*(lower4) + (283497267/100000000000000 : ℝ)*(upper5) + (2134190650052707/100000000000000 : ℝ)*(major0) + (2134190650052707/100000000000000 : ℝ)*(major1) + (2134190650052707/100000000000000 : ℝ)*(major2) + (90141149/6250000000000 : ℝ)*(sp2) + (3204455094649549/100000000000000 : ℝ)*(sp4) + (3204453286702307/100000000000000 : ℝ)*(sp5) + (1602225859482869/50000000000000 : ℝ)*(sp6) + (26598143930123/2500000000000 : ℝ)*(sp7) + (26598143930123/2500000000000 : ℝ)*(f.failure) + (3204455094649549/100000000000000 : ℝ)*(f.sum) + (1698096147771/856000000000000000000000000 : ℝ)*base65 + (11880136220939849761/428000000000000000000000000000000 : ℝ)*base67 + (926911017736150239/428000000000000000000000000000000 : ℝ)*base70 + (52603809789499849761/428000000000000000000000000000000 : ℝ)*base71 + (4269901509467/856000000000000000000000000 : ℝ)*base73 + (57294820230188150239/428000000000000000000000000000000 : ℝ)*base76 + (2410541067979849761/428000000000000000000000000000000 : ℝ)*base77 + (4947149814579849761/428000000000000000000000000000000 : ℝ)*base79 + (872623292137/171200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (78541/10000000000000000000 : ℝ)*base90 + (78541/10000000000000000000 : ℝ)*base92 + (78541/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1727_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2027/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16971/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1727_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1727_s4_0 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133444979/250000000 : ℝ)*x 0 + (257005417/500000000 : ℝ)*x 1 + (-1518280743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133444979/250000000 : ℝ)^5439 ≤ (23072654414101/50000000000000 : ℝ)^4415 := by
    have hnat : (133444979 : ℕ)^5439*50000000000000^4415 ≤ 23072654414101^4415*250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133444979 250000000 23072654414101 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257005417/500000000 : ℝ)^5439 ≤ (1101225296323/2500000000000 : ℝ)^4415 := by
    have hnat : (257005417 : ℕ)^5439*2500000000000^4415 ≤ 1101225296323^4415*500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257005417 500000000 1101225296323 2500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518280743/10000000000 : ℝ)^5439 ≤ (9805679313943/100000000000000 : ℝ)^4415 := by
    have hnat : (1518280743 : ℕ)^5439*100000000000000^4415 ≤ 9805679313943^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518280743 10000000000 9805679313943 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133444979/250000000 : ℝ), (257005417/500000000 : ℝ), (-1518280743/10000000000 : ℝ)] ![(23072654414101/50000000000000 : ℝ), (1101225296323/2500000000000 : ℝ), (9805679313943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133444979/250000000 : ℝ)|^5439 ≤ (23072654414101/50000000000000 : ℝ)^4415
        have hw : |(133444979/250000000 : ℝ)|=(133444979/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257005417/500000000 : ℝ)|^5439 ≤ (1101225296323/2500000000000 : ℝ)^4415
        have hw : |(257005417/500000000 : ℝ)|=(257005417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1518280743/10000000000 : ℝ)|^5439 ≤ (9805679313943/100000000000000 : ℝ)^4415
        have hw : |(-1518280743/10000000000 : ℝ)|=(1518280743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s4_1 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338273071/2500000000 : ℝ)*x 0 + (514369661/1000000000 : ℝ)*x 1 + (5455745723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338273071/2500000000 : ℝ)^5439 ≤ (8508450365063/100000000000000 : ℝ)^4415 := by
    have hnat : (338273071 : ℕ)^5439*100000000000000^4415 ≤ 8508450365063^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338273071 2500000000 8508450365063 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514369661/1000000000 : ℝ)^5439 ≤ (44086897308479/100000000000000 : ℝ)^4415 := by
    have hnat : (514369661 : ℕ)^5439*100000000000000^4415 ≤ 44086897308479^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514369661 1000000000 44086897308479 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455745723/10000000000 : ℝ)^5439 ≤ (47404652319061/100000000000000 : ℝ)^4415 := by
    have hnat : (5455745723 : ℕ)^5439*100000000000000^4415 ≤ 47404652319061^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455745723 10000000000 47404652319061 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338273071/2500000000 : ℝ), (514369661/1000000000 : ℝ), (5455745723/10000000000 : ℝ)] ![(8508450365063/100000000000000 : ℝ), (44086897308479/100000000000000 : ℝ), (47404652319061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338273071/2500000000 : ℝ)|^5439 ≤ (8508450365063/100000000000000 : ℝ)^4415
        have hw : |(-338273071/2500000000 : ℝ)|=(338273071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514369661/1000000000 : ℝ)|^5439 ≤ (44086897308479/100000000000000 : ℝ)^4415
        have hw : |(514369661/1000000000 : ℝ)|=(514369661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455745723/10000000000 : ℝ)|^5439 ≤ (47404652319061/100000000000000 : ℝ)^4415
        have hw : |(5455745723/10000000000 : ℝ)|=(5455745723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s4_2 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626171449/5000000000 : ℝ)*x 0 + (-1202643343/10000000000 : ℝ)*x 1 + (54557457/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626171449/5000000000 : ℝ)^5439 ≤ (22618443908299/50000000000000 : ℝ)^4415 := by
    have hnat : (2626171449 : ℕ)^5439*50000000000000^4415 ≤ 22618443908299^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626171449 5000000000 22618443908299 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202643343/10000000000 : ℝ)^5439 ≤ (3679230048229/50000000000000 : ℝ)^4415 := by
    have hnat : (1202643343 : ℕ)^5439*50000000000000^4415 ≤ 3679230048229^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202643343 10000000000 3679230048229 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54557457/100000000 : ℝ)^5439 ≤ (1481395377277/3125000000000 : ℝ)^4415 := by
    have hnat : (54557457 : ℕ)^5439*3125000000000^4415 ≤ 1481395377277^4415*100000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54557457 100000000 1481395377277 3125000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626171449/5000000000 : ℝ), (-1202643343/10000000000 : ℝ), (54557457/100000000 : ℝ)] ![(22618443908299/50000000000000 : ℝ), (3679230048229/50000000000000 : ℝ), (1481395377277/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626171449/5000000000 : ℝ)|^5439 ≤ (22618443908299/50000000000000 : ℝ)^4415
        have hw : |(2626171449/5000000000 : ℝ)|=(2626171449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1202643343/10000000000 : ℝ)|^5439 ≤ (3679230048229/50000000000000 : ℝ)^4415
        have hw : |(-1202643343/10000000000 : ℝ)|=(1202643343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54557457/100000000 : ℝ)|^5439 ≤ (1481395377277/3125000000000 : ℝ)^4415
        have hw : |(54557457/100000000 : ℝ)|=(54557457/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s4_3 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626171437/5000000000 : ℝ)*x 0 + (136393643/250000000 : ℝ)*x 1 + (-300660837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626171437/5000000000 : ℝ)^5439 ≤ (45236887561951/100000000000000 : ℝ)^4415 := by
    have hnat : (2626171437 : ℕ)^5439*100000000000000^4415 ≤ 45236887561951^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626171437 5000000000 45236887561951 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136393643/250000000 : ℝ)^5439 ≤ (47404652286949/100000000000000 : ℝ)^4415 := by
    have hnat : (136393643 : ℕ)^5439*100000000000000^4415 ≤ 47404652286949^4415*250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136393643 250000000 47404652286949 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300660837/2500000000 : ℝ)^5439 ≤ (3679230067073/50000000000000 : ℝ)^4415 := by
    have hnat : (300660837 : ℕ)^5439*50000000000000^4415 ≤ 3679230067073^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300660837 2500000000 3679230067073 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626171437/5000000000 : ℝ), (136393643/250000000 : ℝ), (-300660837/2500000000 : ℝ)] ![(45236887561951/100000000000000 : ℝ), (47404652286949/100000000000000 : ℝ), (3679230067073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626171437/5000000000 : ℝ)|^5439 ≤ (45236887561951/100000000000000 : ℝ)^4415
        have hw : |(2626171437/5000000000 : ℝ)|=(2626171437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136393643/250000000 : ℝ)|^5439 ≤ (47404652286949/100000000000000 : ℝ)^4415
        have hw : |(136393643/250000000 : ℝ)|=(136393643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300660837/2500000000 : ℝ)|^5439 ≤ (3679230067073/50000000000000 : ℝ)^4415
        have hw : |(-300660837/2500000000 : ℝ)|=(300660837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s4_4 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083900203/10000000000 : ℝ)*x 0 + (457062637/1000000000 : ℝ)*x 1 + (3630760497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083900203/10000000000 : ℝ)^5439 ≤ (2073715777223/6250000000000 : ℝ)^4415 := by
    have hnat : (4083900203 : ℕ)^5439*6250000000000^4415 ≤ 2073715777223^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083900203 10000000000 2073715777223 6250000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457062637/1000000000 : ℝ)^5439 ≤ (19058190202493/50000000000000 : ℝ)^4415 := by
    have hnat : (457062637 : ℕ)^5439*50000000000000^4415 ≤ 19058190202493^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457062637 1000000000 19058190202493 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3630760497/10000000000 : ℝ)^5439 ≤ (28704167142347/100000000000000 : ℝ)^4415 := by
    have hnat : (3630760497 : ℕ)^5439*100000000000000^4415 ≤ 28704167142347^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3630760497 10000000000 28704167142347 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083900203/10000000000 : ℝ), (457062637/1000000000 : ℝ), (3630760497/10000000000 : ℝ)] ![(2073715777223/6250000000000 : ℝ), (19058190202493/50000000000000 : ℝ), (28704167142347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083900203/10000000000 : ℝ)|^5439 ≤ (2073715777223/6250000000000 : ℝ)^4415
        have hw : |(4083900203/10000000000 : ℝ)|=(4083900203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457062637/1000000000 : ℝ)|^5439 ≤ (19058190202493/50000000000000 : ℝ)^4415
        have hw : |(457062637/1000000000 : ℝ)|=(457062637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3630760497/10000000000 : ℝ)|^5439 ≤ (28704167142347/100000000000000 : ℝ)^4415
        have hw : |(3630760497/10000000000 : ℝ)|=(3630760497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1727_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2027/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2027/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1697/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2027/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2027/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2027/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2027/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2027/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2027/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2027/20000 : ℝ) ^ (5431/1024 : ℝ) ≤ (66693971275917/12500000000000000000 : ℝ) := by
    have hpowers : (2027/20000 : ℝ)^5431 ≤ (66693971275917/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2027 : ℕ)^5431*12500000000000000000^1024 ≤ 66693971275917^1024*20000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2027 20000 66693971275917 12500000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2027/20000 : ℝ)) (X := (66693971275917/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16971/100000 : ℝ) ^ (5431/1024 : ℝ) ≤ (4107342264665373/50000000000000000000 : ℝ) := by
    have hpowers : (16971/100000 : ℝ)^5431 ≤ (4107342264665373/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16971 : ℕ)^5431*50000000000000000000^1024 ≤ 4107342264665373^1024*100000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16971 100000 4107342264665373 50000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16971/100000 : ℝ)) (X := (4107342264665373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250066693971275917/6250000000000000000 : ℝ) ≤ (5000010059927219/5000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (6250066693971275917/6250000000000000000 : ℝ)^1024 ≤ (5000010059927219/5000000000000000 : ℝ)^5431 := by
      have hnat : (6250066693971275917 : ℕ)^1024*5000000000000000^5431 ≤ 5000010059927219^5431*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250066693971275917 6250000000000000000 5000010059927219 5000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010059927219/5000000000000000 : ℝ)) (X := (6250066693971275917/6250000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004374118149769041/50000000000000000000 : ℝ) ≤ (10000164939716927/10000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (50004374118149769041/50000000000000000000 : ℝ)^1024 ≤ (10000164939716927/10000000000000000 : ℝ)^5431 := by
      have hnat : (50004374118149769041 : ℕ)^1024*10000000000000000^5431 ≤ 10000164939716927^5431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004374118149769041 50000000000000000000 10000164939716927 10000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000164939716927/10000000000000000 : ℝ)) (X := (50004374118149769041/50000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004107342264665373/25000000000000000000 : ℝ) ≤ (1250038719947427/1250000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (25004107342264665373/25000000000000000000 : ℝ)^1024 ≤ (1250038719947427/1250000000000000 : ℝ)^5431 := by
      have hnat : (25004107342264665373 : ℕ)^1024*1250000000000000^5431 ≤ 1250038719947427^5431*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004107342264665373 25000000000000000000 1250038719947427 1250000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250038719947427/1250000000000000 : ℝ)) (X := (25004107342264665373/25000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(66693971275917/12500000000000000000 : ℝ) ≤ ((34178601020356143069/34180000000000000000 : ℝ)+2*(144819862489/683600000000000 : ℝ)*(2027/20000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (34178601020356143069/34180000000000000000 : ℝ)+2*(144819862489/683600000000000 : ℝ)*(2027/20000 : ℝ)=(5000010059927219/5000000000000000 : ℝ) by norm_num, show 1+2*(66693971275917/12500000000000000000 : ℝ)=(6250066693971275917/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4107342264665373/50000000000000000000 : ℝ)+(66693971275917/12500000000000000000 : ℝ) ≤ ((34178601020356143069/34180000000000000000 : ℝ)+(144819862489/683600000000000 : ℝ)*((16971/100000 : ℝ)+(2027/20000 : ℝ)))^(5431/1024 : ℝ) := by
    rw [show (34178601020356143069/34180000000000000000 : ℝ)+(144819862489/683600000000000 : ℝ)*((16971/100000 : ℝ)+(2027/20000 : ℝ))=(10000164939716927/10000000000000000 : ℝ) by norm_num, show 1+(4107342264665373/50000000000000000000 : ℝ)+(66693971275917/12500000000000000000 : ℝ)=(50004374118149769041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4107342264665373/50000000000000000000 : ℝ) ≤ ((34178601020356143069/34180000000000000000 : ℝ)+2*(144819862489/683600000000000 : ℝ)*(16971/100000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (34178601020356143069/34180000000000000000 : ℝ)+2*(144819862489/683600000000000 : ℝ)*(16971/100000 : ℝ)=(1250038719947427/1250000000000000 : ℝ) by norm_num, show 1+2*(4107342264665373/50000000000000000000 : ℝ)=(25004107342264665373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34178601020356143069/34180000000000000000 : ℝ)*(X 1 0+X 2 0)+(144819862489/683600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (2027/20000 : ℝ)) (hi := (16971/100000 : ℝ)) (c := (34178601020356143069/34180000000000000000 : ℝ)) (alpha := (144819862489/683600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34178601020356143069/34180000000000000000 : ℝ)*(X 0 1+X 2 1)+(144819862489/683600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (2027/20000 : ℝ)) (hi := (16971/100000 : ℝ)) (c := (34178601020356143069/34180000000000000000 : ℝ)) (alpha := (144819862489/683600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34178601020356143069/34180000000000000000 : ℝ)*(X 0 2+X 1 2)+(144819862489/683600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (2027/20000 : ℝ)) (hi := (16971/100000 : ℝ)) (c := (34178601020356143069/34180000000000000000 : ℝ)) (alpha := (144819862489/683600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((133444979/250000000 : ℝ)*X 2 0+(257005417/500000000 : ℝ)*X 2 1+(-1518280743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s4_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-338273071/2500000000 : ℝ)*X 0 0+(514369661/1000000000 : ℝ)*X 0 1+(5455745723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s4_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2626171449/5000000000 : ℝ)*X 1 0+(-1202643343/10000000000 : ℝ)*X 1 1+(54557457/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s4_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2626171437/5000000000 : ℝ)*X 2 0+(136393643/250000000 : ℝ)*X 2 1+(-300660837/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s4_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4083900203/10000000000 : ℝ)*X 0 0+(457062637/1000000000 : ℝ)*X 0 1+(3630760497/10000000000 : ℝ)*X 0 2+(4083900203/10000000000 : ℝ)*X 1 0+(457062637/1000000000 : ℝ)*X 1 1+(3630760497/10000000000 : ℝ)*X 1 2+(4083900203/10000000000 : ℝ)*X 2 0+(457062637/1000000000 : ℝ)*X 2 1+(3630760497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s4_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7083223933646007401787/2136250000000000000000000000 : ℝ) := by norm_num
    linear_combination (113202083/25000000000000 : ℝ)*(base19) + (477088031/100000000000000 : ℝ)*(base23) + (127614951/100000000000000 : ℝ)*(lower1) + (2211939/3125000000000 : ℝ)*(upper3) + (17986963/100000000000000 : ℝ)*(lower4) + (69324267/100000000000000 : ℝ)*(upper5) + (533574955049711/25000000000000 : ℝ)*(major0) + (533574955049711/25000000000000 : ℝ)*(major1) + (533574955049711/25000000000000 : ℝ)*(major2) + (287475813/100000000000000 : ℝ)*(sp0) + (1602309674864081/50000000000000 : ℝ)*(sp1) + (320461889691983/10000000000000 : ℝ)*(sp2) + (1602309292582159/50000000000000 : ℝ)*(sp3) + (1063980180145247/100000000000000 : ℝ)*(sp4) + (1063980180145247/100000000000000 : ℝ)*(f.failure) + (1602309674864081/50000000000000 : ℝ)*(f.sum) + (2691891909597/4272500000000000000000000000 : ℝ)*base65 + (2882761181787946941/854500000000000000000000000000000 : ℝ)*base68 + (353752796575446941/854500000000000000000000000000000 : ℝ)*base70 + (71630785325642553059/854500000000000000000000000000000 : ℝ)*base71 + (14449917985821/8545000000000000000000000000 : ℝ)*base74 + (21245375451091553059/854500000000000000000000000000000 : ℝ)*base75 + (3344941384081446941/854500000000000000000000000000000 : ℝ)*base78 + (472118133692053059/854500000000000000000000000000000 : ℝ)*base79 + (7511498193059/8545000000000000000000000000 : ℝ)*base81 + (1671751/400000000000000000000 : ℝ)*base89 + (1671751/400000000000000000000 : ℝ)*base91 + (1671751/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1727_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2027/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2027/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1697/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1727_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1727_box_0 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046950097/10000000000 : ℝ)*x 0 + (5408406581/10000000000 : ℝ)*x 1 + (108168131/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046950097/10000000000 : ℝ)^5439 ≤ (1550782795613/25000000000000 : ℝ)^4415 := by
    have hnat : (1046950097 : ℕ)^5439*25000000000000^4415 ≤ 1550782795613^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046950097 10000000000 1550782795613 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408406581/10000000000 : ℝ)^5439 ≤ (937968691269/2000000000000 : ℝ)^4415 := by
    have hnat : (5408406581 : ℕ)^5439*2000000000000^4415 ≤ 937968691269^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408406581 10000000000 937968691269 2000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108168131/200000000 : ℝ)^5439 ≤ (46898434232289/100000000000000 : ℝ)^4415 := by
    have hnat : (108168131 : ℕ)^5439*100000000000000^4415 ≤ 46898434232289^4415*200000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108168131 200000000 46898434232289 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046950097/10000000000 : ℝ), (5408406581/10000000000 : ℝ), (108168131/200000000 : ℝ)] ![(1550782795613/25000000000000 : ℝ), (937968691269/2000000000000 : ℝ), (46898434232289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046950097/10000000000 : ℝ)|^5439 ≤ (1550782795613/25000000000000 : ℝ)^4415
        have hw : |(-1046950097/10000000000 : ℝ)|=(1046950097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408406581/10000000000 : ℝ)|^5439 ≤ (937968691269/2000000000000 : ℝ)^4415
        have hw : |(5408406581/10000000000 : ℝ)|=(5408406581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108168131/200000000 : ℝ)|^5439 ≤ (46898434232289/100000000000000 : ℝ)^4415
        have hw : |(108168131/200000000 : ℝ)|=(108168131/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_1 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224388991/10000000000 : ℝ)*x 0 + (-20438707/156250000 : ℝ)*x 1 + (5408406599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224388991/10000000000 : ℝ)^5439 ≤ (44940471560709/100000000000000 : ℝ)^4415 := by
    have hnat : (5224388991 : ℕ)^5439*100000000000000^4415 ≤ 44940471560709^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224388991 10000000000 44940471560709 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20438707/156250000 : ℝ)^5439 ≤ (1632218731901/20000000000000 : ℝ)^4415 := by
    have hnat : (20438707 : ℕ)^5439*20000000000000^4415 ≤ 1632218731901^4415*156250000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20438707 156250000 1632218731901 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408406599/10000000000 : ℝ)^5439 ≤ (46898434755737/100000000000000 : ℝ)^4415 := by
    have hnat : (5408406599 : ℕ)^5439*100000000000000^4415 ≤ 46898434755737^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408406599 10000000000 46898434755737 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224388991/10000000000 : ℝ), (-20438707/156250000 : ℝ), (5408406599/10000000000 : ℝ)] ![(44940471560709/100000000000000 : ℝ), (1632218731901/20000000000000 : ℝ), (46898434755737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224388991/10000000000 : ℝ)|^5439 ≤ (44940471560709/100000000000000 : ℝ)^4415
        have hw : |(5224388991/10000000000 : ℝ)|=(5224388991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20438707/156250000 : ℝ)|^5439 ≤ (1632218731901/20000000000000 : ℝ)^4415
        have hw : |(-20438707/156250000 : ℝ)|=(20438707/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408406599/10000000000 : ℝ)|^5439 ≤ (46898434755737/100000000000000 : ℝ)^4415
        have hw : |(5408406599/10000000000 : ℝ)|=(5408406599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_2 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224389369/10000000000 : ℝ)*x 0 + (540840627/1000000000 : ℝ)*x 1 + (-10219353/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224389369/10000000000 : ℝ)^5439 ≤ (11235118891611/25000000000000 : ℝ)^4415 := by
    have hnat : (5224389369 : ℕ)^5439*25000000000000^4415 ≤ 11235118891611^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224389369 10000000000 11235118891611 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540840627/1000000000 : ℝ)^5439 ≤ (46898431241159/100000000000000 : ℝ)^4415 := by
    have hnat : (540840627 : ℕ)^5439*100000000000000^4415 ≤ 46898431241159^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540840627 1000000000 46898431241159 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10219353/78125000 : ℝ)^5439 ≤ (4080546583799/50000000000000 : ℝ)^4415 := by
    have hnat : (10219353 : ℕ)^5439*50000000000000^4415 ≤ 4080546583799^4415*78125000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10219353 78125000 4080546583799 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224389369/10000000000 : ℝ), (540840627/1000000000 : ℝ), (-10219353/78125000 : ℝ)] ![(11235118891611/25000000000000 : ℝ), (46898431241159/100000000000000 : ℝ), (4080546583799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224389369/10000000000 : ℝ)|^5439 ≤ (11235118891611/25000000000000 : ℝ)^4415
        have hw : |(5224389369/10000000000 : ℝ)|=(5224389369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540840627/1000000000 : ℝ)|^5439 ≤ (46898431241159/100000000000000 : ℝ)^4415
        have hw : |(540840627/1000000000 : ℝ)|=(540840627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10219353/78125000 : ℝ)|^5439 ≤ (4080546583799/50000000000000 : ℝ)^4415
        have hw : |(-10219353/78125000 : ℝ)|=(10219353/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_3 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (892738157/2000000000 : ℝ)*x 0 + (391423927/1000000000 : ℝ)*x 1 + (1957119739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892738157/2000000000 : ℝ)^5439 ≤ (37020761693903/100000000000000 : ℝ)^4415 := by
    have hnat : (892738157 : ℕ)^5439*100000000000000^4415 ≤ 37020761693903^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892738157 2000000000 37020761693903 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391423927/1000000000 : ℝ)^5439 ≤ (15744809058897/50000000000000 : ℝ)^4415 := by
    have hnat : (391423927 : ℕ)^5439*50000000000000^4415 ≤ 15744809058897^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391423927 1000000000 15744809058897 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1957119739/5000000000 : ℝ)^5439 ≤ (31489620179239/100000000000000 : ℝ)^4415 := by
    have hnat : (1957119739 : ℕ)^5439*100000000000000^4415 ≤ 31489620179239^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957119739 5000000000 31489620179239 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(892738157/2000000000 : ℝ), (391423927/1000000000 : ℝ), (1957119739/5000000000 : ℝ)] ![(37020761693903/100000000000000 : ℝ), (15744809058897/50000000000000 : ℝ), (31489620179239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(892738157/2000000000 : ℝ)|^5439 ≤ (37020761693903/100000000000000 : ℝ)^4415
        have hw : |(892738157/2000000000 : ℝ)|=(892738157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(391423927/1000000000 : ℝ)|^5439 ≤ (15744809058897/50000000000000 : ℝ)^4415
        have hw : |(391423927/1000000000 : ℝ)|=(391423927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1957119739/5000000000 : ℝ)|^5439 ≤ (31489620179239/100000000000000 : ℝ)^4415
        have hw : |(1957119739/5000000000 : ℝ)|=(1957119739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_4 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-335861679/2000000000 : ℝ)*x 0 + (323622069/625000000 : ℝ)*x 1 + (5177952949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335861679/2000000000 : ℝ)^5439 ≤ (2220444198959/20000000000000 : ℝ)^4415 := by
    have hnat : (335861679 : ℕ)^5439*20000000000000^4415 ≤ 2220444198959^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335861679 2000000000 2220444198959 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323622069/625000000 : ℝ)^5439 ≤ (44448890312281/100000000000000 : ℝ)^4415 := by
    have hnat : (323622069 : ℕ)^5439*100000000000000^4415 ≤ 44448890312281^4415*625000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323622069 625000000 44448890312281 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177952949/10000000000 : ℝ)^5439 ≤ (8889777734623/20000000000000 : ℝ)^4415 := by
    have hnat : (5177952949 : ℕ)^5439*20000000000000^4415 ≤ 8889777734623^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177952949 10000000000 8889777734623 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-335861679/2000000000 : ℝ), (323622069/625000000 : ℝ), (5177952949/10000000000 : ℝ)] ![(2220444198959/20000000000000 : ℝ), (44448890312281/100000000000000 : ℝ), (8889777734623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-335861679/2000000000 : ℝ)|^5439 ≤ (2220444198959/20000000000000 : ℝ)^4415
        have hw : |(-335861679/2000000000 : ℝ)|=(335861679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323622069/625000000 : ℝ)|^5439 ≤ (44448890312281/100000000000000 : ℝ)^4415
        have hw : |(323622069/625000000 : ℝ)|=(323622069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177952949/10000000000 : ℝ)|^5439 ≤ (8889777734623/20000000000000 : ℝ)^4415
        have hw : |(5177952949/10000000000 : ℝ)|=(5177952949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_5 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336253423/625000000 : ℝ)*x 0 + (-1410505029/10000000000 : ℝ)*x 1 + (5177952419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336253423/625000000 : ℝ)^5439 ≤ (46595747579483/100000000000000 : ℝ)^4415 := by
    have hnat : (336253423 : ℕ)^5439*100000000000000^4415 ≤ 46595747579483^4415*625000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336253423 625000000 46595747579483 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410505029/10000000000 : ℝ)^5439 ≤ (559710583869/6250000000000 : ℝ)^4415 := by
    have hnat : (1410505029 : ℕ)^5439*6250000000000^4415 ≤ 559710583869^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410505029 10000000000 559710583869 6250000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177952419/10000000000 : ℝ)^5439 ≤ (22224441534113/50000000000000 : ℝ)^4415 := by
    have hnat : (5177952419 : ℕ)^5439*50000000000000^4415 ≤ 22224441534113^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177952419 10000000000 22224441534113 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336253423/625000000 : ℝ), (-1410505029/10000000000 : ℝ), (5177952419/10000000000 : ℝ)] ![(46595747579483/100000000000000 : ℝ), (559710583869/6250000000000 : ℝ), (22224441534113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336253423/625000000 : ℝ)|^5439 ≤ (46595747579483/100000000000000 : ℝ)^4415
        have hw : |(336253423/625000000 : ℝ)|=(336253423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1410505029/10000000000 : ℝ)|^5439 ≤ (559710583869/6250000000000 : ℝ)^4415
        have hw : |(-1410505029/10000000000 : ℝ)|=(1410505029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177952419/10000000000 : ℝ)|^5439 ≤ (22224441534113/50000000000000 : ℝ)^4415
        have hw : |(5177952419/10000000000 : ℝ)|=(5177952419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_6 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538005457/1000000000 : ℝ)*x 0 + (1035590517/2000000000 : ℝ)*x 1 + (-56420203/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538005457/1000000000 : ℝ)^5439 ≤ (5824468183363/12500000000000 : ℝ)^4415 := by
    have hnat : (538005457 : ℕ)^5439*12500000000000^4415 ≤ 5824468183363^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538005457 1000000000 5824468183363 12500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035590517/2000000000 : ℝ)^5439 ≤ (1111222120593/2500000000000 : ℝ)^4415 := by
    have hnat : (1035590517 : ℕ)^5439*2500000000000^4415 ≤ 1111222120593^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035590517 2000000000 1111222120593 2500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56420203/400000000 : ℝ)^5439 ≤ (8955369701699/100000000000000 : ℝ)^4415 := by
    have hnat : (56420203 : ℕ)^5439*100000000000000^4415 ≤ 8955369701699^4415*400000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56420203 400000000 8955369701699 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538005457/1000000000 : ℝ), (1035590517/2000000000 : ℝ), (-56420203/400000000 : ℝ)] ![(5824468183363/12500000000000 : ℝ), (1111222120593/2500000000000 : ℝ), (8955369701699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538005457/1000000000 : ℝ)|^5439 ≤ (5824468183363/12500000000000 : ℝ)^4415
        have hw : |(538005457/1000000000 : ℝ)|=(538005457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035590517/2000000000 : ℝ)|^5439 ≤ (1111222120593/2500000000000 : ℝ)^4415
        have hw : |(1035590517/2000000000 : ℝ)|=(1035590517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56420203/400000000 : ℝ)|^5439 ≤ (8955369701699/100000000000000 : ℝ)^4415
        have hw : |(-56420203/400000000 : ℝ)|=(56420203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_7 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (921684743/2500000000 : ℝ)*x 0 + (1075478287/2500000000 : ℝ)*x 1 + (2150956529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921684743/2500000000 : ℝ)^5439 ≤ (914073102451/3125000000000 : ℝ)^4415 := by
    have hnat : (921684743 : ℕ)^5439*3125000000000^4415 ≤ 914073102451^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921684743 2500000000 914073102451 3125000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075478287/2500000000 : ℝ)^5439 ≤ (8843707701971/25000000000000 : ℝ)^4415 := by
    have hnat : (1075478287 : ℕ)^5439*25000000000000^4415 ≤ 8843707701971^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075478287 2500000000 8843707701971 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150956529/5000000000 : ℝ)^5439 ≤ (35374829896159/100000000000000 : ℝ)^4415 := by
    have hnat : (2150956529 : ℕ)^5439*100000000000000^4415 ≤ 35374829896159^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150956529 5000000000 35374829896159 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(921684743/2500000000 : ℝ), (1075478287/2500000000 : ℝ), (2150956529/5000000000 : ℝ)] ![(914073102451/3125000000000 : ℝ), (8843707701971/25000000000000 : ℝ), (35374829896159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(921684743/2500000000 : ℝ)|^5439 ≤ (914073102451/3125000000000 : ℝ)^4415
        have hw : |(921684743/2500000000 : ℝ)|=(921684743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075478287/2500000000 : ℝ)|^5439 ≤ (8843707701971/25000000000000 : ℝ)^4415
        have hw : |(1075478287/2500000000 : ℝ)|=(1075478287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150956529/5000000000 : ℝ)|^5439 ≤ (35374829896159/100000000000000 : ℝ)^4415
        have hw : |(2150956529/5000000000 : ℝ)|=(2150956529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_8 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-385773057/2500000000 : ℝ)*x 0 + (1001410229/2000000000 : ℝ)*x 1 + (2725226533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385773057/2500000000 : ℝ)^5439 ≤ (5001730384173/50000000000000 : ℝ)^4415 := by
    have hnat : (385773057 : ℕ)^5439*50000000000000^4415 ≤ 5001730384173^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385773057 2500000000 5001730384173 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001410229/2000000000 : ℝ)^5439 ≤ (42648534312803/100000000000000 : ℝ)^4415 := by
    have hnat : (1001410229 : ℕ)^5439*100000000000000^4415 ≤ 42648534312803^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001410229 2000000000 42648534312803 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725226533/5000000000 : ℝ)^5439 ≤ (23674002453647/50000000000000 : ℝ)^4415 := by
    have hnat : (2725226533 : ℕ)^5439*50000000000000^4415 ≤ 23674002453647^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725226533 5000000000 23674002453647 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385773057/2500000000 : ℝ), (1001410229/2000000000 : ℝ), (2725226533/5000000000 : ℝ)] ![(5001730384173/50000000000000 : ℝ), (42648534312803/100000000000000 : ℝ), (23674002453647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385773057/2500000000 : ℝ)|^5439 ≤ (5001730384173/50000000000000 : ℝ)^4415
        have hw : |(-385773057/2500000000 : ℝ)|=(385773057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001410229/2000000000 : ℝ)|^5439 ≤ (42648534312803/100000000000000 : ℝ)^4415
        have hw : |(1001410229/2000000000 : ℝ)|=(1001410229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725226533/5000000000 : ℝ)|^5439 ≤ (23674002453647/50000000000000 : ℝ)^4415
        have hw : |(2725226533/5000000000 : ℝ)|=(2725226533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_9 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129900323/250000000 : ℝ)*x 0 + (-257730381/2000000000 : ℝ)*x 1 + (1090090477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129900323/250000000 : ℝ)^5439 ≤ (44639954790557/100000000000000 : ℝ)^4415 := by
    have hnat : (129900323 : ℕ)^5439*100000000000000^4415 ≤ 44639954790557^4415*250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129900323 250000000 44639954790557 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257730381/2000000000 : ℝ)^5439 ≤ (8012047572567/100000000000000 : ℝ)^4415 := by
    have hnat : (257730381 : ℕ)^5439*100000000000000^4415 ≤ 8012047572567^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257730381 2000000000 8012047572567 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090090477/2000000000 : ℝ)^5439 ≤ (23673998809679/50000000000000 : ℝ)^4415 := by
    have hnat : (1090090477 : ℕ)^5439*50000000000000^4415 ≤ 23673998809679^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090090477 2000000000 23673998809679 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129900323/250000000 : ℝ), (-257730381/2000000000 : ℝ), (1090090477/2000000000 : ℝ)] ![(44639954790557/100000000000000 : ℝ), (8012047572567/100000000000000 : ℝ), (23673998809679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129900323/250000000 : ℝ)|^5439 ≤ (44639954790557/100000000000000 : ℝ)^4415
        have hw : |(129900323/250000000 : ℝ)|=(129900323/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257730381/2000000000 : ℝ)|^5439 ≤ (8012047572567/100000000000000 : ℝ)^4415
        have hw : |(-257730381/2000000000 : ℝ)|=(257730381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090090477/2000000000 : ℝ)|^5439 ≤ (23673998809679/50000000000000 : ℝ)^4415
        have hw : |(1090090477/2000000000 : ℝ)|=(1090090477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_10 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196012753/10000000000 : ℝ)*x 0 + (2725226423/5000000000 : ℝ)*x 1 + (-1288651491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196012753/10000000000 : ℝ)^5439 ≤ (44639953023061/100000000000000 : ℝ)^4415 := by
    have hnat : (5196012753 : ℕ)^5439*100000000000000^4415 ≤ 44639953023061^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196012753 10000000000 44639953023061 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725226423/5000000000 : ℝ)^5439 ≤ (9469600510579/20000000000000 : ℝ)^4415 := by
    have hnat : (2725226423 : ℕ)^5439*20000000000000^4415 ≤ 9469600510579^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725226423 5000000000 9469600510579 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288651491/10000000000 : ℝ)^5439 ≤ (1602408880313/20000000000000 : ℝ)^4415 := by
    have hnat : (1288651491 : ℕ)^5439*20000000000000^4415 ≤ 1602408880313^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288651491 10000000000 1602408880313 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196012753/10000000000 : ℝ), (2725226423/5000000000 : ℝ), (-1288651491/10000000000 : ℝ)] ![(44639953023061/100000000000000 : ℝ), (9469600510579/20000000000000 : ℝ), (1602408880313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196012753/10000000000 : ℝ)|^5439 ≤ (44639953023061/100000000000000 : ℝ)^4415
        have hw : |(5196012753/10000000000 : ℝ)|=(5196012753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725226423/5000000000 : ℝ)|^5439 ≤ (9469600510579/20000000000000 : ℝ)^4415
        have hw : |(2725226423/5000000000 : ℝ)|=(2725226423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288651491/10000000000 : ℝ)|^5439 ≤ (1602408880313/20000000000000 : ℝ)^4415
        have hw : |(-1288651491/10000000000 : ℝ)|=(1288651491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_11 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2300248099/5000000000 : ℝ)*x 0 + (960830553/2500000000 : ℝ)*x 1 + (3843322267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2300248099/5000000000 : ℝ)^5439 ≤ (4802935550429/12500000000000 : ℝ)^4415 := by
    have hnat : (2300248099 : ℕ)^5439*12500000000000^4415 ≤ 4802935550429^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300248099 5000000000 4802935550429 12500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960830553/2500000000 : ℝ)^5439 ≤ (60133315473/195312500000 : ℝ)^4415 := by
    have hnat : (960830553 : ℕ)^5439*195312500000^4415 ≤ 60133315473^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960830553 2500000000 60133315473 195312500000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3843322267/10000000000 : ℝ)^5439 ≤ (30788258064963/100000000000000 : ℝ)^4415 := by
    have hnat : (3843322267 : ℕ)^5439*100000000000000^4415 ≤ 30788258064963^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843322267 10000000000 30788258064963 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2300248099/5000000000 : ℝ), (960830553/2500000000 : ℝ), (3843322267/10000000000 : ℝ)] ![(4802935550429/12500000000000 : ℝ), (60133315473/195312500000 : ℝ), (30788258064963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2300248099/5000000000 : ℝ)|^5439 ≤ (4802935550429/12500000000000 : ℝ)^4415
        have hw : |(2300248099/5000000000 : ℝ)|=(2300248099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(960830553/2500000000 : ℝ)|^5439 ≤ (60133315473/195312500000 : ℝ)^4415
        have hw : |(960830553/2500000000 : ℝ)|=(960830553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3843322267/10000000000 : ℝ)|^5439 ≤ (30788258064963/100000000000000 : ℝ)^4415
        have hw : |(3843322267/10000000000 : ℝ)|=(3843322267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_12 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1177261607/10000000000 : ℝ)*x 0 + (1114303557/2000000000 : ℝ)*x 1 + (2576514239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1177261607/10000000000 : ℝ)^5439 ≤ (3583805587941/50000000000000 : ℝ)^4415 := by
    have hnat : (1177261607 : ℕ)^5439*50000000000000^4415 ≤ 3583805587941^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177261607 10000000000 3583805587941 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114303557/2000000000 : ℝ)^5439 ≤ (24323467822049/50000000000000 : ℝ)^4415 := by
    have hnat : (1114303557 : ℕ)^5439*50000000000000^4415 ≤ 24323467822049^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114303557 2000000000 24323467822049 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576514239/5000000000 : ℝ)^5439 ≤ (8837090633591/20000000000000 : ℝ)^4415 := by
    have hnat : (2576514239 : ℕ)^5439*20000000000000^4415 ≤ 8837090633591^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576514239 5000000000 8837090633591 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1177261607/10000000000 : ℝ), (1114303557/2000000000 : ℝ), (2576514239/5000000000 : ℝ)] ![(3583805587941/50000000000000 : ℝ), (24323467822049/50000000000000 : ℝ), (8837090633591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1177261607/10000000000 : ℝ)|^5439 ≤ (3583805587941/50000000000000 : ℝ)^4415
        have hw : |(-1177261607/10000000000 : ℝ)|=(1177261607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114303557/2000000000 : ℝ)|^5439 ≤ (24323467822049/50000000000000 : ℝ)^4415
        have hw : |(1114303557/2000000000 : ℝ)|=(1114303557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576514239/5000000000 : ℝ)|^5439 ≤ (8837090633591/20000000000000 : ℝ)^4415
        have hw : |(2576514239/5000000000 : ℝ)|=(2576514239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_13 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396923281/10000000000 : ℝ)*x 0 + (-177644537/1250000000 : ℝ)*x 1 + (1030605719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396923281/10000000000 : ℝ)^5439 ≤ (11693948293011/25000000000000 : ℝ)^4415 := by
    have hnat : (5396923281 : ℕ)^5439*25000000000000^4415 ≤ 11693948293011^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396923281 10000000000 11693948293011 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177644537/1250000000 : ℝ)^5439 ≤ (2259688104259/25000000000000 : ℝ)^4415 := by
    have hnat : (177644537 : ℕ)^5439*25000000000000^4415 ≤ 2259688104259^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177644537 1250000000 2259688104259 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030605719/2000000000 : ℝ)^5439 ≤ (11046363600969/25000000000000 : ℝ)^4415 := by
    have hnat : (1030605719 : ℕ)^5439*25000000000000^4415 ≤ 11046363600969^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030605719 2000000000 11046363600969 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396923281/10000000000 : ℝ), (-177644537/1250000000 : ℝ), (1030605719/2000000000 : ℝ)] ![(11693948293011/25000000000000 : ℝ), (2259688104259/25000000000000 : ℝ), (11046363600969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396923281/10000000000 : ℝ)|^5439 ≤ (11693948293011/25000000000000 : ℝ)^4415
        have hw : |(5396923281/10000000000 : ℝ)|=(5396923281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177644537/1250000000 : ℝ)|^5439 ≤ (2259688104259/25000000000000 : ℝ)^4415
        have hw : |(-177644537/1250000000 : ℝ)|=(177644537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030605719/2000000000 : ℝ)|^5439 ≤ (11046363600969/25000000000000 : ℝ)^4415
        have hw : |(1030605719/2000000000 : ℝ)|=(1030605719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_14 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168653857/312500000 : ℝ)*x 0 + (10306057/20000000 : ℝ)*x 1 + (-1421156229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168653857/312500000 : ℝ)^5439 ≤ (5846974337363/12500000000000 : ℝ)^4415 := by
    have hnat : (168653857 : ℕ)^5439*12500000000000^4415 ≤ 5846974337363^4415*312500000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168653857 312500000 5846974337363 12500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10306057/20000000 : ℝ)^5439 ≤ (883709068007/2000000000000 : ℝ)^4415 := by
    have hnat : (10306057 : ℕ)^5439*2000000000000^4415 ≤ 883709068007^4415*20000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10306057 20000000 883709068007 2000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1421156229/10000000000 : ℝ)^5439 ≤ (9038751892071/100000000000000 : ℝ)^4415 := by
    have hnat : (1421156229 : ℕ)^5439*100000000000000^4415 ≤ 9038751892071^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421156229 10000000000 9038751892071 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168653857/312500000 : ℝ), (10306057/20000000 : ℝ), (-1421156229/10000000000 : ℝ)] ![(5846974337363/12500000000000 : ℝ), (883709068007/2000000000000 : ℝ), (9038751892071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168653857/312500000 : ℝ)|^5439 ≤ (5846974337363/12500000000000 : ℝ)^4415
        have hw : |(168653857/312500000 : ℝ)|=(168653857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10306057/20000000 : ℝ)|^5439 ≤ (883709068007/2000000000000 : ℝ)^4415
        have hw : |(10306057/20000000 : ℝ)|=(10306057/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1421156229/10000000000 : ℝ)|^5439 ≤ (9038751892071/100000000000000 : ℝ)^4415
        have hw : |(-1421156229/10000000000 : ℝ)|=(1421156229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_box_15 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3599727287/10000000000 : ℝ)*x 0 + (4343726767/10000000000 : ℝ)*x 1 + (4343726677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3599727287/10000000000 : ℝ)^5439 ≤ (28402220113809/100000000000000 : ℝ)^4415 := by
    have hnat : (3599727287 : ℕ)^5439*100000000000000^4415 ≤ 28402220113809^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3599727287 10000000000 28402220113809 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4343726767/10000000000 : ℝ)^5439 ≤ (8949722598463/25000000000000 : ℝ)^4415 := by
    have hnat : (4343726767 : ℕ)^5439*25000000000000^4415 ≤ 8949722598463^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343726767 10000000000 8949722598463 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343726677/10000000000 : ℝ)^5439 ≤ (447486118501/1250000000000 : ℝ)^4415 := by
    have hnat : (4343726677 : ℕ)^5439*1250000000000^4415 ≤ 447486118501^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343726677 10000000000 447486118501 1250000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3599727287/10000000000 : ℝ), (4343726767/10000000000 : ℝ), (4343726677/10000000000 : ℝ)] ![(28402220113809/100000000000000 : ℝ), (8949722598463/25000000000000 : ℝ), (447486118501/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3599727287/10000000000 : ℝ)|^5439 ≤ (28402220113809/100000000000000 : ℝ)^4415
        have hw : |(3599727287/10000000000 : ℝ)|=(3599727287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4343726767/10000000000 : ℝ)|^5439 ≤ (8949722598463/25000000000000 : ℝ)^4415
        have hw : |(4343726767/10000000000 : ℝ)|=(4343726767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4343726677/10000000000 : ℝ)|^5439 ≤ (447486118501/1250000000000 : ℝ)^4415
        have hw : |(4343726677/10000000000 : ℝ)|=(4343726677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1727_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1697/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2027/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66913/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58799/100000 : ℝ) ∧ (2563/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4533/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1697/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2027/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1697/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2027/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1697/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2027/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1697/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2027/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1697/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2027/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1697/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2027/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2027/20000 : ℝ) ^ (5431/1024 : ℝ) ≤ (66693971275917/12500000000000000000 : ℝ) := by
    have hpowers : (2027/20000 : ℝ)^5431 ≤ (66693971275917/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2027 : ℕ)^5431*12500000000000000000^1024 ≤ 66693971275917^1024*20000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2027 20000 66693971275917 12500000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2027/20000 : ℝ)) (X := (66693971275917/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1697/10000 : ℝ) ^ (5431/1024 : ℝ) ≤ (8212117633552321/100000000000000000000 : ℝ) := by
    have hpowers : (1697/10000 : ℝ)^5431 ≤ (8212117633552321/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1697 : ℕ)^5431*100000000000000000000^1024 ≤ 8212117633552321^1024*10000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1697 10000 8212117633552321 100000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1697/10000 : ℝ)) (X := (8212117633552321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250066693971275917/6250000000000000000 : ℝ) ≤ (5000010059927219/5000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (6250066693971275917/6250000000000000000 : ℝ)^1024 ≤ (5000010059927219/5000000000000000 : ℝ)^5431 := by
      have hnat : (6250066693971275917 : ℕ)^1024*5000000000000000^5431 ≤ 5000010059927219^5431*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250066693971275917 6250000000000000000 5000010059927219 5000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010059927219/5000000000000000 : ℝ)) (X := (6250066693971275917/6250000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008745669403759657/100000000000000000000 : ℝ) ≤ (10000164891322253/10000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (100008745669403759657/100000000000000000000 : ℝ)^1024 ≤ (10000164891322253/10000000000000000 : ℝ)^5431 := by
      have hnat : (100008745669403759657 : ℕ)^1024*10000000000000000^5431 ≤ 10000164891322253^5431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008745669403759657 100000000000000000000 10000164891322253 10000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000164891322253/10000000000000000 : ℝ)) (X := (100008745669403759657/100000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008212117633552321/50000000000000000000 : ℝ) ≤ (2500077415697517/2500000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (50008212117633552321/50000000000000000000 : ℝ)^1024 ≤ (2500077415697517/2500000000000000 : ℝ)^5431 := by
      have hnat : (50008212117633552321 : ℕ)^1024*2500000000000000^5431 ≤ 2500077415697517^5431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008212117633552321 50000000000000000000 2500077415697517 2500000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500077415697517/2500000000000000 : ℝ)) (X := (50008212117633552321/50000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(66693971275917/12500000000000000000 : ℝ) ≤ ((854340037519405921/854375000000000000 : ℝ)+2*(28954293563/136700000000000 : ℝ)*(2027/20000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (854340037519405921/854375000000000000 : ℝ)+2*(28954293563/136700000000000 : ℝ)*(2027/20000 : ℝ)=(5000010059927219/5000000000000000 : ℝ) by norm_num, show 1+2*(66693971275917/12500000000000000000 : ℝ)=(6250066693971275917/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8212117633552321/100000000000000000000 : ℝ)+(66693971275917/12500000000000000000 : ℝ) ≤ ((854340037519405921/854375000000000000 : ℝ)+(28954293563/136700000000000 : ℝ)*((1697/10000 : ℝ)+(2027/20000 : ℝ)))^(5431/1024 : ℝ) := by
    rw [show (854340037519405921/854375000000000000 : ℝ)+(28954293563/136700000000000 : ℝ)*((1697/10000 : ℝ)+(2027/20000 : ℝ))=(10000164891322253/10000000000000000 : ℝ) by norm_num, show 1+(8212117633552321/100000000000000000000 : ℝ)+(66693971275917/12500000000000000000 : ℝ)=(100008745669403759657/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8212117633552321/100000000000000000000 : ℝ) ≤ ((854340037519405921/854375000000000000 : ℝ)+2*(28954293563/136700000000000 : ℝ)*(1697/10000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (854340037519405921/854375000000000000 : ℝ)+2*(28954293563/136700000000000 : ℝ)*(1697/10000 : ℝ)=(2500077415697517/2500000000000000 : ℝ) by norm_num, show 1+2*(8212117633552321/100000000000000000000 : ℝ)=(50008212117633552321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (854340037519405921/854375000000000000 : ℝ)*(X 1 0+X 2 0)+(28954293563/136700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (2027/20000 : ℝ)) (hi := (1697/10000 : ℝ)) (c := (854340037519405921/854375000000000000 : ℝ)) (alpha := (28954293563/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (854340037519405921/854375000000000000 : ℝ)*(X 0 1+X 2 1)+(28954293563/136700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (2027/20000 : ℝ)) (hi := (1697/10000 : ℝ)) (c := (854340037519405921/854375000000000000 : ℝ)) (alpha := (28954293563/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (854340037519405921/854375000000000000 : ℝ)*(X 0 2+X 1 2)+(28954293563/136700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (2027/20000 : ℝ)) (hi := (1697/10000 : ℝ)) (c := (854340037519405921/854375000000000000 : ℝ)) (alpha := (28954293563/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1046950097/10000000000 : ℝ)*X 0 0+(5408406581/10000000000 : ℝ)*X 0 1+(108168131/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5224388991/10000000000 : ℝ)*X 1 0+(-20438707/156250000 : ℝ)*X 1 1+(5408406599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224389369/10000000000 : ℝ)*X 2 0+(540840627/1000000000 : ℝ)*X 2 1+(-10219353/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((892738157/2000000000 : ℝ)*X 0 0+(391423927/1000000000 : ℝ)*X 0 1+(1957119739/5000000000 : ℝ)*X 0 2+(892738157/2000000000 : ℝ)*X 1 0+(391423927/1000000000 : ℝ)*X 1 1+(1957119739/5000000000 : ℝ)*X 1 2+(892738157/2000000000 : ℝ)*X 2 0+(391423927/1000000000 : ℝ)*X 2 1+(1957119739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-335861679/2000000000 : ℝ)*X 0 0+(323622069/625000000 : ℝ)*X 0 1+(5177952949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((336253423/625000000 : ℝ)*X 1 0+(-1410505029/10000000000 : ℝ)*X 1 1+(5177952419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538005457/1000000000 : ℝ)*X 2 0+(1035590517/2000000000 : ℝ)*X 2 1+(-56420203/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((921684743/2500000000 : ℝ)*X 0 0+(1075478287/2500000000 : ℝ)*X 0 1+(2150956529/5000000000 : ℝ)*X 0 2+(921684743/2500000000 : ℝ)*X 1 0+(1075478287/2500000000 : ℝ)*X 1 1+(2150956529/5000000000 : ℝ)*X 1 2+(921684743/2500000000 : ℝ)*X 2 0+(1075478287/2500000000 : ℝ)*X 2 1+(2150956529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-385773057/2500000000 : ℝ)*X 0 0+(1001410229/2000000000 : ℝ)*X 0 1+(2725226533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((129900323/250000000 : ℝ)*X 1 0+(-257730381/2000000000 : ℝ)*X 1 1+(1090090477/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196012753/10000000000 : ℝ)*X 2 0+(2725226423/5000000000 : ℝ)*X 2 1+(-1288651491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2300248099/5000000000 : ℝ)*X 0 0+(960830553/2500000000 : ℝ)*X 0 1+(3843322267/10000000000 : ℝ)*X 0 2+(2300248099/5000000000 : ℝ)*X 1 0+(960830553/2500000000 : ℝ)*X 1 1+(3843322267/10000000000 : ℝ)*X 1 2+(2300248099/5000000000 : ℝ)*X 2 0+(960830553/2500000000 : ℝ)*X 2 1+(3843322267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1177261607/10000000000 : ℝ)*X 0 0+(1114303557/2000000000 : ℝ)*X 0 1+(2576514239/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396923281/10000000000 : ℝ)*X 1 0+(-177644537/1250000000 : ℝ)*X 1 1+(1030605719/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((168653857/312500000 : ℝ)*X 2 0+(10306057/20000000 : ℝ)*X 2 1+(-1421156229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3599727287/10000000000 : ℝ)*X 0 0+(4343726767/10000000000 : ℝ)*X 0 1+(4343726677/10000000000 : ℝ)*X 0 2+(3599727287/10000000000 : ℝ)*X 1 0+(4343726767/10000000000 : ℝ)*X 1 1+(4343726677/10000000000 : ℝ)*X 1 2+(3599727287/10000000000 : ℝ)*X 2 0+(4343726767/10000000000 : ℝ)*X 2 1+(4343726677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66913/100000 : ℝ) ≤ (-2858320493069284562480800266099/4271875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46241/100000000000000 : ℝ)*(upper1) + (19807323/100000000000000 : ℝ)*(upper2) + (7166913/20000000000000 : ℝ)*(upper3) + (5200303/100000000000000 : ℝ)*(upper5) + (34986493171469/2500000000000 : ℝ)*(major0) + (34986493171469/2500000000000 : ℝ)*(major1) + (34986493171469/2500000000000 : ℝ)*(major2) + (128735013/2000000000000 : ℝ)*(sp1) + (626013303/12500000000000 : ℝ)*(sp2) + (703214289/100000000000000 : ℝ)*(sp3) + (530892846062361/25000000000000 : ℝ)*(sp4) + (2123564947498793/100000000000000 : ℝ)*(sp5) + (2123566376143019/100000000000000 : ℝ)*(sp6) + (17441269231803/2500000000000 : ℝ)*(sp7) + (697651472486409/100000000000000 : ℝ)*(f.failure) + (530892846062361/25000000000000 : ℝ)*(f.sum) + (8467760826501/1367000000000000000000000000 : ℝ)*base65 + (4406583338701963/1067968750000000000000000000000 : ℝ)*base68 + (3388959916055669/533984375000000000000000000000 : ℝ)*base70 + (1542039253779727/4271875000000000000000000000000 : ℝ)*base72 + (777329582949/273400000000000000000000000 : ℝ)*base73 + (87259932484029727/4271875000000000000000000000000 : ℝ)*base76 + (23727109055270273/4271875000000000000000000000000 : ℝ)*base77 + (3441821975973477/4271875000000000000000000000000 : ℝ)*base80 + (18453783435211/1367000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (585697/400000000000000000000 : ℝ)*base89 + (585697/400000000000000000000 : ℝ)*base91 + (585697/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58799/100000 : ℝ) ≤ (6279769385313503794113594749757/10679687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5749553/12500000000000 : ℝ)*(lower1) + (14580781/50000000000000 : ℝ)*(lower2) + (195353/50000000000000 : ℝ)*(lower3) + (8009449/25000000000000 : ℝ)*(upper4) + (15603/12500000000000 : ℝ)*(lower5) + (94325825675653/6250000000000 : ℝ)*(major0) + (94325825675653/6250000000000 : ℝ)*(major1) + (94325825675653/6250000000000 : ℝ)*(major2) + (1123230426560569/50000000000000 : ℝ)*(sp0) + (224645262445833/10000000000000 : ℝ)*(sp1) + (280805533340859/12500000000000 : ℝ)*(sp2) + (376182607691473/50000000000000 : ℝ)*(sp3) + (1028582851/12500000000000 : ℝ)*(sp9) + (8293197133/50000000000000 : ℝ)*(sp10) + (376182607691473/50000000000000 : ℝ)*(f.failure) + (1123230426560569/50000000000000 : ℝ)*(f.sum) + (129826432989/26699218750000000000000000 : ℝ)*base65 + (82273255262142201/10679687500000000000000000000000 : ℝ)*base67 + (19526827362203913/5339843750000000000000000000000 : ℝ)*base69 + (55964421086016413/5339843750000000000000000000000 : ℝ)*base71 + (1015840570581/1708750000000000000000000000 : ℝ)*base73 + (67950081943548451/10679687500000000000000000000000 : ℝ)*base75 + (5898365811976661/667480468750000000000000000000 : ℝ)*base77 + (31788380520266413/5339843750000000000000000000000 : ℝ)*base79 + (14751452187333/3417500000000000000000000000 : ℝ)*base82 + (1123991/200000000000000000000 : ℝ)*base90 + (1123991/200000000000000000000 : ℝ)*base92 + (1123991/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2563/3125 : ℝ) ≤ (35037180552459429588985072048359/42718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2798929/10000000000000 : ℝ)*(upper1) + (1146527/1000000000000 : ℝ)*(lower3) + (1890331/10000000000000 : ℝ)*(upper4) + (6962383/25000000000000 : ℝ)*(lower5) + (1520251041607631/100000000000000 : ℝ)*(major0) + (1520251041607631/100000000000000 : ℝ)*(major1) + (1520251041607631/100000000000000 : ℝ)*(major2) + (650683789/25000000000000 : ℝ)*(sp0) + (19934277999/100000000000000 : ℝ)*(sp2) + (459374657/6250000000000 : ℝ)*(sp3) + (1127646159207587/50000000000000 : ℝ)*(sp8) + (225529492115033/10000000000000 : ℝ)*(sp9) + (2255274986872331/100000000000000 : ℝ)*(sp10) + (757860388084101/100000000000000 : ℝ)*(sp11) + (189466934519653/25000000000000 : ℝ)*(f.failure) + (225529492115033/10000000000000 : ℝ)*(f.sum) + (34463525369937/6835000000000000000000000000 : ℝ)*base66 + (803558475923610599/85437500000000000000000000000000 : ℝ)*base68 + (243758602306298099/85437500000000000000000000000000 : ℝ)*base70 + (547861980298610599/85437500000000000000000000000000 : ℝ)*base72 + (15686528799417/6835000000000000000000000000 : ℝ)*base74 + (592099401938923099/85437500000000000000000000000000 : ℝ)*base76 + (563477073833485599/85437500000000000000000000000000 : ℝ)*base78 + (716388464900485599/85437500000000000000000000000000 : ℝ)*base80 + (35607084107357/6835000000000000000000000000 : ℝ)*base82 + (110051/100000000000000000000 : ℝ)*base90 + (110051/100000000000000000000 : ℝ)*base92 + (110051/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-4533/5000 : ℝ) ≤ (-19363847658312065076654243289131/21359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1901577/12500000000000 : ℝ)*(lower0) + (1574221/6250000000000 : ℝ)*(lower1) + (1302501/4000000000000 : ℝ)*(lower2) + (1571330371706163/100000000000000 : ℝ)*(major0) + (1571330371706163/100000000000000 : ℝ)*(major1) + (1571330371706163/100000000000000 : ℝ)*(major2) + (313902541/25000000000000 : ℝ)*(sp0) + (1469244421/12500000000000 : ℝ)*(sp5) + (6353481809/50000000000000 : ℝ)*(sp6) + (1946162963/100000000000000 : ℝ)*(sp7) + (597386766980169/25000000000000 : ℝ)*(sp12) + (149346035598467/6250000000000 : ℝ)*(sp13) + (1194767808283611/50000000000000 : ℝ)*(sp14) + (783329597106277/100000000000000 : ℝ)*(sp15) + (19583288581731/2500000000000 : ℝ)*(f.failure) + (59738708088271/2500000000000 : ℝ)*(f.sum) + (6365744535611/1708750000000000000000000000 : ℝ)*base65 + (425632418898865127/85437500000000000000000000000000 : ℝ)*base68 + (208975032569365127/85437500000000000000000000000000 : ℝ)*base70 + (116875550341865127/85437500000000000000000000000000 : ℝ)*base72 + (3627072293651/1708750000000000000000000000 : ℝ)*base73 + (711609971279865127/85437500000000000000000000000000 : ℝ)*base76 + (298685261630384873/85437500000000000000000000000000 : ℝ)*base77 + (169710162027740127/85437500000000000000000000000000 : ℝ)*base80 + (651114066079/106796875000000000000000000 : ℝ)*base82 + (94923/10000000000000000000 : ℝ)*base89 + (94923/10000000000000000000 : ℝ)*base91 + (94923/10000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1727_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1697/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2027/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58799/100000 : ℝ) else (2563/3125 : ℝ) ≤ X j i ∧ X j i ≤ (4533/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1727_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1727_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58799/100000 : ℝ) else (2563/3125 : ℝ) ≤ X j i ∧ X j i ≤ (4533/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1727_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1727_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1727_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58799/100000 : ℝ) else (2563/3125 : ℝ) ≤ X j i ∧ X j i ≤ (4533/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1727_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
