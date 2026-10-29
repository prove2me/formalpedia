-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1527_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:44.200397+00:00
-- url     : https://prove2.me/submissions/47b6482d-0f14-4cce-bd3d-c8cfcc37ab51

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
theorem support_rectangle_w1527_s3_0 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845665377/10000000000 : ℝ)*x 0 + (5434045587/10000000000 : ℝ)*x 1 + (1303969627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845665377/10000000000 : ℝ)^4551 ≤ (11300401877729/100000000000000 : ℝ)^3527 := by
    have hnat : (1845665377 : ℕ)^4551*100000000000000^3527 ≤ 11300401877729^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845665377 10000000000 11300401877729 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434045587/10000000000 : ℝ)^4551 ≤ (45521981845043/100000000000000 : ℝ)^3527 := by
    have hnat : (5434045587 : ℕ)^4551*100000000000000^3527 ≤ 45521981845043^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434045587 10000000000 45521981845043 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303969627/2500000000 : ℝ)^4551 ≤ (43177616270409/100000000000000 : ℝ)^3527 := by
    have hnat : (1303969627 : ℕ)^4551*100000000000000^3527 ≤ 43177616270409^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303969627 2500000000 43177616270409 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845665377/10000000000 : ℝ), (5434045587/10000000000 : ℝ), (1303969627/2500000000 : ℝ)] ![(11300401877729/100000000000000 : ℝ), (45521981845043/100000000000000 : ℝ), (43177616270409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845665377/10000000000 : ℝ)|^4551 ≤ (11300401877729/100000000000000 : ℝ)^3527
        have hw : |(-1845665377/10000000000 : ℝ)|=(1845665377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434045587/10000000000 : ℝ)|^4551 ≤ (45521981845043/100000000000000 : ℝ)^3527
        have hw : |(5434045587/10000000000 : ℝ)|=(5434045587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303969627/2500000000 : ℝ)|^4551 ≤ (43177616270409/100000000000000 : ℝ)^3527
        have hw : |(1303969627/2500000000 : ℝ)|=(1303969627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_1 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351468053/10000000000 : ℝ)*x 0 + (-391486219/2000000000 : ℝ)*x 1 + (521587841/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351468053/10000000000 : ℝ)^4551 ≤ (11157837310973/25000000000000 : ℝ)^3527 := by
    have hnat : (5351468053 : ℕ)^4551*25000000000000^3527 ≤ 11157837310973^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351468053 10000000000 11157837310973 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391486219/2000000000 : ℝ)^4551 ≤ (761939720063/6250000000000 : ℝ)^3527 := by
    have hnat : (391486219 : ℕ)^4551*6250000000000^3527 ≤ 761939720063^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391486219 2000000000 761939720063 6250000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521587841/1000000000 : ℝ)^4551 ≤ (43177615223621/100000000000000 : ℝ)^3527 := by
    have hnat : (521587841 : ℕ)^4551*100000000000000^3527 ≤ 43177615223621^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521587841 1000000000 43177615223621 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351468053/10000000000 : ℝ), (-391486219/2000000000 : ℝ), (521587841/1000000000 : ℝ)] ![(11157837310973/25000000000000 : ℝ), (761939720063/6250000000000 : ℝ), (43177615223621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351468053/10000000000 : ℝ)|^4551 ≤ (11157837310973/25000000000000 : ℝ)^3527
        have hw : |(5351468053/10000000000 : ℝ)|=(5351468053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391486219/2000000000 : ℝ)|^4551 ≤ (761939720063/6250000000000 : ℝ)^3527
        have hw : |(-391486219/2000000000 : ℝ)|=(391486219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521587841/1000000000 : ℝ)|^4551 ≤ (43177615223621/100000000000000 : ℝ)^3527
        have hw : |(521587841/1000000000 : ℝ)|=(521587841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_2 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675734099/5000000000 : ℝ)*x 0 + (325992389/625000000 : ℝ)*x 1 + (-1957431149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675734099/5000000000 : ℝ)^4551 ≤ (22315675402147/50000000000000 : ℝ)^3527 := by
    have hnat : (2675734099 : ℕ)^4551*50000000000000^3527 ≤ 22315675402147^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675734099 5000000000 22315675402147 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325992389/625000000 : ℝ)^4551 ≤ (43177613236861/100000000000000 : ℝ)^3527 := by
    have hnat : (325992389 : ℕ)^4551*100000000000000^3527 ≤ 43177613236861^3527*625000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325992389 625000000 43177613236861 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1957431149/10000000000 : ℝ)^4551 ≤ (12191035954967/100000000000000 : ℝ)^3527 := by
    have hnat : (1957431149 : ℕ)^4551*100000000000000^3527 ≤ 12191035954967^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957431149 10000000000 12191035954967 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675734099/5000000000 : ℝ), (325992389/625000000 : ℝ), (-1957431149/10000000000 : ℝ)] ![(22315675402147/50000000000000 : ℝ), (43177613236861/100000000000000 : ℝ), (12191035954967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675734099/5000000000 : ℝ)|^4551 ≤ (22315675402147/50000000000000 : ℝ)^3527
        have hw : |(2675734099/5000000000 : ℝ)|=(2675734099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325992389/625000000 : ℝ)|^4551 ≤ (43177613236861/100000000000000 : ℝ)^3527
        have hw : |(325992389/625000000 : ℝ)|=(325992389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1957431149/10000000000 : ℝ)|^4551 ≤ (12191035954967/100000000000000 : ℝ)^3527
        have hw : |(-1957431149/10000000000 : ℝ)|=(1957431149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_3 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852515187/2000000000 : ℝ)*x 0 + (100468717/250000000 : ℝ)*x 1 + (141209221/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852515187/2000000000 : ℝ)^4551 ≤ (4159721083913/12500000000000 : ℝ)^3527 := by
    have hnat : (852515187 : ℕ)^4551*12500000000000^3527 ≤ 4159721083913^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852515187 2000000000 4159721083913 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100468717/250000000 : ℝ)^4551 ≤ (30842236270233/100000000000000 : ℝ)^3527 := by
    have hnat : (100468717 : ℕ)^4551*100000000000000^3527 ≤ 30842236270233^3527*250000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100468717 250000000 30842236270233 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141209221/312500000 : ℝ)^4551 ≤ (8969998761837/25000000000000 : ℝ)^3527 := by
    have hnat : (141209221 : ℕ)^4551*25000000000000^3527 ≤ 8969998761837^3527*312500000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141209221 312500000 8969998761837 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852515187/2000000000 : ℝ), (100468717/250000000 : ℝ), (141209221/312500000 : ℝ)] ![(4159721083913/12500000000000 : ℝ), (30842236270233/100000000000000 : ℝ), (8969998761837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852515187/2000000000 : ℝ)|^4551 ≤ (4159721083913/12500000000000 : ℝ)^3527
        have hw : |(852515187/2000000000 : ℝ)|=(852515187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100468717/250000000 : ℝ)|^4551 ≤ (30842236270233/100000000000000 : ℝ)^3527
        have hw : |(100468717/250000000 : ℝ)|=(100468717/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141209221/312500000 : ℝ)|^4551 ≤ (8969998761837/25000000000000 : ℝ)^3527
        have hw : |(141209221/312500000 : ℝ)|=(141209221/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_4 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845695979/10000000000 : ℝ)*x 0 + (2608516121/5000000000 : ℝ)*x 1 + (2716441529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845695979/10000000000 : ℝ)^4551 ≤ (706290227661/6250000000000 : ℝ)^3527 := by
    have hnat : (1845695979 : ℕ)^4551*6250000000000^3527 ≤ 706290227661^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845695979 10000000000 706290227661 6250000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608516121/5000000000 : ℝ)^4551 ≤ (8637988057017/20000000000000 : ℝ)^3527 := by
    have hnat : (2608516121 : ℕ)^4551*20000000000000^3527 ≤ 8637988057017^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608516121 5000000000 8637988057017 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716441529/5000000000 : ℝ)^4551 ≤ (45509416061719/100000000000000 : ℝ)^3527 := by
    have hnat : (2716441529 : ℕ)^4551*100000000000000^3527 ≤ 45509416061719^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716441529 5000000000 45509416061719 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845695979/10000000000 : ℝ), (2608516121/5000000000 : ℝ), (2716441529/5000000000 : ℝ)] ![(706290227661/6250000000000 : ℝ), (8637988057017/20000000000000 : ℝ), (45509416061719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845695979/10000000000 : ℝ)|^4551 ≤ (706290227661/6250000000000 : ℝ)^3527
        have hw : |(-1845695979/10000000000 : ℝ)|=(1845695979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608516121/5000000000 : ℝ)|^4551 ≤ (8637988057017/20000000000000 : ℝ)^3527
        have hw : |(2608516121/5000000000 : ℝ)|=(2608516121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716441529/5000000000 : ℝ)|^4551 ≤ (45509416061719/100000000000000 : ℝ)^3527
        have hw : |(2716441529/5000000000 : ℝ)|=(2716441529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_5 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647034611/5000000000 : ℝ)*x 0 + (-435106599/2500000000 : ℝ)*x 1 + (5432883053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647034611/5000000000 : ℝ)^4551 ≤ (22007311064299/50000000000000 : ℝ)^3527 := by
    have hnat : (2647034611 : ℕ)^4551*50000000000000^3527 ≤ 22007311064299^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647034611 5000000000 22007311064299 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435106599/2500000000 : ℝ)^4551 ≤ (10475961854131/100000000000000 : ℝ)^3527 := by
    have hnat : (435106599 : ℕ)^4551*100000000000000^3527 ≤ 10475961854131^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435106599 2500000000 10475961854131 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432883053/10000000000 : ℝ)^4551 ≤ (11377354001919/25000000000000 : ℝ)^3527 := by
    have hnat : (5432883053 : ℕ)^4551*25000000000000^3527 ≤ 11377354001919^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432883053 10000000000 11377354001919 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647034611/5000000000 : ℝ), (-435106599/2500000000 : ℝ), (5432883053/10000000000 : ℝ)] ![(22007311064299/50000000000000 : ℝ), (10475961854131/100000000000000 : ℝ), (11377354001919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647034611/5000000000 : ℝ)|^4551 ≤ (22007311064299/50000000000000 : ℝ)^3527
        have hw : |(2647034611/5000000000 : ℝ)|=(2647034611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435106599/2500000000 : ℝ)|^4551 ≤ (10475961854131/100000000000000 : ℝ)^3527
        have hw : |(-435106599/2500000000 : ℝ)|=(435106599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432883053/10000000000 : ℝ)|^4551 ≤ (11377354001919/25000000000000 : ℝ)^3527
        have hw : |(5432883053/10000000000 : ℝ)|=(5432883053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_6 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294069319/10000000000 : ℝ)*x 0 + (2716441489/5000000000 : ℝ)*x 1 + (-870213183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294069319/10000000000 : ℝ)^4551 ≤ (4401462316919/10000000000000 : ℝ)^3527 := by
    have hnat : (5294069319 : ℕ)^4551*10000000000000^3527 ≤ 4401462316919^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294069319 10000000000 4401462316919 10000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716441489/5000000000 : ℝ)^4551 ≤ (22754707598513/50000000000000 : ℝ)^3527 := by
    have hnat : (2716441489 : ℕ)^4551*50000000000000^3527 ≤ 22754707598513^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716441489 5000000000 22754707598513 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870213183/5000000000 : ℝ)^4551 ≤ (1309495202641/12500000000000 : ℝ)^3527 := by
    have hnat : (870213183 : ℕ)^4551*12500000000000^3527 ≤ 1309495202641^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870213183 5000000000 1309495202641 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294069319/10000000000 : ℝ), (2716441489/5000000000 : ℝ), (-870213183/5000000000 : ℝ)] ![(4401462316919/10000000000000 : ℝ), (22754707598513/50000000000000 : ℝ), (1309495202641/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294069319/10000000000 : ℝ)|^4551 ≤ (4401462316919/10000000000000 : ℝ)^3527
        have hw : |(5294069319/10000000000 : ℝ)|=(5294069319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716441489/5000000000 : ℝ)|^4551 ≤ (22754707598513/50000000000000 : ℝ)^3527
        have hw : |(2716441489/5000000000 : ℝ)|=(2716441489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-870213183/5000000000 : ℝ)|^4551 ≤ (1309495202641/12500000000000 : ℝ)^3527
        have hw : |(-870213183/5000000000 : ℝ)|=(870213183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s3_7 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133207687/312500000 : ℝ)*x 0 + (225802541/500000000 : ℝ)*x 1 + (251338297/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133207687/312500000 : ℝ)^4551 ≤ (4159809289569/12500000000000 : ℝ)^3527 := by
    have hnat : (133207687 : ℕ)^4551*12500000000000^3527 ≤ 4159809289569^3527*312500000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133207687 312500000 4159809289569 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225802541/500000000 : ℝ)^4551 ≤ (2240806574613/6250000000000 : ℝ)^3527 := by
    have hnat : (225802541 : ℕ)^4551*6250000000000^3527 ≤ 2240806574613^3527*500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225802541 500000000 2240806574613 6250000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251338297/625000000 : ℝ)^4551 ≤ (30868620482391/100000000000000 : ℝ)^3527 := by
    have hnat : (251338297 : ℕ)^4551*100000000000000^3527 ≤ 30868620482391^3527*625000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251338297 625000000 30868620482391 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133207687/312500000 : ℝ), (225802541/500000000 : ℝ), (251338297/625000000 : ℝ)] ![(4159809289569/12500000000000 : ℝ), (2240806574613/6250000000000 : ℝ), (30868620482391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133207687/312500000 : ℝ)|^4551 ≤ (4159809289569/12500000000000 : ℝ)^3527
        have hw : |(133207687/312500000 : ℝ)|=(133207687/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225802541/500000000 : ℝ)|^4551 ≤ (2240806574613/6250000000000 : ℝ)^3527
        have hw : |(225802541/500000000 : ℝ)|=(225802541/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251338297/625000000 : ℝ)|^4551 ≤ (30868620482391/100000000000000 : ℝ)^3527
        have hw : |(251338297/625000000 : ℝ)|=(251338297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1527_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10919/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15541/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7971/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10551/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7971/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10551/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7971/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10551/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7971/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10551/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7971/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10551/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7971/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10551/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10551/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (2291217841516167/50000000000000000000 : ℝ) := by
    have hpowers : (10551/100000 : ℝ)^4549 ≤ (2291217841516167/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10551 : ℕ)^4549*50000000000000000000^1024 ≤ 2291217841516167^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10551 100000 2291217841516167 50000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10551/100000 : ℝ)) (X := (2291217841516167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7971/50000 : ℝ) ^ (4549/1024 : ℝ) ≤ (7166875678775243/25000000000000000000 : ℝ) := by
    have hpowers : (7971/50000 : ℝ)^4549 ≤ (7166875678775243/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7971 : ℕ)^4549*25000000000000000000^1024 ≤ 7166875678775243^1024*50000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7971 50000 7166875678775243 25000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7971/50000 : ℝ)) (X := (7166875678775243/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002291217841516167/25000000000000000000 : ℝ) ≤ (10000206297978681/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (25002291217841516167/25000000000000000000 : ℝ)^1024 ≤ (10000206297978681/10000000000000000 : ℝ)^4549 := by
      have hnat : (25002291217841516167 : ℕ)^1024*10000000000000000^4549 ≤ 10000206297978681^4549*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002291217841516167 25000000000000000000 10000206297978681 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000206297978681/10000000000000000 : ℝ)) (X := (25002291217841516167/25000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016624969199066653/50000000000000000000 : ℝ) ≤ (2500187093600339/2500000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (50016624969199066653/50000000000000000000 : ℝ)^1024 ≤ (2500187093600339/2500000000000000 : ℝ)^4549 := by
      have hnat : (50016624969199066653 : ℕ)^1024*2500000000000000^4549 ≤ 2500187093600339^4549*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016624969199066653 50000000000000000000 2500187093600339 2500000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500187093600339/2500000000000000 : ℝ)) (X := (50016624969199066653/50000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507166875678775243/12500000000000000000 : ℝ) ≤ (10001290450824031/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (12507166875678775243/12500000000000000000 : ℝ)^1024 ≤ (10001290450824031/10000000000000000 : ℝ)^4549 := by
      have hnat : (12507166875678775243 : ℕ)^1024*10000000000000000^4549 ≤ 10001290450824031^4549*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507166875678775243 12500000000000000000 10001290450824031 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290450824031/10000000000000000 : ℝ)) (X := (12507166875678775243/12500000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2291217841516167/50000000000000000000 : ℝ) ≤ ((17966557751910593807/17970000000000000000 : ℝ)+2*(21683056907/21564000000000 : ℝ)*(10551/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (17966557751910593807/17970000000000000000 : ℝ)+2*(21683056907/21564000000000 : ℝ)*(10551/100000 : ℝ)=(10000206297978681/10000000000000000 : ℝ) by norm_num, show 1+2*(2291217841516167/50000000000000000000 : ℝ)=(25002291217841516167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7166875678775243/25000000000000000000 : ℝ)+(2291217841516167/50000000000000000000 : ℝ) ≤ ((17966557751910593807/17970000000000000000 : ℝ)+(21683056907/21564000000000 : ℝ)*((7971/50000 : ℝ)+(10551/100000 : ℝ)))^(4549/1024 : ℝ) := by
    rw [show (17966557751910593807/17970000000000000000 : ℝ)+(21683056907/21564000000000 : ℝ)*((7971/50000 : ℝ)+(10551/100000 : ℝ))=(2500187093600339/2500000000000000 : ℝ) by norm_num, show 1+(7166875678775243/25000000000000000000 : ℝ)+(2291217841516167/50000000000000000000 : ℝ)=(50016624969199066653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7166875678775243/25000000000000000000 : ℝ) ≤ ((17966557751910593807/17970000000000000000 : ℝ)+2*(21683056907/21564000000000 : ℝ)*(7971/50000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (17966557751910593807/17970000000000000000 : ℝ)+2*(21683056907/21564000000000 : ℝ)*(7971/50000 : ℝ)=(10001290450824031/10000000000000000 : ℝ) by norm_num, show 1+2*(7166875678775243/25000000000000000000 : ℝ)=(12507166875678775243/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17966557751910593807/17970000000000000000 : ℝ)*(X 1 0+X 2 0)+(21683056907/21564000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (10551/100000 : ℝ)) (hi := (7971/50000 : ℝ)) (c := (17966557751910593807/17970000000000000000 : ℝ)) (alpha := (21683056907/21564000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17966557751910593807/17970000000000000000 : ℝ)*(X 0 1+X 2 1)+(21683056907/21564000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (10551/100000 : ℝ)) (hi := (7971/50000 : ℝ)) (c := (17966557751910593807/17970000000000000000 : ℝ)) (alpha := (21683056907/21564000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17966557751910593807/17970000000000000000 : ℝ)*(X 0 2+X 1 2)+(21683056907/21564000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (10551/100000 : ℝ)) (hi := (7971/50000 : ℝ)) (c := (17966557751910593807/17970000000000000000 : ℝ)) (alpha := (21683056907/21564000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1845665377/10000000000 : ℝ)*X 0 0+(5434045587/10000000000 : ℝ)*X 0 1+(1303969627/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351468053/10000000000 : ℝ)*X 1 0+(-391486219/2000000000 : ℝ)*X 1 1+(521587841/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675734099/5000000000 : ℝ)*X 2 0+(325992389/625000000 : ℝ)*X 2 1+(-1957431149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((852515187/2000000000 : ℝ)*X 0 0+(100468717/250000000 : ℝ)*X 0 1+(141209221/312500000 : ℝ)*X 0 2+(852515187/2000000000 : ℝ)*X 1 0+(100468717/250000000 : ℝ)*X 1 1+(141209221/312500000 : ℝ)*X 1 2+(852515187/2000000000 : ℝ)*X 2 0+(100468717/250000000 : ℝ)*X 2 1+(141209221/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1845695979/10000000000 : ℝ)*X 0 0+(2608516121/5000000000 : ℝ)*X 0 1+(2716441529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647034611/5000000000 : ℝ)*X 1 0+(-435106599/2500000000 : ℝ)*X 1 1+(5432883053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294069319/10000000000 : ℝ)*X 2 0+(2716441489/5000000000 : ℝ)*X 2 1+(-870213183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((133207687/312500000 : ℝ)*X 0 0+(225802541/500000000 : ℝ)*X 0 1+(251338297/625000000 : ℝ)*X 0 2+(133207687/312500000 : ℝ)*X 1 0+(225802541/500000000 : ℝ)*X 1 1+(251338297/625000000 : ℝ)*X 1 2+(133207687/312500000 : ℝ)*X 2 0+(225802541/500000000 : ℝ)*X 2 1+(251338297/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5482356997063460869535400763/449250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77760493/4000000000000 : ℝ)*(base19) + (225029309/12500000000000 : ℝ)*(base23) + (71702931/50000000000000 : ℝ)*(lower2) + (31621481/10000000000000 : ℝ)*(upper3) + (88031217/100000000000000 : ℝ)*(upper5) + (1645984918073497/50000000000000 : ℝ)*(major0) + (1645984918073497/50000000000000 : ℝ)*(major1) + (1645984918073497/50000000000000 : ℝ)*(major2) + (229183615785553/5000000000000 : ℝ)*(sp0) + (4583696587926873/100000000000000 : ℝ)*(sp1) + (2291848365852363/50000000000000 : ℝ)*(sp2) + (1000112880865849/50000000000000 : ℝ)*(sp3) + (13108114069/50000000000000 : ℝ)*(sp4) + (2994368919/20000000000000 : ℝ)*(sp7) + (500060183394073/25000000000000 : ℝ)*(f.failure) + (4583698531939199/100000000000000 : ℝ)*(f.sum) + (8482793450459/2695500000000000000000000000 : ℝ)*base66 + (5600838164166599237/2695500000000000000000000000000000 : ℝ)*base67 + (11773702589525400763/2695500000000000000000000000000000 : ℝ)*base70 + (8653338415929900763/2695500000000000000000000000000000 : ℝ)*base72 + (6496762676753/1078200000000000000000000000 : ℝ)*base74 + (16948123679781599237/2695500000000000000000000000000000 : ℝ)*base75 + (9795700060425599237/2695500000000000000000000000000000 : ℝ)*base77 + (46552035903102599237/2695500000000000000000000000000000 : ℝ)*base79 + (505089703957/336937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14524107/1250000000000000000000 : ℝ)*base90 + (14524107/1250000000000000000000 : ℝ)*base92 + (14524107/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1275820259787271541887551043/224625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (867816481/100000000000000 : ℝ)*(base19) + (289407093/25000000000000 : ℝ)*(base23) + (53862249/50000000000000 : ℝ)*(upper3) + (88263591/100000000000000 : ℝ)*(lower4) + (53685111/50000000000000 : ℝ)*(upper5) + (831813568677061/25000000000000 : ℝ)*(major0) + (831813568677061/25000000000000 : ℝ)*(major1) + (831813568677061/25000000000000 : ℝ)*(major2) + (13193313259/100000000000000 : ℝ)*(sp1) + (8358567587/50000000000000 : ℝ)*(sp2) + (1158207093599851/25000000000000 : ℝ)*(sp4) + (144775447289677/3125000000000 : ℝ)*(sp5) + (2316405249817929/50000000000000 : ℝ)*(sp6) + (1010839992845563/50000000000000 : ℝ)*(sp7) + (1010839992845563/50000000000000 : ℝ)*(f.failure) + (1158207093599851/25000000000000 : ℝ)*(f.sum) + (843787019069/673875000000000000000000000 : ℝ)*base65 + (7786783891245816319/1347750000000000000000000000000000 : ℝ)*base68 + (8214329405379816319/1347750000000000000000000000000000 : ℝ)*base70 + (4627424772276066319/1347750000000000000000000000000000 : ℝ)*base72 + (9958797302921/5391000000000000000000000000 : ℝ)*base74 + (10414591861742316319/1347750000000000000000000000000000 : ℝ)*base76 + (2888478230633316319/1347750000000000000000000000000000 : ℝ)*base78 + (23695749331698816319/1347750000000000000000000000000000 : ℝ)*base80 + (3022764471761/2695500000000000000000000000 : ℝ)*base81 + (5956017/2500000000000000000000 : ℝ)*base90 + (5956017/2500000000000000000000 : ℝ)*base92 + (5956017/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1527_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15541/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1527_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1527_s4_0 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-461508959/2500000000 : ℝ)*x 0 + (5431607121/10000000000 : ℝ)*x 1 + (2609035927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461508959/2500000000 : ℝ)^4551 ≤ (11303328691587/100000000000000 : ℝ)^3527 := by
    have hnat : (461508959 : ℕ)^4551*100000000000000^3527 ≤ 11303328691587^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461508959 2500000000 11303328691587 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431607121/10000000000 : ℝ)^4551 ≤ (45495625349181/100000000000000 : ℝ)^3527 := by
    have hnat : (5431607121 : ℕ)^4551*100000000000000^3527 ≤ 45495625349181^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431607121 10000000000 45495625349181 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609035927/5000000000 : ℝ)^4551 ≤ (43201045943331/100000000000000 : ℝ)^3527 := by
    have hnat : (2609035927 : ℕ)^4551*100000000000000^3527 ≤ 43201045943331^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609035927 5000000000 43201045943331 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-461508959/2500000000 : ℝ), (5431607121/10000000000 : ℝ), (2609035927/5000000000 : ℝ)] ![(11303328691587/100000000000000 : ℝ), (45495625349181/100000000000000 : ℝ), (43201045943331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-461508959/2500000000 : ℝ)|^4551 ≤ (11303328691587/100000000000000 : ℝ)^3527
        have hw : |(-461508959/2500000000 : ℝ)|=(461508959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431607121/10000000000 : ℝ)|^4551 ≤ (45495625349181/100000000000000 : ℝ)^3527
        have hw : |(5431607121/10000000000 : ℝ)|=(5431607121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609035927/5000000000 : ℝ)|^4551 ≤ (43201045943331/100000000000000 : ℝ)^3527
        have hw : |(2609035927/5000000000 : ℝ)|=(2609035927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_1 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350827319/10000000000 : ℝ)*x 0 + (-1955373413/10000000000 : ℝ)*x 1 + (2609035831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350827319/10000000000 : ℝ)^4551 ≤ (8924890834789/20000000000000 : ℝ)^3527 := by
    have hnat : (5350827319 : ℕ)^4551*20000000000000^3527 ≤ 8924890834789^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350827319 10000000000 8924890834789 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955373413/10000000000 : ℝ)^4551 ≤ (2434900384001/20000000000000 : ℝ)^3527 := by
    have hnat : (1955373413 : ℕ)^4551*20000000000000^3527 ≤ 2434900384001^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955373413 10000000000 2434900384001 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609035831/5000000000 : ℝ)^4551 ≤ (43201043892231/100000000000000 : ℝ)^3527 := by
    have hnat : (2609035831 : ℕ)^4551*100000000000000^3527 ≤ 43201043892231^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609035831 5000000000 43201043892231 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350827319/10000000000 : ℝ), (-1955373413/10000000000 : ℝ), (2609035831/5000000000 : ℝ)] ![(8924890834789/20000000000000 : ℝ), (2434900384001/20000000000000 : ℝ), (43201043892231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350827319/10000000000 : ℝ)|^4551 ≤ (8924890834789/20000000000000 : ℝ)^3527
        have hw : |(5350827319/10000000000 : ℝ)|=(5350827319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955373413/10000000000 : ℝ)|^4551 ≤ (2434900384001/20000000000000 : ℝ)^3527
        have hw : |(-1955373413/10000000000 : ℝ)|=(1955373413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609035831/5000000000 : ℝ)|^4551 ≤ (43201043892231/100000000000000 : ℝ)^3527
        have hw : |(2609035831/5000000000 : ℝ)|=(2609035831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_2 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675413499/5000000000 : ℝ)*x 0 + (5218072353/10000000000 : ℝ)*x 1 + (-1955372923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675413499/5000000000 : ℝ)^4551 ≤ (22312225359829/50000000000000 : ℝ)^3527 := by
    have hnat : (2675413499 : ℕ)^4551*50000000000000^3527 ≤ 22312225359829^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675413499 5000000000 22312225359829 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218072353/10000000000 : ℝ)^4551 ≤ (21600525637027/50000000000000 : ℝ)^3527 := by
    have hnat : (5218072353 : ℕ)^4551*50000000000000^3527 ≤ 21600525637027^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218072353 10000000000 21600525637027 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955372923/10000000000 : ℝ)^4551 ≤ (6087248991713/50000000000000 : ℝ)^3527 := by
    have hnat : (1955372923 : ℕ)^4551*50000000000000^3527 ≤ 6087248991713^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955372923 10000000000 6087248991713 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675413499/5000000000 : ℝ), (5218072353/10000000000 : ℝ), (-1955372923/10000000000 : ℝ)] ![(22312225359829/50000000000000 : ℝ), (21600525637027/50000000000000 : ℝ), (6087248991713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675413499/5000000000 : ℝ)|^4551 ≤ (22312225359829/50000000000000 : ℝ)^3527
        have hw : |(2675413499/5000000000 : ℝ)|=(2675413499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218072353/10000000000 : ℝ)|^4551 ≤ (21600525637027/50000000000000 : ℝ)^3527
        have hw : |(5218072353/10000000000 : ℝ)|=(5218072353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1955372923/10000000000 : ℝ)|^4551 ≤ (6087248991713/50000000000000 : ℝ)^3527
        have hw : |(-1955372923/10000000000 : ℝ)|=(1955372923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_3 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106570173/250000000 : ℝ)*x 0 + (251501893/625000000 : ℝ)*x 1 + (112834031/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106570173/250000000 : ℝ)^4551 ≤ (33280095533371/100000000000000 : ℝ)^3527 := by
    have hnat : (106570173 : ℕ)^4551*100000000000000^3527 ≤ 33280095533371^3527*250000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106570173 250000000 33280095533371 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251501893/625000000 : ℝ)^4551 ≤ (30894548758173/100000000000000 : ℝ)^3527 := by
    have hnat : (251501893 : ℕ)^4551*100000000000000^3527 ≤ 30894548758173^3527*625000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251501893 625000000 30894548758173 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112834031/250000000 : ℝ)^4551 ≤ (7165071137497/20000000000000 : ℝ)^3527 := by
    have hnat : (112834031 : ℕ)^4551*20000000000000^3527 ≤ 7165071137497^3527*250000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112834031 250000000 7165071137497 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106570173/250000000 : ℝ), (251501893/625000000 : ℝ), (112834031/250000000 : ℝ)] ![(33280095533371/100000000000000 : ℝ), (30894548758173/100000000000000 : ℝ), (7165071137497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106570173/250000000 : ℝ)|^4551 ≤ (33280095533371/100000000000000 : ℝ)^3527
        have hw : |(106570173/250000000 : ℝ)|=(106570173/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251501893/625000000 : ℝ)|^4551 ≤ (30894548758173/100000000000000 : ℝ)^3527
        have hw : |(251501893/625000000 : ℝ)|=(251501893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112834031/250000000 : ℝ)|^4551 ≤ (7165071137497/20000000000000 : ℝ)^3527
        have hw : |(112834031/250000000 : ℝ)|=(112834031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_4 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1846064873/10000000000 : ℝ)*x 0 + (1304794367/2500000000 : ℝ)*x 1 + (2715246507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1846064873/10000000000 : ℝ)^4551 ≤ (11303558105811/100000000000000 : ℝ)^3527 := by
    have hnat : (1846064873 : ℕ)^4551*100000000000000^3527 ≤ 11303558105811^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846064873 10000000000 11303558105811 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304794367/2500000000 : ℝ)^4551 ≤ (43212857373017/100000000000000 : ℝ)^3527 := by
    have hnat : (1304794367 : ℕ)^4551*100000000000000^3527 ≤ 43212857373017^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304794367 2500000000 43212857373017 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715246507/5000000000 : ℝ)^4551 ≤ (9096716902663/20000000000000 : ℝ)^3527 := by
    have hnat : (2715246507 : ℕ)^4551*20000000000000^3527 ≤ 9096716902663^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715246507 5000000000 9096716902663 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1846064873/10000000000 : ℝ), (1304794367/2500000000 : ℝ), (2715246507/5000000000 : ℝ)] ![(11303558105811/100000000000000 : ℝ), (43212857373017/100000000000000 : ℝ), (9096716902663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1846064873/10000000000 : ℝ)|^4551 ≤ (11303558105811/100000000000000 : ℝ)^3527
        have hw : |(-1846064873/10000000000 : ℝ)|=(1846064873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304794367/2500000000 : ℝ)|^4551 ≤ (43212857373017/100000000000000 : ℝ)^3527
        have hw : |(1304794367/2500000000 : ℝ)|=(1304794367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715246507/5000000000 : ℝ)|^4551 ≤ (9096716902663/20000000000000 : ℝ)^3527
        have hw : |(2715246507/5000000000 : ℝ)|=(2715246507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_5 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294648149/10000000000 : ℝ)*x 0 + (-871476009/5000000000 : ℝ)*x 1 + (2715246543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294648149/10000000000 : ℝ)^4551 ≤ (11005208203163/25000000000000 : ℝ)^3527 := by
    have hnat : (5294648149 : ℕ)^4551*25000000000000^3527 ≤ 11005208203163^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294648149 10000000000 11005208203163 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871476009/5000000000 : ℝ)^4551 ≤ (5247790936511/50000000000000 : ℝ)^3527 := by
    have hnat : (871476009 : ℕ)^4551*50000000000000^3527 ≤ 5247790936511^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871476009 5000000000 5247790936511 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715246543/5000000000 : ℝ)^4551 ≤ (568544816143/1250000000000 : ℝ)^3527 := by
    have hnat : (2715246543 : ℕ)^4551*1250000000000^3527 ≤ 568544816143^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715246543 5000000000 568544816143 1250000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294648149/10000000000 : ℝ), (-871476009/5000000000 : ℝ), (2715246543/5000000000 : ℝ)] ![(11005208203163/25000000000000 : ℝ), (5247790936511/50000000000000 : ℝ), (568544816143/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294648149/10000000000 : ℝ)|^4551 ≤ (11005208203163/25000000000000 : ℝ)^3527
        have hw : |(5294648149/10000000000 : ℝ)|=(5294648149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-871476009/5000000000 : ℝ)|^4551 ≤ (5247790936511/50000000000000 : ℝ)^3527
        have hw : |(-871476009/5000000000 : ℝ)|=(871476009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715246543/5000000000 : ℝ)|^4551 ≤ (568544816143/1250000000000 : ℝ)^3527
        have hw : |(2715246543/5000000000 : ℝ)|=(2715246543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_6 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26473241/50000000 : ℝ)*x 0 + (1357623267/2500000000 : ℝ)*x 1 + (-1742951973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26473241/50000000 : ℝ)^4551 ≤ (5502604169973/12500000000000 : ℝ)^3527 := by
    have hnat : (26473241 : ℕ)^4551*12500000000000^3527 ≤ 5502604169973^3527*50000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26473241 50000000 5502604169973 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357623267/2500000000 : ℝ)^4551 ≤ (11370896274227/25000000000000 : ℝ)^3527 := by
    have hnat : (1357623267 : ℕ)^4551*25000000000000^3527 ≤ 11370896274227^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357623267 2500000000 11370896274227 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1742951973/10000000000 : ℝ)^4551 ≤ (10495581523371/100000000000000 : ℝ)^3527 := by
    have hnat : (1742951973 : ℕ)^4551*100000000000000^3527 ≤ 10495581523371^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742951973 10000000000 10495581523371 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26473241/50000000 : ℝ), (1357623267/2500000000 : ℝ), (-1742951973/10000000000 : ℝ)] ![(5502604169973/12500000000000 : ℝ), (11370896274227/25000000000000 : ℝ), (10495581523371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26473241/50000000 : ℝ)|^4551 ≤ (5502604169973/12500000000000 : ℝ)^3527
        have hw : |(26473241/50000000 : ℝ)|=(26473241/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357623267/2500000000 : ℝ)|^4551 ≤ (11370896274227/25000000000000 : ℝ)^3527
        have hw : |(1357623267/2500000000 : ℝ)|=(1357623267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1742951973/10000000000 : ℝ)|^4551 ≤ (10495581523371/100000000000000 : ℝ)^3527
        have hw : |(-1742951973/10000000000 : ℝ)|=(1742951973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s4_7 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426287311/1000000000 : ℝ)*x 0 + (1127706853/2500000000 : ℝ)*x 1 + (805316441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426287311/1000000000 : ℝ)^4551 ≤ (33280762315019/100000000000000 : ℝ)^3527 := by
    have hnat : (426287311 : ℕ)^4551*100000000000000^3527 ≤ 33280762315019^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426287311 1000000000 33280762315019 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127706853/2500000000 : ℝ)^4551 ≤ (35799405916883/100000000000000 : ℝ)^3527 := by
    have hnat : (1127706853 : ℕ)^4551*100000000000000^3527 ≤ 35799405916883^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127706853 2500000000 35799405916883 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805316441/2000000000 : ℝ)^4551 ≤ (15459915876317/50000000000000 : ℝ)^3527 := by
    have hnat : (805316441 : ℕ)^4551*50000000000000^3527 ≤ 15459915876317^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805316441 2000000000 15459915876317 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426287311/1000000000 : ℝ), (1127706853/2500000000 : ℝ), (805316441/2000000000 : ℝ)] ![(33280762315019/100000000000000 : ℝ), (35799405916883/100000000000000 : ℝ), (15459915876317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426287311/1000000000 : ℝ)|^4551 ≤ (33280762315019/100000000000000 : ℝ)^3527
        have hw : |(426287311/1000000000 : ℝ)|=(426287311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127706853/2500000000 : ℝ)|^4551 ≤ (35799405916883/100000000000000 : ℝ)^3527
        have hw : |(1127706853/2500000000 : ℝ)|=(1127706853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805316441/2000000000 : ℝ)|^4551 ≤ (15459915876317/50000000000000 : ℝ)^3527
        have hw : |(805316441/2000000000 : ℝ)|=(805316441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1527_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5483/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10919/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10919/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10919/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10919/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10919/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10919/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10919/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (42690386044653/800000000000000000 : ℝ) := by
    have hpowers : (10919/100000 : ℝ)^4549 ≤ (42690386044653/800000000000000000 : ℝ)^1024 := by
      have hnat : (10919 : ℕ)^4549*800000000000000000^1024 ≤ 42690386044653^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10919 100000 42690386044653 800000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10919/100000 : ℝ)) (X := (42690386044653/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15541/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (6400000958143161/25000000000000000000 : ℝ) := by
    have hpowers : (15541/100000 : ℝ)^4549 ≤ (6400000958143161/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15541 : ℕ)^4549*25000000000000000000^1024 ≤ 6400000958143161^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15541 100000 6400000958143161 25000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15541/100000 : ℝ)) (X := (6400000958143161/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (400042690386044653/400000000000000000 : ℝ) ≤ (2000048046985907/2000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (400042690386044653/400000000000000000 : ℝ)^1024 ≤ (2000048046985907/2000000000000000 : ℝ)^4549 := by
      have hnat : (400042690386044653 : ℕ)^1024*2000000000000000^4549 ≤ 2000048046985907^4549*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400042690386044653 400000000000000000 2000048046985907 2000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000048046985907/2000000000000000 : ℝ)) (X := (400042690386044653/400000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030936302088154269/100000000000000000000 : ℝ) ≤ (10000696306373959/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (100030936302088154269/100000000000000000000 : ℝ)^1024 ≤ (10000696306373959/10000000000000000 : ℝ)^4549 := by
      have hnat : (100030936302088154269 : ℕ)^1024*10000000000000000^4549 ≤ 10000696306373959^4549*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030936302088154269 100000000000000000000 10000696306373959 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000696306373959/10000000000000000 : ℝ)) (X := (100030936302088154269/100000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506400000958143161/12500000000000000000 : ℝ) ≤ (10001152377818383/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (12506400000958143161/12500000000000000000 : ℝ)^1024 ≤ (10001152377818383/10000000000000000 : ℝ)^4549 := by
      have hnat : (12506400000958143161 : ℕ)^1024*10000000000000000^4549 ≤ 10001152377818383^4549*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506400000958143161 12500000000000000000 10001152377818383 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001152377818383/10000000000000000 : ℝ)) (X := (12506400000958143161/12500000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(42690386044653/800000000000000000 : ℝ) ≤ ((23105575338820489729/23110000000000000000 : ℝ)+2*(57008930553/57775000000000 : ℝ)*(10919/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (23105575338820489729/23110000000000000000 : ℝ)+2*(57008930553/57775000000000 : ℝ)*(10919/100000 : ℝ)=(2000048046985907/2000000000000000 : ℝ) by norm_num, show 1+2*(42690386044653/800000000000000000 : ℝ)=(400042690386044653/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6400000958143161/25000000000000000000 : ℝ)+(42690386044653/800000000000000000 : ℝ) ≤ ((23105575338820489729/23110000000000000000 : ℝ)+(57008930553/57775000000000 : ℝ)*((15541/100000 : ℝ)+(10919/100000 : ℝ)))^(4549/1024 : ℝ) := by
    rw [show (23105575338820489729/23110000000000000000 : ℝ)+(57008930553/57775000000000 : ℝ)*((15541/100000 : ℝ)+(10919/100000 : ℝ))=(10000696306373959/10000000000000000 : ℝ) by norm_num, show 1+(6400000958143161/25000000000000000000 : ℝ)+(42690386044653/800000000000000000 : ℝ)=(100030936302088154269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6400000958143161/25000000000000000000 : ℝ) ≤ ((23105575338820489729/23110000000000000000 : ℝ)+2*(57008930553/57775000000000 : ℝ)*(15541/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (23105575338820489729/23110000000000000000 : ℝ)+2*(57008930553/57775000000000 : ℝ)*(15541/100000 : ℝ)=(10001152377818383/10000000000000000 : ℝ) by norm_num, show 1+2*(6400000958143161/25000000000000000000 : ℝ)=(12506400000958143161/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23105575338820489729/23110000000000000000 : ℝ)*(X 1 0+X 2 0)+(57008930553/57775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (15541/100000 : ℝ)) (c := (23105575338820489729/23110000000000000000 : ℝ)) (alpha := (57008930553/57775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23105575338820489729/23110000000000000000 : ℝ)*(X 0 1+X 2 1)+(57008930553/57775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (15541/100000 : ℝ)) (c := (23105575338820489729/23110000000000000000 : ℝ)) (alpha := (57008930553/57775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23105575338820489729/23110000000000000000 : ℝ)*(X 0 2+X 1 2)+(57008930553/57775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (15541/100000 : ℝ)) (c := (23105575338820489729/23110000000000000000 : ℝ)) (alpha := (57008930553/57775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-461508959/2500000000 : ℝ)*X 0 0+(5431607121/10000000000 : ℝ)*X 0 1+(2609035927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350827319/10000000000 : ℝ)*X 1 0+(-1955373413/10000000000 : ℝ)*X 1 1+(2609035831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675413499/5000000000 : ℝ)*X 2 0+(5218072353/10000000000 : ℝ)*X 2 1+(-1955372923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((106570173/250000000 : ℝ)*X 0 0+(251501893/625000000 : ℝ)*X 0 1+(112834031/250000000 : ℝ)*X 0 2+(106570173/250000000 : ℝ)*X 1 0+(251501893/625000000 : ℝ)*X 1 1+(112834031/250000000 : ℝ)*X 1 2+(106570173/250000000 : ℝ)*X 2 0+(251501893/625000000 : ℝ)*X 2 1+(112834031/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1846064873/10000000000 : ℝ)*X 0 0+(1304794367/2500000000 : ℝ)*X 0 1+(2715246507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294648149/10000000000 : ℝ)*X 1 0+(-871476009/5000000000 : ℝ)*X 1 1+(2715246543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26473241/50000000 : ℝ)*X 2 0+(1357623267/2500000000 : ℝ)*X 2 1+(-1742951973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((426287311/1000000000 : ℝ)*X 0 0+(1127706853/2500000000 : ℝ)*X 0 1+(805316441/2000000000 : ℝ)*X 0 2+(426287311/1000000000 : ℝ)*X 1 0+(1127706853/2500000000 : ℝ)*X 1 1+(805316441/2000000000 : ℝ)*X 1 2+(426287311/1000000000 : ℝ)*X 2 0+(1127706853/2500000000 : ℝ)*X 2 1+(805316441/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32458621379979568348341/2311000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1619544623/100000000000000 : ℝ)*(base19) + (1199009/125000000000 : ℝ)*(base23) + (50751737/25000000000000 : ℝ)*(lower2) + (1246397/6250000000000 : ℝ)*(upper3) + (21785253/12500000000000 : ℝ)*(upper5) + (1681687646566273/50000000000000 : ℝ)*(major0) + (1681687646566273/50000000000000 : ℝ)*(major1) + (3363375293132547/100000000000000 : ℝ)*(major2) + (4683091277499839/100000000000000 : ℝ)*(sp0) + (936624188936841/20000000000000 : ℝ)*(sp1) + (1170780401255407/25000000000000 : ℝ)*(sp2) + (255452201829683/12500000000000 : ℝ)*(sp3) + (31286728989/100000000000000 : ℝ)*(sp4) + (9939223093/100000000000000 : ℝ)*(sp7) + (1021813776930279/50000000000000 : ℝ)*(f.failure) + (1170780641057207/25000000000000 : ℝ)*(f.sum) + (35835529072363/11555000000000000000000000000 : ℝ)*base65 + (2751086722208010017/1155500000000000000000000000000000 : ℝ)*base67 + (18925285381577309763/2311000000000000000000000000000000 : ℝ)*base69 + (4632624133285010017/1155500000000000000000000000000000 : ℝ)*base71 + (39347706287793/11555000000000000000000000000 : ℝ)*base73 + (5567349769760690237/2311000000000000000000000000000000 : ℝ)*base76 + (4084911294095089983/1155500000000000000000000000000000 : ℝ)*base78 + (1459260299074089983/1155500000000000000000000000000000 : ℝ)*base80 + (25107891607297/11555000000000000000000000000 : ℝ)*base81 + (11856139/2500000000000000000000 : ℝ)*base89 + (11856139/2500000000000000000000 : ℝ)*base91 + (13143861/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300805864762431748821314541/57775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572185231/100000000000000 : ℝ)*(base19) + (803538843/100000000000000 : ℝ)*(base23) + (89787453/100000000000000 : ℝ)*(upper3) + (19375517/25000000000000 : ℝ)*(lower4) + (81057487/100000000000000 : ℝ)*(upper5) + (339866385058543/10000000000000 : ℝ)*(major0) + (339866385058543/10000000000000 : ℝ)*(major1) + (339866385058543/10000000000000 : ℝ)*(major2) + (9685710611/100000000000000 : ℝ)*(sp1) + (13398388373/100000000000000 : ℝ)*(sp2) + (1183064554739211/25000000000000 : ℝ)*(sp4) + (2366123980530501/50000000000000 : ℝ)*(sp5) + (1183061004257407/25000000000000 : ℝ)*(sp6) + (1032534654331911/50000000000000 : ℝ)*(sp7) + (1032534654331911/50000000000000 : ℝ)*(f.failure) + (1183064554739211/25000000000000 : ℝ)*(f.sum) + (488059652317/72218750000000000000000000 : ℝ)*base65 + (1266390745194795153/231100000000000000000000000000000 : ℝ)*base68 + (1699078274531795153/231100000000000000000000000000000 : ℝ)*base70 + (1054660153892895153/231100000000000000000000000000000 : ℝ)*base72 + (5942832955403/2311000000000000000000000000 : ℝ)*base74 + (503870957906404847/231100000000000000000000000000000 : ℝ)*base75 + (2347016799014595153/231100000000000000000000000000000 : ℝ)*base78 + (1738615720143895153/231100000000000000000000000000000 : ℝ)*base80 + (433344635797/92440000000000000000000000 : ℝ)*base82 + (1460651/2500000000000000000000 : ℝ)*base89 + (1460651/2500000000000000000000 : ℝ)*base91 + (1460651/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1527_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5483/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1527_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1527_s5_0 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1846079621/10000000000 : ℝ)*x 0 + (2715660783/5000000000 : ℝ)*x 1 + (5218328367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1846079621/10000000000 : ℝ)^4551 ≤ (11303674626547/100000000000000 : ℝ)^3527 := by
    have hnat : (1846079621 : ℕ)^4551*100000000000000^3527 ≤ 11303674626547^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846079621 10000000000 11303674626547 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715660783/5000000000 : ℝ)^4551 ≤ (45492539113271/100000000000000 : ℝ)^3527 := by
    have hnat : (2715660783 : ℕ)^4551*100000000000000^3527 ≤ 45492539113271^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715660783 5000000000 45492539113271 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218328367/10000000000 : ℝ)^4551 ≤ (2160189312151/5000000000000 : ℝ)^3527 := by
    have hnat : (5218328367 : ℕ)^4551*5000000000000^3527 ≤ 2160189312151^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218328367 10000000000 2160189312151 5000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1846079621/10000000000 : ℝ), (2715660783/5000000000 : ℝ), (5218328367/10000000000 : ℝ)] ![(11303674626547/100000000000000 : ℝ), (45492539113271/100000000000000 : ℝ), (2160189312151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1846079621/10000000000 : ℝ)|^4551 ≤ (11303674626547/100000000000000 : ℝ)^3527
        have hw : |(-1846079621/10000000000 : ℝ)|=(1846079621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715660783/5000000000 : ℝ)|^4551 ≤ (45492539113271/100000000000000 : ℝ)^3527
        have hw : |(2715660783/5000000000 : ℝ)|=(2715660783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218328367/10000000000 : ℝ)|^4551 ≤ (2160189312151/5000000000000 : ℝ)^3527
        have hw : |(5218328367/10000000000 : ℝ)|=(5218328367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_1 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337688027/2500000000 : ℝ)*x 0 + (-97756587/500000000 : ℝ)*x 1 + (1043665833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337688027/2500000000 : ℝ)^4551 ≤ (44623644828673/100000000000000 : ℝ)^3527 := by
    have hnat : (1337688027 : ℕ)^4551*100000000000000^3527 ≤ 44623644828673^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337688027 2500000000 44623644828673 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97756587/500000000 : ℝ)^4551 ≤ (12172560393993/100000000000000 : ℝ)^3527 := by
    have hnat : (97756587 : ℕ)^4551*100000000000000^3527 ≤ 12172560393993^3527*500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97756587 500000000 12172560393993 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043665833/2000000000 : ℝ)^4551 ≤ (21601897384013/50000000000000 : ℝ)^3527 := by
    have hnat : (1043665833 : ℕ)^4551*50000000000000^3527 ≤ 21601897384013^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043665833 2000000000 21601897384013 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337688027/2500000000 : ℝ), (-97756587/500000000 : ℝ), (1043665833/2000000000 : ℝ)] ![(44623644828673/100000000000000 : ℝ), (12172560393993/100000000000000 : ℝ), (21601897384013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337688027/2500000000 : ℝ)|^4551 ≤ (44623644828673/100000000000000 : ℝ)^3527
        have hw : |(1337688027/2500000000 : ℝ)|=(1337688027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97756587/500000000 : ℝ)|^4551 ≤ (12172560393993/100000000000000 : ℝ)^3527
        have hw : |(-97756587/500000000 : ℝ)|=(97756587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043665833/2000000000 : ℝ)|^4551 ≤ (21601897384013/50000000000000 : ℝ)^3527
        have hw : |(1043665833/2000000000 : ℝ)|=(1043665833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_2 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675376243/5000000000 : ℝ)*x 0 + (2609164337/5000000000 : ℝ)*x 1 + (-391026377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675376243/5000000000 : ℝ)^4551 ≤ (44623648896321/100000000000000 : ℝ)^3527 := by
    have hnat : (2675376243 : ℕ)^4551*100000000000000^3527 ≤ 44623648896321^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675376243 5000000000 44623648896321 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609164337/5000000000 : ℝ)^4551 ≤ (4320378952269/10000000000000 : ℝ)^3527 := by
    have hnat : (2609164337 : ℕ)^4551*10000000000000^3527 ≤ 4320378952269^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609164337 5000000000 4320378952269 10000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391026377/2000000000 : ℝ)^4551 ≤ (12172561558857/100000000000000 : ℝ)^3527 := by
    have hnat : (391026377 : ℕ)^4551*100000000000000^3527 ≤ 12172561558857^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391026377 2000000000 12172561558857 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675376243/5000000000 : ℝ), (2609164337/5000000000 : ℝ), (-391026377/2000000000 : ℝ)] ![(44623648896321/100000000000000 : ℝ), (4320378952269/10000000000000 : ℝ), (12172561558857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675376243/5000000000 : ℝ)|^4551 ≤ (44623648896321/100000000000000 : ℝ)^3527
        have hw : |(2675376243/5000000000 : ℝ)|=(2675376243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609164337/5000000000 : ℝ)|^4551 ≤ (4320378952269/10000000000000 : ℝ)^3527
        have hw : |(2609164337/5000000000 : ℝ)|=(2609164337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391026377/2000000000 : ℝ)|^4551 ≤ (12172561558857/100000000000000 : ℝ)^3527
        have hw : |(-391026377/2000000000 : ℝ)|=(391026377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_3 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4262834081/10000000000 : ℝ)*x 0 + (4024648911/10000000000 : ℝ)*x 1 + (90254723/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262834081/10000000000 : ℝ)^4551 ≤ (33280369146187/100000000000000 : ℝ)^3527 := by
    have hnat : (4262834081 : ℕ)^4551*100000000000000^3527 ≤ 33280369146187^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262834081 10000000000 33280369146187 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024648911/10000000000 : ℝ)^4551 ≤ (30900677308341/100000000000000 : ℝ)^3527 := by
    have hnat : (4024648911 : ℕ)^4551*100000000000000^3527 ≤ 30900677308341^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024648911 10000000000 30900677308341 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90254723/200000000 : ℝ)^4551 ≤ (4477369192617/12500000000000 : ℝ)^3527 := by
    have hnat : (90254723 : ℕ)^4551*12500000000000^3527 ≤ 4477369192617^3527*200000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90254723 200000000 4477369192617 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262834081/10000000000 : ℝ), (4024648911/10000000000 : ℝ), (90254723/200000000 : ℝ)] ![(33280369146187/100000000000000 : ℝ), (30900677308341/100000000000000 : ℝ), (4477369192617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262834081/10000000000 : ℝ)|^4551 ≤ (33280369146187/100000000000000 : ℝ)^3527
        have hw : |(4262834081/10000000000 : ℝ)|=(4262834081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024648911/10000000000 : ℝ)|^4551 ≤ (30900677308341/100000000000000 : ℝ)^3527
        have hw : |(4024648911/10000000000 : ℝ)|=(4024648911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90254723/200000000 : ℝ)|^4551 ≤ (4477369192617/12500000000000 : ℝ)^3527
        have hw : |(90254723/200000000 : ℝ)|=(90254723/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_4 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1846108003/10000000000 : ℝ)*x 0 + (2609714411/5000000000 : ℝ)*x 1 + (1086042601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1846108003/10000000000 : ℝ)^4551 ≤ (11303898867309/100000000000000 : ℝ)^3527 := by
    have hnat : (1846108003 : ℕ)^4551*100000000000000^3527 ≤ 11303898867309^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846108003 10000000000 11303898867309 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609714411/5000000000 : ℝ)^4551 ≤ (21607771362233/50000000000000 : ℝ)^3527 := by
    have hnat : (2609714411 : ℕ)^4551*50000000000000^3527 ≤ 21607771362233^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609714411 5000000000 21607771362233 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086042601/2000000000 : ℝ)^4551 ≤ (45480558397537/100000000000000 : ℝ)^3527 := by
    have hnat : (1086042601 : ℕ)^4551*100000000000000^3527 ≤ 45480558397537^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086042601 2000000000 45480558397537 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1846108003/10000000000 : ℝ), (2609714411/5000000000 : ℝ), (1086042601/2000000000 : ℝ)] ![(11303898867309/100000000000000 : ℝ), (21607771362233/50000000000000 : ℝ), (45480558397537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1846108003/10000000000 : ℝ)|^4551 ≤ (11303898867309/100000000000000 : ℝ)^3527
        have hw : |(-1846108003/10000000000 : ℝ)|=(1846108003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609714411/5000000000 : ℝ)|^4551 ≤ (21607771362233/50000000000000 : ℝ)^3527
        have hw : |(2609714411/5000000000 : ℝ)|=(2609714411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086042601/2000000000 : ℝ)|^4551 ≤ (45480558397537/100000000000000 : ℝ)^3527
        have hw : |(1086042601/2000000000 : ℝ)|=(1086042601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_5 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330919757/625000000 : ℝ)*x 0 + (-1743247927/10000000000 : ℝ)*x 1 + (1357553217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330919757/625000000 : ℝ)^4551 ≤ (11005390481847/25000000000000 : ℝ)^3527 := by
    have hnat : (330919757 : ℕ)^4551*25000000000000^3527 ≤ 11005390481847^3527*625000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330919757 625000000 11005390481847 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1743247927/10000000000 : ℝ)^4551 ≤ (164029392973/1562500000000 : ℝ)^3527 := by
    have hnat : (1743247927 : ℕ)^4551*1562500000000^3527 ≤ 164029392973^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743247927 10000000000 164029392973 1562500000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357553217/2500000000 : ℝ)^4551 ≤ (284253480731/625000000000 : ℝ)^3527 := by
    have hnat : (1357553217 : ℕ)^4551*625000000000^3527 ≤ 284253480731^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357553217 2500000000 284253480731 625000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330919757/625000000 : ℝ), (-1743247927/10000000000 : ℝ), (1357553217/2500000000 : ℝ)] ![(11005390481847/25000000000000 : ℝ), (164029392973/1562500000000 : ℝ), (284253480731/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330919757/625000000 : ℝ)|^4551 ≤ (11005390481847/25000000000000 : ℝ)^3527
        have hw : |(330919757/625000000 : ℝ)|=(330919757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1743247927/10000000000 : ℝ)|^4551 ≤ (164029392973/1562500000000 : ℝ)^3527
        have hw : |(-1743247927/10000000000 : ℝ)|=(1743247927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357553217/2500000000 : ℝ)|^4551 ≤ (284253480731/625000000000 : ℝ)^3527
        have hw : |(1357553217/2500000000 : ℝ)|=(1357553217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_6 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647358007/5000000000 : ℝ)*x 0 + (678776603/1250000000 : ℝ)*x 1 + (-1743248123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647358007/5000000000 : ℝ)^4551 ≤ (44021560876031/100000000000000 : ℝ)^3527 := by
    have hnat : (2647358007 : ℕ)^4551*100000000000000^3527 ≤ 44021560876031^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647358007 5000000000 44021560876031 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678776603/1250000000 : ℝ)^4551 ≤ (45480556441447/100000000000000 : ℝ)^3527 := by
    have hnat : (678776603 : ℕ)^4551*100000000000000^3527 ≤ 45480556441447^3527*1250000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678776603 1250000000 45480556441447 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1743248123/10000000000 : ℝ)^4551 ≤ (10497882673273/100000000000000 : ℝ)^3527 := by
    have hnat : (1743248123 : ℕ)^4551*100000000000000^3527 ≤ 10497882673273^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743248123 10000000000 10497882673273 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647358007/5000000000 : ℝ), (678776603/1250000000 : ℝ), (-1743248123/10000000000 : ℝ)] ![(44021560876031/100000000000000 : ℝ), (45480556441447/100000000000000 : ℝ), (10497882673273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647358007/5000000000 : ℝ)|^4551 ≤ (44021560876031/100000000000000 : ℝ)^3527
        have hw : |(2647358007/5000000000 : ℝ)|=(2647358007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678776603/1250000000 : ℝ)|^4551 ≤ (45480556441447/100000000000000 : ℝ)^3527
        have hw : |(678776603/1250000000 : ℝ)|=(678776603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1743248123/10000000000 : ℝ)|^4551 ≤ (10497882673273/100000000000000 : ℝ)^3527
        have hw : |(-1743248123/10000000000 : ℝ)|=(1743248123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s5_7 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266431217/625000000 : ℝ)*x 0 + (4510215377/10000000000 : ℝ)*x 1 + (4027187927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266431217/625000000 : ℝ)^4551 ≤ (8320256970027/25000000000000 : ℝ)^3527 := by
    have hnat : (266431217 : ℕ)^4551*25000000000000^3527 ≤ 8320256970027^3527*625000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266431217 625000000 8320256970027 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510215377/10000000000 : ℝ)^4551 ≤ (8948284624619/25000000000000 : ℝ)^3527 := by
    have hnat : (4510215377 : ℕ)^4551*25000000000000^3527 ≤ 8948284624619^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510215377 10000000000 8948284624619 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027187927/10000000000 : ℝ)^4551 ≤ (30925833597409/100000000000000 : ℝ)^3527 := by
    have hnat : (4027187927 : ℕ)^4551*100000000000000^3527 ≤ 30925833597409^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027187927 10000000000 30925833597409 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266431217/625000000 : ℝ), (4510215377/10000000000 : ℝ), (4027187927/10000000000 : ℝ)] ![(8320256970027/25000000000000 : ℝ), (8948284624619/25000000000000 : ℝ), (30925833597409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266431217/625000000 : ℝ)|^4551 ≤ (8320256970027/25000000000000 : ℝ)^3527
        have hw : |(266431217/625000000 : ℝ)|=(266431217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510215377/10000000000 : ℝ)|^4551 ≤ (8948284624619/25000000000000 : ℝ)^3527
        have hw : |(4510215377/10000000000 : ℝ)|=(4510215377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027187927/10000000000 : ℝ)|^4551 ≤ (30925833597409/100000000000000 : ℝ)^3527
        have hw : |(4027187927/10000000000 : ℝ)|=(4027187927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1527_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5483/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2743/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5483/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5483/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5483/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5483/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5483/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5483/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5483/50000 : ℝ) ^ (4549/1024 : ℝ) ≤ (543909704255161/10000000000000000000 : ℝ) := by
    have hpowers : (5483/50000 : ℝ)^4549 ≤ (543909704255161/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5483 : ℕ)^4549*10000000000000000000^1024 ≤ 543909704255161^1024*50000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5483 50000 543909704255161 10000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5483/50000 : ℝ)) (X := (543909704255161/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4549/1024 : ℝ) ≤ (25228901388240017/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4549 ≤ (25228901388240017/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4549*100000000000000000000^1024 ≤ 25228901388240017^1024*10000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 25228901388240017 100000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (25228901388240017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000543909704255161/5000000000000000000 : ℝ) ≤ (10000244862635369/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (5000543909704255161/5000000000000000000 : ℝ)^1024 ≤ (10000244862635369/10000000000000000 : ℝ)^4549 := by
      have hnat : (5000543909704255161 : ℕ)^1024*10000000000000000^4549 ≤ 10000244862635369^4549*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000543909704255161 5000000000000000000 10000244862635369 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000244862635369/10000000000000000 : ℝ)) (X := (5000543909704255161/5000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030667998430791627/100000000000000000000 : ℝ) ≤ (10000690268181253/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (100030667998430791627/100000000000000000000 : ℝ)^1024 ≤ (10000690268181253/10000000000000000 : ℝ)^4549 := by
      have hnat : (100030667998430791627 : ℕ)^1024*10000000000000000^4549 ≤ 10000690268181253^4549*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030667998430791627 100000000000000000000 10000690268181253 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690268181253/10000000000000000 : ℝ)) (X := (100030667998430791627/100000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025228901388240017/50000000000000000000 : ℝ) ≤ (10001135673727137/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (50025228901388240017/50000000000000000000 : ℝ)^1024 ≤ (10001135673727137/10000000000000000 : ℝ)^4549 := by
      have hnat : (50025228901388240017 : ℕ)^1024*10000000000000000^4549 ≤ 10001135673727137^4549*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025228901388240017 50000000000000000000 10001135673727137 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001135673727137/10000000000000000 : ℝ)) (X := (50025228901388240017/50000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(543909704255161/10000000000000000000 : ℝ) ≤ ((869833444694809259/870000000000000000 : ℝ)+2*(8565491267/8700000000000 : ℝ)*(5483/50000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (869833444694809259/870000000000000000 : ℝ)+2*(8565491267/8700000000000 : ℝ)*(5483/50000 : ℝ)=(10000244862635369/10000000000000000 : ℝ) by norm_num, show 1+2*(543909704255161/10000000000000000000 : ℝ)=(5000543909704255161/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25228901388240017/100000000000000000000 : ℝ)+(543909704255161/10000000000000000000 : ℝ) ≤ ((869833444694809259/870000000000000000 : ℝ)+(8565491267/8700000000000 : ℝ)*((1549/10000 : ℝ)+(5483/50000 : ℝ)))^(4549/1024 : ℝ) := by
    rw [show (869833444694809259/870000000000000000 : ℝ)+(8565491267/8700000000000 : ℝ)*((1549/10000 : ℝ)+(5483/50000 : ℝ))=(10000690268181253/10000000000000000 : ℝ) by norm_num, show 1+(25228901388240017/100000000000000000000 : ℝ)+(543909704255161/10000000000000000000 : ℝ)=(100030667998430791627/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25228901388240017/100000000000000000000 : ℝ) ≤ ((869833444694809259/870000000000000000 : ℝ)+2*(8565491267/8700000000000 : ℝ)*(1549/10000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (869833444694809259/870000000000000000 : ℝ)+2*(8565491267/8700000000000 : ℝ)*(1549/10000 : ℝ)=(10001135673727137/10000000000000000 : ℝ) by norm_num, show 1+2*(25228901388240017/100000000000000000000 : ℝ)=(50025228901388240017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (869833444694809259/870000000000000000 : ℝ)*(X 1 0+X 2 0)+(8565491267/8700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (5483/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (869833444694809259/870000000000000000 : ℝ)) (alpha := (8565491267/8700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (869833444694809259/870000000000000000 : ℝ)*(X 0 1+X 2 1)+(8565491267/8700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (5483/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (869833444694809259/870000000000000000 : ℝ)) (alpha := (8565491267/8700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (869833444694809259/870000000000000000 : ℝ)*(X 0 2+X 1 2)+(8565491267/8700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (5483/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (869833444694809259/870000000000000000 : ℝ)) (alpha := (8565491267/8700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1846079621/10000000000 : ℝ)*X 0 0+(2715660783/5000000000 : ℝ)*X 0 1+(5218328367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337688027/2500000000 : ℝ)*X 1 0+(-97756587/500000000 : ℝ)*X 1 1+(1043665833/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675376243/5000000000 : ℝ)*X 2 0+(2609164337/5000000000 : ℝ)*X 2 1+(-391026377/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4262834081/10000000000 : ℝ)*X 0 0+(4024648911/10000000000 : ℝ)*X 0 1+(90254723/200000000 : ℝ)*X 0 2+(4262834081/10000000000 : ℝ)*X 1 0+(4024648911/10000000000 : ℝ)*X 1 1+(90254723/200000000 : ℝ)*X 1 2+(4262834081/10000000000 : ℝ)*X 2 0+(4024648911/10000000000 : ℝ)*X 2 1+(90254723/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1846108003/10000000000 : ℝ)*X 0 0+(2609714411/5000000000 : ℝ)*X 0 1+(1086042601/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330919757/625000000 : ℝ)*X 1 0+(-1743247927/10000000000 : ℝ)*X 1 1+(1357553217/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647358007/5000000000 : ℝ)*X 2 0+(678776603/1250000000 : ℝ)*X 2 1+(-1743248123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266431217/625000000 : ℝ)*X 0 0+(4510215377/10000000000 : ℝ)*X 0 1+(4027187927/10000000000 : ℝ)*X 0 2+(266431217/625000000 : ℝ)*X 1 0+(4510215377/10000000000 : ℝ)*X 1 1+(4027187927/10000000000 : ℝ)*X 1 2+(266431217/625000000 : ℝ)*X 2 0+(4510215377/10000000000 : ℝ)*X 2 1+(4027187927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1104311282309542718532677/181250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (534264903/50000000000000 : ℝ)*(base19) + (346854001/25000000000000 : ℝ)*(base23) + (855627/12500000000000 : ℝ)*(lower2) + (16438131/12500000000000 : ℝ)*(upper3) + (33259163/100000000000000 : ℝ)*(upper5) + (84298663843603/2500000000000 : ℝ)*(major0) + (84298663843603/2500000000000 : ℝ)*(major1) + (84298663843603/2500000000000 : ℝ)*(major2) + (2347510879427587/50000000000000 : ℝ)*(sp0) + (586882035034077/12500000000000 : ℝ)*(sp1) + (2347527980693209/50000000000000 : ℝ)*(sp2) + (2048823801436369/100000000000000 : ℝ)*(sp3) + (2224371703/6250000000000 : ℝ)*(sp4) + (2350831543/20000000000000 : ℝ)*(sp7) + (512208888898521/25000000000000 : ℝ)*(f.failure) + (2347528674401211/50000000000000 : ℝ)*(f.sum) + (31731350669/87000000000000000000000000 : ℝ)*base66 + (393280959483787/75000000000000000000000000000 : ℝ)*base68 + (282231099408787/75000000000000000000000000000 : ℝ)*base70 + (467673522708787/75000000000000000000000000000 : ℝ)*base72 + (16236292103/8700000000000000000000000 : ℝ)*base74 + (652818440058787/75000000000000000000000000000 : ℝ)*base76 + (260933069208787/75000000000000000000000000000 : ℝ)*base78 + (45027636116213/75000000000000000000000000000 : ℝ)*base79 + (154159404433/87000000000000000000000000 : ℝ)*base81 + (8964661/1250000000000000000000 : ℝ)*base89 + (8964661/1250000000000000000000 : ℝ)*base91 + (8964661/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15319501634040177362278623/3625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81211277/10000000000000 : ℝ)*(base19) + (410908581/50000000000000 : ℝ)*(base23) + (16974903/10000000000000 : ℝ)*(lower1) + (75069107/100000000000000 : ℝ)*(upper3) + (67844187/100000000000000 : ℝ)*(lower4) + (83868167/100000000000000 : ℝ)*(upper5) + (851806345539597/25000000000000 : ℝ)*(major0) + (851806345539597/25000000000000 : ℝ)*(major1) + (851806345539597/25000000000000 : ℝ)*(major2) + (289332567/10000000000000 : ℝ)*(sp1) + (4744179224532111/100000000000000 : ℝ)*(sp4) + (4744175519093671/100000000000000 : ℝ)*(sp5) + (4744178402714949/100000000000000 : ℝ)*(sp6) + (12939196243223/625000000000 : ℝ)*(sp7) + (12939196243223/625000000000 : ℝ)*(f.failure) + (4744179224532111/100000000000000 : ℝ)*(f.sum) + (295119121617/145000000000000000000000000 : ℝ)*base65 + (2531586658699671/250000000000000000000000000000 : ℝ)*base68 + (637382736949671/250000000000000000000000000000 : ℝ)*base70 + (626126873800329/250000000000000000000000000000 : ℝ)*base71 + (1010191021203/145000000000000000000000000 : ℝ)*base74 + (1980737842699671/250000000000000000000000000000 : ℝ)*base76 + (580238430300329/250000000000000000000000000000 : ℝ)*base77 + (746187342199671/250000000000000000000000000000 : ℝ)*base80 + (406937239253/145000000000000000000000000 : ℝ)*base82 + (136043/31250000000000000000 : ℝ)*base89 + (136043/31250000000000000000 : ℝ)*base91 + (136043/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1527_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5483/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1527_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1527_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1527_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1527_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1527_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1527_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
