-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1136_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:16.794669+00:00
-- url     : https://prove2.me/submissions/53202ae0-8d20-40d1-8c60-3fb382cc2964

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
theorem support_rectangle_w1136_s3_0 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165891683/10000000000 : ℝ)*x 0 + (217191849/400000000 : ℝ)*x 1 + (5231519173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165891683/10000000000 : ℝ)^8329 ≤ (52610523753/400000000000 : ℝ)^6281 := by
    have hnat : (2165891683 : ℕ)^8329*400000000000^6281 ≤ 52610523753^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165891683 10000000000 52610523753 400000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217191849/400000000 : ℝ)^8329 ≤ (22247249737853/50000000000000 : ℝ)^6281 := by
    have hnat : (217191849 : ℕ)^8329*50000000000000^6281 ≤ 22247249737853^6281*400000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217191849 400000000 22247249737853 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231519173/10000000000 : ℝ)^8329 ≤ (21176434790141/50000000000000 : ℝ)^6281 := by
    have hnat : (5231519173 : ℕ)^8329*50000000000000^6281 ≤ 21176434790141^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231519173 10000000000 21176434790141 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165891683/10000000000 : ℝ), (217191849/400000000 : ℝ), (5231519173/10000000000 : ℝ)] ![(52610523753/400000000000 : ℝ), (22247249737853/50000000000000 : ℝ), (21176434790141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165891683/10000000000 : ℝ)|^8329 ≤ (52610523753/400000000000 : ℝ)^6281
        have hw : |(-2165891683/10000000000 : ℝ)|=(2165891683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217191849/400000000 : ℝ)|^8329 ≤ (22247249737853/50000000000000 : ℝ)^6281
        have hw : |(217191849/400000000 : ℝ)|=(217191849/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231519173/10000000000 : ℝ)|^8329 ≤ (21176434790141/50000000000000 : ℝ)^6281
        have hw : |(5231519173/10000000000 : ℝ)|=(5231519173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_1 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167310553/312500000 : ℝ)*x 0 + (-2267257491/10000000000 : ℝ)*x 1 + (5231519031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167310553/312500000 : ℝ)^8329 ≤ (2729504472937/6250000000000 : ℝ)^6281 := by
    have hnat : (167310553 : ℕ)^8329*6250000000000^6281 ≤ 2729504472937^6281*312500000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167310553 312500000 2729504472937 6250000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267257491/10000000000 : ℝ)^8329 ≤ (1746882545277/12500000000000 : ℝ)^6281 := by
    have hnat : (2267257491 : ℕ)^8329*12500000000000^6281 ≤ 1746882545277^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267257491 10000000000 1746882545277 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231519031/10000000000 : ℝ)^8329 ≤ (10588217013963/25000000000000 : ℝ)^6281 := by
    have hnat : (5231519031 : ℕ)^8329*25000000000000^6281 ≤ 10588217013963^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231519031 10000000000 10588217013963 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167310553/312500000 : ℝ), (-2267257491/10000000000 : ℝ), (5231519031/10000000000 : ℝ)] ![(2729504472937/6250000000000 : ℝ), (1746882545277/12500000000000 : ℝ), (10588217013963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167310553/312500000 : ℝ)|^8329 ≤ (2729504472937/6250000000000 : ℝ)^6281
        have hw : |(167310553/312500000 : ℝ)|=(167310553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2267257491/10000000000 : ℝ)|^8329 ≤ (1746882545277/12500000000000 : ℝ)^6281
        have hw : |(-2267257491/10000000000 : ℝ)|=(2267257491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231519031/10000000000 : ℝ)|^8329 ≤ (10588217013963/25000000000000 : ℝ)^6281
        have hw : |(5231519031/10000000000 : ℝ)|=(5231519031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_2 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676968891/5000000000 : ℝ)*x 0 + (5231519121/10000000000 : ℝ)*x 1 + (-2267257259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676968891/5000000000 : ℝ)^8329 ≤ (10918018124307/25000000000000 : ℝ)^6281 := by
    have hnat : (2676968891 : ℕ)^8329*25000000000000^6281 ≤ 10918018124307^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676968891 5000000000 10918018124307 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231519121/10000000000 : ℝ)^8329 ≤ (1058821725551/2500000000000 : ℝ)^6281 := by
    have hnat : (5231519121 : ℕ)^8329*2500000000000^6281 ≤ 1058821725551^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231519121 10000000000 1058821725551 2500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267257259/10000000000 : ℝ)^8329 ≤ (559002338637/4000000000000 : ℝ)^6281 := by
    have hnat : (2267257259 : ℕ)^8329*4000000000000^6281 ≤ 559002338637^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267257259 10000000000 559002338637 4000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676968891/5000000000 : ℝ), (5231519121/10000000000 : ℝ), (-2267257259/10000000000 : ℝ)] ![(10918018124307/25000000000000 : ℝ), (1058821725551/2500000000000 : ℝ), (559002338637/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676968891/5000000000 : ℝ)|^8329 ≤ (10918018124307/25000000000000 : ℝ)^6281
        have hw : |(2676968891/5000000000 : ℝ)|=(2676968891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231519121/10000000000 : ℝ)|^8329 ≤ (1058821725551/2500000000000 : ℝ)^6281
        have hw : |(5231519121/10000000000 : ℝ)|=(5231519121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2267257259/10000000000 : ℝ)|^8329 ≤ (559002338637/4000000000000 : ℝ)^6281
        have hw : |(-2267257259/10000000000 : ℝ)|=(2267257259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_3 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363223011/10000000000 : ℝ)*x 0 + (4170647277/10000000000 : ℝ)*x 1 + (4564649833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363223011/10000000000 : ℝ)^8329 ≤ (8323424436801/25000000000000 : ℝ)^6281 := by
    have hnat : (4363223011 : ℕ)^8329*25000000000000^6281 ≤ 8323424436801^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363223011 10000000000 8323424436801 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170647277/10000000000 : ℝ)^8329 ≤ (7839817896319/25000000000000 : ℝ)^6281 := by
    have hnat : (4170647277 : ℕ)^8329*25000000000000^6281 ≤ 7839817896319^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170647277 10000000000 7839817896319 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564649833/10000000000 : ℝ)^8329 ≤ (35347030654699/100000000000000 : ℝ)^6281 := by
    have hnat : (4564649833 : ℕ)^8329*100000000000000^6281 ≤ 35347030654699^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564649833 10000000000 35347030654699 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363223011/10000000000 : ℝ), (4170647277/10000000000 : ℝ), (4564649833/10000000000 : ℝ)] ![(8323424436801/25000000000000 : ℝ), (7839817896319/25000000000000 : ℝ), (35347030654699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363223011/10000000000 : ℝ)|^8329 ≤ (8323424436801/25000000000000 : ℝ)^6281
        have hw : |(4363223011/10000000000 : ℝ)|=(4363223011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170647277/10000000000 : ℝ)|^8329 ≤ (7839817896319/25000000000000 : ℝ)^6281
        have hw : |(4170647277/10000000000 : ℝ)|=(4170647277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564649833/10000000000 : ℝ)|^8329 ≤ (35347030654699/100000000000000 : ℝ)^6281
        have hw : |(4564649833/10000000000 : ℝ)|=(4564649833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_4 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43318201/200000000 : ℝ)*x 0 + (5232291881/10000000000 : ℝ)*x 1 + (339313699/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43318201/200000000 : ℝ)^8329 ≤ (13152778841867/100000000000000 : ℝ)^6281 := by
    have hnat : (43318201 : ℕ)^8329*100000000000000^6281 ≤ 13152778841867^6281*200000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43318201 200000000 13152778841867 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232291881/10000000000 : ℝ)^8329 ≤ (42361165125869/100000000000000 : ℝ)^6281 := by
    have hnat : (5232291881 : ℕ)^8329*100000000000000^6281 ≤ 42361165125869^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232291881 10000000000 42361165125869 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339313699/625000000 : ℝ)^8329 ≤ (8897211202307/20000000000000 : ℝ)^6281 := by
    have hnat : (339313699 : ℕ)^8329*20000000000000^6281 ≤ 8897211202307^6281*625000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339313699 625000000 8897211202307 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43318201/200000000 : ℝ), (5232291881/10000000000 : ℝ), (339313699/625000000 : ℝ)] ![(13152778841867/100000000000000 : ℝ), (42361165125869/100000000000000 : ℝ), (8897211202307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43318201/200000000 : ℝ)|^8329 ≤ (13152778841867/100000000000000 : ℝ)^6281
        have hw : |(-43318201/200000000 : ℝ)|=(43318201/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232291881/10000000000 : ℝ)|^8329 ≤ (42361165125869/100000000000000 : ℝ)^6281
        have hw : |(5232291881/10000000000 : ℝ)|=(5232291881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339313699/625000000 : ℝ)|^8329 ≤ (8897211202307/20000000000000 : ℝ)^6281
        have hw : |(339313699/625000000 : ℝ)|=(339313699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_5 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303727147/10000000000 : ℝ)*x 0 + (-2069757229/10000000000 : ℝ)*x 1 + (2714509677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303727147/10000000000 : ℝ)^8329 ≤ (2695611972727/6250000000000 : ℝ)^6281 := by
    have hnat : (5303727147 : ℕ)^8329*6250000000000^6281 ≤ 2695611972727^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303727147 10000000000 2695611972727 6250000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069757229/10000000000 : ℝ)^8329 ≤ (6192075283879/50000000000000 : ℝ)^6281 := by
    have hnat : (2069757229 : ℕ)^8329*50000000000000^6281 ≤ 6192075283879^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069757229 10000000000 6192075283879 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714509677/5000000000 : ℝ)^8329 ≤ (22243028929371/50000000000000 : ℝ)^6281 := by
    have hnat : (2714509677 : ℕ)^8329*50000000000000^6281 ≤ 22243028929371^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714509677 5000000000 22243028929371 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303727147/10000000000 : ℝ), (-2069757229/10000000000 : ℝ), (2714509677/5000000000 : ℝ)] ![(2695611972727/6250000000000 : ℝ), (6192075283879/50000000000000 : ℝ), (22243028929371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303727147/10000000000 : ℝ)|^8329 ≤ (2695611972727/6250000000000 : ℝ)^6281
        have hw : |(5303727147/10000000000 : ℝ)|=(5303727147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069757229/10000000000 : ℝ)|^8329 ≤ (6192075283879/50000000000000 : ℝ)^6281
        have hw : |(-2069757229/10000000000 : ℝ)|=(2069757229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714509677/5000000000 : ℝ)|^8329 ≤ (22243028929371/50000000000000 : ℝ)^6281
        have hw : |(2714509677/5000000000 : ℝ)|=(2714509677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_6 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325931761/2500000000 : ℝ)*x 0 + (1357254879/2500000000 : ℝ)*x 1 + (-1034878573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325931761/2500000000 : ℝ)^8329 ≤ (4312979045293/10000000000000 : ℝ)^6281 := by
    have hnat : (1325931761 : ℕ)^8329*10000000000000^6281 ≤ 4312979045293^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325931761 2500000000 4312979045293 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357254879/2500000000 : ℝ)^8329 ≤ (44486059619021/100000000000000 : ℝ)^6281 := by
    have hnat : (1357254879 : ℕ)^8329*100000000000000^6281 ≤ 44486059619021^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357254879 2500000000 44486059619021 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034878573/5000000000 : ℝ)^8329 ≤ (12384149909207/100000000000000 : ℝ)^6281 := by
    have hnat : (1034878573 : ℕ)^8329*100000000000000^6281 ≤ 12384149909207^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034878573 5000000000 12384149909207 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325931761/2500000000 : ℝ), (1357254879/2500000000 : ℝ), (-1034878573/5000000000 : ℝ)] ![(4312979045293/10000000000000 : ℝ), (44486059619021/100000000000000 : ℝ), (12384149909207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325931761/2500000000 : ℝ)|^8329 ≤ (4312979045293/10000000000000 : ℝ)^6281
        have hw : |(1325931761/2500000000 : ℝ)|=(1325931761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357254879/2500000000 : ℝ)|^8329 ≤ (44486059619021/100000000000000 : ℝ)^6281
        have hw : |(1357254879/2500000000 : ℝ)|=(1357254879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034878573/5000000000 : ℝ)|^8329 ≤ (12384149909207/100000000000000 : ℝ)^6281
        have hw : |(-1034878573/5000000000 : ℝ)|=(1034878573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s3_7 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363259501/10000000000 : ℝ)*x 0 + (4563114751/10000000000 : ℝ)*x 1 + (4172191003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363259501/10000000000 : ℝ)^8329 ≤ (4161758371743/12500000000000 : ℝ)^6281 := by
    have hnat : (4363259501 : ℕ)^8329*12500000000000^6281 ≤ 4161758371743^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363259501 10000000000 4161758371743 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4563114751/10000000000 : ℝ)^8329 ≤ (35331268437643/100000000000000 : ℝ)^6281 := by
    have hnat : (4563114751 : ℕ)^8329*100000000000000^6281 ≤ 35331268437643^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563114751 10000000000 35331268437643 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172191003/10000000000 : ℝ)^8329 ≤ (31374664575593/100000000000000 : ℝ)^6281 := by
    have hnat : (4172191003 : ℕ)^8329*100000000000000^6281 ≤ 31374664575593^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172191003 10000000000 31374664575593 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363259501/10000000000 : ℝ), (4563114751/10000000000 : ℝ), (4172191003/10000000000 : ℝ)] ![(4161758371743/12500000000000 : ℝ), (35331268437643/100000000000000 : ℝ), (31374664575593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363259501/10000000000 : ℝ)|^8329 ≤ (4161758371743/12500000000000 : ℝ)^6281
        have hw : |(4363259501/10000000000 : ℝ)|=(4363259501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4563114751/10000000000 : ℝ)|^8329 ≤ (35331268437643/100000000000000 : ℝ)^6281
        have hw : |(4563114751/10000000000 : ℝ)|=(4563114751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172191003/10000000000 : ℝ)|^8329 ≤ (31374664575593/100000000000000 : ℝ)^6281
        have hw : |(4172191003/10000000000 : ℝ)|=(4172191003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1136_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10617/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14813/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (413/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (413/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (413/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (413/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (413/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (413/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9043/100000 : ℝ) ^ (1041/256 : ℝ) ≤ (5700891195773107/100000000000000000000 : ℝ) := by
    have hpowers : (9043/100000 : ℝ)^1041 ≤ (5700891195773107/100000000000000000000 : ℝ)^256 := by
      have hnat : (9043 : ℕ)^1041*100000000000000000000^256 ≤ 5700891195773107^256*100000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9043 100000 5700891195773107 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9043/100000 : ℝ)) (X := (5700891195773107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hpowhi : (413/2500 : ℝ) ^ (1041/256 : ℝ) ≤ (1032597757069001/1562500000000000000 : ℝ) := by
    have hpowers : (413/2500 : ℝ)^1041 ≤ (1032597757069001/1562500000000000000 : ℝ)^256 := by
      have hnat : (413 : ℕ)^1041*1562500000000000000^256 ≤ 1032597757069001^256*2500^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 2500 1032597757069001 1562500000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/2500 : ℝ)) (X := (1032597757069001/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005700891195773107/50000000000000000000 : ℝ) ≤ (5000140188800223/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50005700891195773107/50000000000000000000 : ℝ)^256 ≤ (5000140188800223/5000000000000000 : ℝ)^1041 := by
      have hnat : (50005700891195773107 : ℕ)^256*5000000000000000^1041 ≤ 5000140188800223^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005700891195773107 50000000000000000000 5000140188800223 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140188800223/5000000000000000 : ℝ)) (X := (50005700891195773107/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100071787147648189171/100000000000000000000 : ℝ) ≤ (5000882446575199/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (100071787147648189171/100000000000000000000 : ℝ)^256 ≤ (5000882446575199/5000000000000000 : ℝ)^1041 := by
      have hnat : (100071787147648189171 : ℕ)^256*5000000000000000^1041 ≤ 5000882446575199^1041*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100071787147648189171 100000000000000000000 5000882446575199 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000882446575199/5000000000000000 : ℝ)) (X := (100071787147648189171/100000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (782282597757069001/781250000000000000 : ℝ) ≤ (200064988174007/200000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (782282597757069001/781250000000000000 : ℝ)^256 ≤ (200064988174007/200000000000000 : ℝ)^1041 := by
      have hnat : (782282597757069001 : ℕ)^256*200000000000000^1041 ≤ 200064988174007^1041*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        782282597757069001 781250000000000000 200064988174007 200000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200064988174007/200000000000000 : ℝ)) (X := (782282597757069001/781250000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5700891195773107/100000000000000000000 : ℝ) ≤ ((7474524743508210287/7477000000000000000 : ℝ)+2*(5798888867/2920703125000 : ℝ)*(9043/100000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (7474524743508210287/7477000000000000000 : ℝ)+2*(5798888867/2920703125000 : ℝ)*(9043/100000 : ℝ)=(5000140188800223/5000000000000000 : ℝ) by norm_num, show 1+2*(5700891195773107/100000000000000000000 : ℝ)=(50005700891195773107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1032597757069001/1562500000000000000 : ℝ)+(5700891195773107/100000000000000000000 : ℝ) ≤ ((7474524743508210287/7477000000000000000 : ℝ)+(5798888867/2920703125000 : ℝ)*((413/2500 : ℝ)+(9043/100000 : ℝ)))^(1041/256 : ℝ) := by
    rw [show (7474524743508210287/7477000000000000000 : ℝ)+(5798888867/2920703125000 : ℝ)*((413/2500 : ℝ)+(9043/100000 : ℝ))=(5000882446575199/5000000000000000 : ℝ) by norm_num, show 1+(1032597757069001/1562500000000000000 : ℝ)+(5700891195773107/100000000000000000000 : ℝ)=(100071787147648189171/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1032597757069001/1562500000000000000 : ℝ) ≤ ((7474524743508210287/7477000000000000000 : ℝ)+2*(5798888867/2920703125000 : ℝ)*(413/2500 : ℝ))^(1041/256 : ℝ) := by
    rw [show (7474524743508210287/7477000000000000000 : ℝ)+2*(5798888867/2920703125000 : ℝ)*(413/2500 : ℝ)=(200064988174007/200000000000000 : ℝ) by norm_num, show 1+2*(1032597757069001/1562500000000000000 : ℝ)=(782282597757069001/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7474524743508210287/7477000000000000000 : ℝ)*(X 1 0+X 2 0)+(5798888867/2920703125000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (9043/100000 : ℝ)) (hi := (413/2500 : ℝ)) (c := (7474524743508210287/7477000000000000000 : ℝ)) (alpha := (5798888867/2920703125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7474524743508210287/7477000000000000000 : ℝ)*(X 0 1+X 2 1)+(5798888867/2920703125000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (9043/100000 : ℝ)) (hi := (413/2500 : ℝ)) (c := (7474524743508210287/7477000000000000000 : ℝ)) (alpha := (5798888867/2920703125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7474524743508210287/7477000000000000000 : ℝ)*(X 0 2+X 1 2)+(5798888867/2920703125000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (9043/100000 : ℝ)) (hi := (413/2500 : ℝ)) (c := (7474524743508210287/7477000000000000000 : ℝ)) (alpha := (5798888867/2920703125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2165891683/10000000000 : ℝ)*X 0 0+(217191849/400000000 : ℝ)*X 0 1+(5231519173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167310553/312500000 : ℝ)*X 1 0+(-2267257491/10000000000 : ℝ)*X 1 1+(5231519031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676968891/5000000000 : ℝ)*X 2 0+(5231519121/10000000000 : ℝ)*X 2 1+(-2267257259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363223011/10000000000 : ℝ)*X 0 0+(4170647277/10000000000 : ℝ)*X 0 1+(4564649833/10000000000 : ℝ)*X 0 2+(4363223011/10000000000 : ℝ)*X 1 0+(4170647277/10000000000 : ℝ)*X 1 1+(4564649833/10000000000 : ℝ)*X 1 2+(4363223011/10000000000 : ℝ)*X 2 0+(4170647277/10000000000 : ℝ)*X 2 1+(4564649833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43318201/200000000 : ℝ)*X 0 0+(5232291881/10000000000 : ℝ)*X 0 1+(339313699/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303727147/10000000000 : ℝ)*X 1 0+(-2069757229/10000000000 : ℝ)*X 1 1+(2714509677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325931761/2500000000 : ℝ)*X 2 0+(1357254879/2500000000 : ℝ)*X 2 1+(-1034878573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363259501/10000000000 : ℝ)*X 0 0+(4563114751/10000000000 : ℝ)*X 0 1+(4172191003/10000000000 : ℝ)*X 0 2+(4363259501/10000000000 : ℝ)*X 1 0+(4563114751/10000000000 : ℝ)*X 1 1+(4172191003/10000000000 : ℝ)*X 1 2+(4363259501/10000000000 : ℝ)*X 2 0+(4563114751/10000000000 : ℝ)*X 2 1+(4172191003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122808777586278298152981/18692500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1704521411/100000000000000 : ℝ)*(base19) + (1610391897/100000000000000 : ℝ)*(base23) + (11721313/12500000000000 : ℝ)*(lower2) + (22470067/25000000000000 : ℝ)*(upper3) + (215243813/100000000000000 : ℝ)*(upper5) + (236924689671863/6250000000000 : ℝ)*(major0) + (236924689671863/6250000000000 : ℝ)*(major1) + (236924689671863/6250000000000 : ℝ)*(major2) + (2521737207744807/50000000000000 : ℝ)*(sp0) + (126087642204183/2500000000000 : ℝ)*(sp1) + (1008701156459367/20000000000000 : ℝ)*(sp2) + (317258606627593/12500000000000 : ℝ)*(sp3) + (16488599559/50000000000000 : ℝ)*(sp4) + (680239591/5000000000000 : ℝ)*(sp7) + (634520614453141/25000000000000 : ℝ)*(f.failure) + (1260876848172183/25000000000000 : ℝ)*(f.sum) + (34900461127727/18692500000000000000000000000 : ℝ)*base66 + (46935656579635319/46731250000000000000000000000000 : ℝ)*base68 + (23476134239052181/46731250000000000000000000000000 : ℝ)*base69 + (498633101778389681/46731250000000000000000000000000 : ℝ)*base71 + (1032436347459/9346250000000000000000000000 : ℝ)*base73 + (674955649980789681/46731250000000000000000000000000 : ℝ)*base75 + (246367011935672819/46731250000000000000000000000000 : ℝ)*base78 + (268657396155754069/46731250000000000000000000000000 : ℝ)*base80 + (157116673830621/37385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10224893/1250000000000000000000 : ℝ)*base90 + (10224893/1250000000000000000000 : ℝ)*base92 + (10224893/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (820772302521086034925617783/93462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32653071/2000000000000 : ℝ)*(base19) + (905707333/50000000000000 : ℝ)*(base23) + (11891003/5000000000000 : ℝ)*(upper3) + (108152651/100000000000000 : ℝ)*(lower4) + (74920481/50000000000000 : ℝ)*(upper5) + (1910304442295703/50000000000000 : ℝ)*(major0) + (1910304442295703/50000000000000 : ℝ)*(major1) + (1910304442295703/50000000000000 : ℝ)*(major2) + (30120288299/100000000000000 : ℝ)*(sp1) + (37890233167/100000000000000 : ℝ)*(sp2) + (5083173504345481/100000000000000 : ℝ)*(sp4) + (317696359462727/6250000000000 : ℝ)*(sp5) + (317695862668603/6250000000000 : ℝ)*(sp6) + (639510993027369/25000000000000 : ℝ)*(sp7) + (639510993027369/25000000000000 : ℝ)*(f.failure) + (5083173504345481/100000000000000 : ℝ)*(f.sum) + (79754111804249/18692500000000000000000000000 : ℝ)*base66 + (831705777879393239/373850000000000000000000000000000 : ℝ)*base68 + (1550305032944856761/373850000000000000000000000000000 : ℝ)*base69 + (2741304753020343239/373850000000000000000000000000000 : ℝ)*base72 + (98183608797997/37385000000000000000000000000 : ℝ)*base73 + (882076901763193239/373850000000000000000000000000000 : ℝ)*base76 + (2983182375007643239/373850000000000000000000000000000 : ℝ)*base78 + (193485811593293239/373850000000000000000000000000000 : ℝ)*base80 + (199746854045217/37385000000000000000000000000 : ℝ)*base81 + (7131663/1250000000000000000000 : ℝ)*base89 + (7131663/1250000000000000000000 : ℝ)*base91 + (7131663/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1136_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14813/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1136_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1136_s4_0 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168939801/10000000000 : ℝ)*x 0 + (2701091719/5000000000 : ℝ)*x 1 + (5257138371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168939801/10000000000 : ℝ)^8329 ≤ (6588591030159/50000000000000 : ℝ)^6281 := by
    have hnat : (2168939801 : ℕ)^8329*50000000000000^6281 ≤ 6588591030159^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168939801 10000000000 6588591030159 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701091719/5000000000 : ℝ)^8329 ≤ (8838939225601/20000000000000 : ℝ)^6281 := by
    have hnat : (2701091719 : ℕ)^8329*20000000000000^6281 ≤ 8838939225601^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701091719 5000000000 8838939225601 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257138371/10000000000 : ℝ)^8329 ≤ (5328515225097/12500000000000 : ℝ)^6281 := by
    have hnat : (5257138371 : ℕ)^8329*12500000000000^6281 ≤ 5328515225097^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257138371 10000000000 5328515225097 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168939801/10000000000 : ℝ), (2701091719/5000000000 : ℝ), (5257138371/10000000000 : ℝ)] ![(6588591030159/50000000000000 : ℝ), (8838939225601/20000000000000 : ℝ), (5328515225097/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168939801/10000000000 : ℝ)|^8329 ≤ (6588591030159/50000000000000 : ℝ)^6281
        have hw : |(-2168939801/10000000000 : ℝ)|=(2168939801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701091719/5000000000 : ℝ)|^8329 ≤ (8838939225601/20000000000000 : ℝ)^6281
        have hw : |(2701091719/5000000000 : ℝ)|=(2701091719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257138371/10000000000 : ℝ)|^8329 ≤ (5328515225097/12500000000000 : ℝ)^6281
        have hw : |(5257138371/10000000000 : ℝ)|=(5257138371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_1 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336761569/2500000000 : ℝ)*x 0 + (-2242655677/10000000000 : ℝ)*x 1 + (5257138689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336761569/2500000000 : ℝ)^8329 ≤ (8719508966391/20000000000000 : ℝ)^6281 := by
    have hnat : (1336761569 : ℕ)^8329*20000000000000^6281 ≤ 8719508966391^6281*2500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336761569 2500000000 8719508966391 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242655677/10000000000 : ℝ)^8329 ≤ (1721791242543/12500000000000 : ℝ)^6281 := by
    have hnat : (2242655677 : ℕ)^8329*12500000000000^6281 ≤ 1721791242543^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242655677 10000000000 1721791242543 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257138689/10000000000 : ℝ)^8329 ≤ (21314062610041/50000000000000 : ℝ)^6281 := by
    have hnat : (5257138689 : ℕ)^8329*50000000000000^6281 ≤ 21314062610041^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257138689 10000000000 21314062610041 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336761569/2500000000 : ℝ), (-2242655677/10000000000 : ℝ), (5257138689/10000000000 : ℝ)] ![(8719508966391/20000000000000 : ℝ), (1721791242543/12500000000000 : ℝ), (21314062610041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336761569/2500000000 : ℝ)|^8329 ≤ (8719508966391/20000000000000 : ℝ)^6281
        have hw : |(1336761569/2500000000 : ℝ)|=(1336761569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2242655677/10000000000 : ℝ)|^8329 ≤ (1721791242543/12500000000000 : ℝ)^6281
        have hw : |(-2242655677/10000000000 : ℝ)|=(2242655677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257138689/10000000000 : ℝ)|^8329 ≤ (21314062610041/50000000000000 : ℝ)^6281
        have hw : |(5257138689/10000000000 : ℝ)|=(5257138689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_2 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347046863/10000000000 : ℝ)*x 0 + (5257137763/10000000000 : ℝ)*x 1 + (-2242656119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347046863/10000000000 : ℝ)^8329 ≤ (43597551178689/100000000000000 : ℝ)^6281 := by
    have hnat : (5347046863 : ℕ)^8329*100000000000000^6281 ≤ 43597551178689^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347046863 10000000000 43597551178689 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257137763/10000000000 : ℝ)^8329 ≤ (8525623052647/20000000000000 : ℝ)^6281 := by
    have hnat : (5257137763 : ℕ)^8329*20000000000000^6281 ≤ 8525623052647^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257137763 10000000000 8525623052647 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242656119/10000000000 : ℝ)^8329 ≤ (3443583385069/25000000000000 : ℝ)^6281 := by
    have hnat : (2242656119 : ℕ)^8329*25000000000000^6281 ≤ 3443583385069^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242656119 10000000000 3443583385069 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347046863/10000000000 : ℝ), (5257137763/10000000000 : ℝ), (-2242656119/10000000000 : ℝ)] ![(43597551178689/100000000000000 : ℝ), (8525623052647/20000000000000 : ℝ), (3443583385069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347046863/10000000000 : ℝ)|^8329 ≤ (43597551178689/100000000000000 : ℝ)^6281
        have hw : |(5347046863/10000000000 : ℝ)|=(5347046863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257137763/10000000000 : ℝ)|^8329 ≤ (8525623052647/20000000000000 : ℝ)^6281
        have hw : |(5257137763/10000000000 : ℝ)|=(5257137763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242656119/10000000000 : ℝ)|^8329 ≤ (3443583385069/25000000000000 : ℝ)^6281
        have hw : |(-2242656119/10000000000 : ℝ)|=(2242656119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_3 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182521591/5000000000 : ℝ)*x 0 + (844659839/2000000000 : ℝ)*x 1 + (563940673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182521591/5000000000 : ℝ)^8329 ≤ (33312116508251/100000000000000 : ℝ)^6281 := by
    have hnat : (2182521591 : ℕ)^8329*100000000000000^6281 ≤ 33312116508251^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182521591 5000000000 33312116508251 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844659839/2000000000 : ℝ)^8329 ≤ (6377065325447/20000000000000 : ℝ)^6281 := by
    have hnat : (844659839 : ℕ)^8329*20000000000000^6281 ≤ 6377065325447^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844659839 2000000000 6377065325447 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563940673/1250000000 : ℝ)^8329 ≤ (3480255684279/10000000000000 : ℝ)^6281 := by
    have hnat : (563940673 : ℕ)^8329*10000000000000^6281 ≤ 3480255684279^6281*1250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563940673 1250000000 3480255684279 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182521591/5000000000 : ℝ), (844659839/2000000000 : ℝ), (563940673/1250000000 : ℝ)] ![(33312116508251/100000000000000 : ℝ), (6377065325447/20000000000000 : ℝ), (3480255684279/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182521591/5000000000 : ℝ)|^8329 ≤ (33312116508251/100000000000000 : ℝ)^6281
        have hw : |(2182521591/5000000000 : ℝ)|=(2182521591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844659839/2000000000 : ℝ)|^8329 ≤ (6377065325447/20000000000000 : ℝ)^6281
        have hw : |(844659839/2000000000 : ℝ)|=(844659839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563940673/1250000000 : ℝ)|^8329 ≤ (3480255684279/10000000000000 : ℝ)^6281
        have hw : |(563940673/1250000000 : ℝ)|=(563940673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_4 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084473889/5000000000 : ℝ)*x 0 + (262877587/500000000 : ℝ)*x 1 + (2700883893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084473889/5000000000 : ℝ)^8329 ≤ (6588623162989/50000000000000 : ℝ)^6281 := by
    have hnat : (1084473889 : ℕ)^8329*50000000000000^6281 ≤ 6588623162989^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084473889 5000000000 6588623162989 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262877587/500000000 : ℝ)^8329 ≤ (42632566622329/100000000000000 : ℝ)^6281 := by
    have hnat : (262877587 : ℕ)^8329*100000000000000^6281 ≤ 42632566622329^6281*500000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262877587 500000000 42632566622329 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700883893/5000000000 : ℝ)^8329 ≤ (44190187033679/100000000000000 : ℝ)^6281 := by
    have hnat : (2700883893 : ℕ)^8329*100000000000000^6281 ≤ 44190187033679^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700883893 5000000000 44190187033679 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084473889/5000000000 : ℝ), (262877587/500000000 : ℝ), (2700883893/5000000000 : ℝ)] ![(6588623162989/50000000000000 : ℝ), (42632566622329/100000000000000 : ℝ), (44190187033679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084473889/5000000000 : ℝ)|^8329 ≤ (6588623162989/50000000000000 : ℝ)^6281
        have hw : |(-1084473889/5000000000 : ℝ)|=(1084473889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262877587/500000000 : ℝ)|^8329 ≤ (42632566622329/100000000000000 : ℝ)^6281
        have hw : |(262877587/500000000 : ℝ)|=(262877587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700883893/5000000000 : ℝ)|^8329 ≤ (44190187033679/100000000000000 : ℝ)^6281
        have hw : |(2700883893/5000000000 : ℝ)|=(2700883893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_5 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53103173/100000000 : ℝ)*x 0 + (-262253223/1250000000 : ℝ)*x 1 + (5401767893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53103173/100000000 : ℝ)^8329 ≤ (10800217738557/25000000000000 : ℝ)^6281 := by
    have hnat : (53103173 : ℕ)^8329*25000000000000^6281 ≤ 10800217738557^6281*100000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53103173 100000000 10800217738557 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262253223/1250000000 : ℝ)^8329 ≤ (1576117604407/12500000000000 : ℝ)^6281 := by
    have hnat : (262253223 : ℕ)^8329*12500000000000^6281 ≤ 1576117604407^6281*1250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262253223 1250000000 1576117604407 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401767893/10000000000 : ℝ)^8329 ≤ (44190188194427/100000000000000 : ℝ)^6281 := by
    have hnat : (5401767893 : ℕ)^8329*100000000000000^6281 ≤ 44190188194427^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401767893 10000000000 44190188194427 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53103173/100000000 : ℝ), (-262253223/1250000000 : ℝ), (5401767893/10000000000 : ℝ)] ![(10800217738557/25000000000000 : ℝ), (1576117604407/12500000000000 : ℝ), (44190188194427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53103173/100000000 : ℝ)|^8329 ≤ (10800217738557/25000000000000 : ℝ)^6281
        have hw : |(53103173/100000000 : ℝ)|=(53103173/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262253223/1250000000 : ℝ)|^8329 ≤ (1576117604407/12500000000000 : ℝ)^6281
        have hw : |(-262253223/1250000000 : ℝ)|=(262253223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401767893/10000000000 : ℝ)|^8329 ≤ (44190188194427/100000000000000 : ℝ)^6281
        have hw : |(5401767893/10000000000 : ℝ)|=(5401767893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_6 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310317497/10000000000 : ℝ)*x 0 + (5401767671/10000000000 : ℝ)*x 1 + (-2098025819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310317497/10000000000 : ℝ)^8329 ≤ (540010913493/1250000000000 : ℝ)^6281 := by
    have hnat : (5310317497 : ℕ)^8329*1250000000000^6281 ≤ 540010913493^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310317497 10000000000 540010913493 1250000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401767671/10000000000 : ℝ)^8329 ≤ (44190185786147/100000000000000 : ℝ)^6281 := by
    have hnat : (5401767671 : ℕ)^8329*100000000000000^6281 ≤ 44190185786147^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401767671 10000000000 44190185786147 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098025819/10000000000 : ℝ)^8329 ≤ (12608941114189/100000000000000 : ℝ)^6281 := by
    have hnat : (2098025819 : ℕ)^8329*100000000000000^6281 ≤ 12608941114189^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098025819 10000000000 12608941114189 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310317497/10000000000 : ℝ), (5401767671/10000000000 : ℝ), (-2098025819/10000000000 : ℝ)] ![(540010913493/1250000000000 : ℝ), (44190185786147/100000000000000 : ℝ), (12608941114189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310317497/10000000000 : ℝ)|^8329 ≤ (540010913493/1250000000000 : ℝ)^6281
        have hw : |(5310317497/10000000000 : ℝ)|=(5310317497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401767671/10000000000 : ℝ)|^8329 ≤ (44190185786147/100000000000000 : ℝ)^6281
        have hw : |(5401767671/10000000000 : ℝ)|=(5401767671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098025819/10000000000 : ℝ)|^8329 ≤ (12608941114189/100000000000000 : ℝ)^6281
        have hw : |(-2098025819/10000000000 : ℝ)|=(2098025819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s4_7 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365057267/10000000000 : ℝ)*x 0 + (70479717/156250000 : ℝ)*x 1 + (2112063161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365057267/10000000000 : ℝ)^8329 ≤ (1665612952381/5000000000000 : ℝ)^6281 := by
    have hnat : (4365057267 : ℕ)^8329*5000000000000^6281 ≤ 1665612952381^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365057267 10000000000 1665612952381 5000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70479717/156250000 : ℝ)^8329 ≤ (34794133191423/100000000000000 : ℝ)^6281 := by
    have hnat : (70479717 : ℕ)^8329*100000000000000^6281 ≤ 34794133191423^6281*156250000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70479717 156250000 34794133191423 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112063161/5000000000 : ℝ)^8329 ≤ (6378721549733/20000000000000 : ℝ)^6281 := by
    have hnat : (2112063161 : ℕ)^8329*20000000000000^6281 ≤ 6378721549733^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112063161 5000000000 6378721549733 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365057267/10000000000 : ℝ), (70479717/156250000 : ℝ), (2112063161/5000000000 : ℝ)] ![(1665612952381/5000000000000 : ℝ), (34794133191423/100000000000000 : ℝ), (6378721549733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365057267/10000000000 : ℝ)|^8329 ≤ (1665612952381/5000000000000 : ℝ)^6281
        have hw : |(4365057267/10000000000 : ℝ)|=(4365057267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70479717/156250000 : ℝ)|^8329 ≤ (34794133191423/100000000000000 : ℝ)^6281
        have hw : |(70479717/156250000 : ℝ)|=(70479717/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112063161/5000000000 : ℝ)|^8329 ≤ (6378721549733/20000000000000 : ℝ)^6281
        have hw : |(2112063161/5000000000 : ℝ)|=(2112063161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1136_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14813/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2791/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14813/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14813/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14813/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14813/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14813/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14813/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10617/100000 : ℝ) ^ (1041/256 : ℝ) ≤ (218956427388681/2000000000000000000 : ℝ) := by
    have hpowers : (10617/100000 : ℝ)^1041 ≤ (218956427388681/2000000000000000000 : ℝ)^256 := by
      have hnat : (10617 : ℕ)^1041*2000000000000000000^256 ≤ 218956427388681^256*100000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10617 100000 218956427388681 2000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10617/100000 : ℝ)) (X := (218956427388681/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14813/100000 : ℝ) ^ (1041/256 : ℝ) ≤ (42412864455498127/100000000000000000000 : ℝ) := by
    have hpowers : (14813/100000 : ℝ)^1041 ≤ (42412864455498127/100000000000000000000 : ℝ)^256 := by
      have hnat : (14813 : ℕ)^1041*100000000000000000000^256 ≤ 42412864455498127^256*100000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14813 100000 42412864455498127 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14813/100000 : ℝ)) (X := (42412864455498127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000218956427388681/1000000000000000000 : ℝ) ≤ (5000269203739321/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (1000218956427388681/1000000000000000000 : ℝ)^256 ≤ (5000269203739321/5000000000000000 : ℝ)^1041 := by
      have hnat : (1000218956427388681 : ℕ)^256*5000000000000000^1041 ≤ 5000269203739321^1041*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000218956427388681 1000000000000000000 5000269203739321 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269203739321/5000000000000000 : ℝ)) (X := (1000218956427388681/1000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053360685824932177/100000000000000000000 : ℝ) ≤ (250032799202883/250000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (100053360685824932177/100000000000000000000 : ℝ)^256 ≤ (250032799202883/250000000000000 : ℝ)^1041 := by
      have hnat : (100053360685824932177 : ℕ)^256*250000000000000^1041 ≤ 250032799202883^1041*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053360685824932177 100000000000000000000 250032799202883 250000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250032799202883/250000000000000 : ℝ)) (X := (100053360685824932177/100000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042412864455498127/50000000000000000000 : ℝ) ≤ (5001042764375999/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50042412864455498127/50000000000000000000 : ℝ)^256 ≤ (5001042764375999/5000000000000000 : ℝ)^1041 := by
      have hnat : (50042412864455498127 : ℕ)^256*5000000000000000^1041 ≤ 5001042764375999^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042412864455498127 50000000000000000000 5001042764375999 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001042764375999/5000000000000000 : ℝ)) (X := (50042412864455498127/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(218956427388681/2000000000000000000 : ℝ) ≤ ((2097291668561058059/2098000000000000000 : ℝ)+2*(386780318339/209800000000000 : ℝ)*(10617/100000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (2097291668561058059/2098000000000000000 : ℝ)+2*(386780318339/209800000000000 : ℝ)*(10617/100000 : ℝ)=(5000269203739321/5000000000000000 : ℝ) by norm_num, show 1+2*(218956427388681/2000000000000000000 : ℝ)=(1000218956427388681/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42412864455498127/100000000000000000000 : ℝ)+(218956427388681/2000000000000000000 : ℝ) ≤ ((2097291668561058059/2098000000000000000 : ℝ)+(386780318339/209800000000000 : ℝ)*((14813/100000 : ℝ)+(10617/100000 : ℝ)))^(1041/256 : ℝ) := by
    rw [show (2097291668561058059/2098000000000000000 : ℝ)+(386780318339/209800000000000 : ℝ)*((14813/100000 : ℝ)+(10617/100000 : ℝ))=(250032799202883/250000000000000 : ℝ) by norm_num, show 1+(42412864455498127/100000000000000000000 : ℝ)+(218956427388681/2000000000000000000 : ℝ)=(100053360685824932177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42412864455498127/100000000000000000000 : ℝ) ≤ ((2097291668561058059/2098000000000000000 : ℝ)+2*(386780318339/209800000000000 : ℝ)*(14813/100000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (2097291668561058059/2098000000000000000 : ℝ)+2*(386780318339/209800000000000 : ℝ)*(14813/100000 : ℝ)=(5001042764375999/5000000000000000 : ℝ) by norm_num, show 1+2*(42412864455498127/100000000000000000000 : ℝ)=(50042412864455498127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2097291668561058059/2098000000000000000 : ℝ)*(X 1 0+X 2 0)+(386780318339/209800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (14813/100000 : ℝ)) (c := (2097291668561058059/2098000000000000000 : ℝ)) (alpha := (386780318339/209800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2097291668561058059/2098000000000000000 : ℝ)*(X 0 1+X 2 1)+(386780318339/209800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (14813/100000 : ℝ)) (c := (2097291668561058059/2098000000000000000 : ℝ)) (alpha := (386780318339/209800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2097291668561058059/2098000000000000000 : ℝ)*(X 0 2+X 1 2)+(386780318339/209800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (14813/100000 : ℝ)) (c := (2097291668561058059/2098000000000000000 : ℝ)) (alpha := (386780318339/209800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2168939801/10000000000 : ℝ)*X 0 0+(2701091719/5000000000 : ℝ)*X 0 1+(5257138371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336761569/2500000000 : ℝ)*X 1 0+(-2242655677/10000000000 : ℝ)*X 1 1+(5257138689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347046863/10000000000 : ℝ)*X 2 0+(5257137763/10000000000 : ℝ)*X 2 1+(-2242656119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182521591/5000000000 : ℝ)*X 0 0+(844659839/2000000000 : ℝ)*X 0 1+(563940673/1250000000 : ℝ)*X 0 2+(2182521591/5000000000 : ℝ)*X 1 0+(844659839/2000000000 : ℝ)*X 1 1+(563940673/1250000000 : ℝ)*X 1 2+(2182521591/5000000000 : ℝ)*X 2 0+(844659839/2000000000 : ℝ)*X 2 1+(563940673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084473889/5000000000 : ℝ)*X 0 0+(262877587/500000000 : ℝ)*X 0 1+(2700883893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53103173/100000000 : ℝ)*X 1 0+(-262253223/1250000000 : ℝ)*X 1 1+(5401767893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310317497/10000000000 : ℝ)*X 2 0+(5401767671/10000000000 : ℝ)*X 2 1+(-2098025819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365057267/10000000000 : ℝ)*X 0 0+(70479717/156250000 : ℝ)*X 0 1+(2112063161/5000000000 : ℝ)*X 0 2+(4365057267/10000000000 : ℝ)*X 1 0+(70479717/156250000 : ℝ)*X 1 1+(2112063161/5000000000 : ℝ)*X 1 2+(4365057267/10000000000 : ℝ)*X 2 0+(70479717/156250000 : ℝ)*X 2 1+(2112063161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116763872919895638613179477/13112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9797167/6250000000000 : ℝ)*(base21) + (458105889/100000000000000 : ℝ)*(lower2) + (219241929/100000000000000 : ℝ)*(upper3) + (15675347/20000000000000 : ℝ)*(lower4) + (4551209/50000000000000 : ℝ)*(upper5) + (647745116916401/12500000000000 : ℝ)*(major0) + (647745116916401/12500000000000 : ℝ)*(major1) + (647745116916401/12500000000000 : ℝ)*(major2) + (6894400265913279/100000000000000 : ℝ)*(sp0) + (6894400265913279/100000000000000 : ℝ)*(sp1) + (275774938087677/4000000000000 : ℝ)*(sp2) + (3469503623114489/100000000000000 : ℝ)*(sp3) + (13328483341/50000000000000 : ℝ)*(sp6) + (3536961753/20000000000000 : ℝ)*(sp7) + (3469521307923253/100000000000000 : ℝ)*(f.failure) + (6894400265913279/100000000000000 : ℝ)*(f.sum) + (167219059178563/2622500000000000000000000000 : ℝ)*base65 + (140391439034609341/26225000000000000000000000000000 : ℝ)*base68 + (547331890363659341/26225000000000000000000000000000 : ℝ)*base70 + (1524197154749890659/26225000000000000000000000000000 : ℝ)*base71 + (3858788986821/1311250000000000000000000000 : ℝ)*base74 + (404678976248109341/26225000000000000000000000000000 : ℝ)*base76 + (395470674475734341/26225000000000000000000000000000 : ℝ)*base78 + (330745191551515659/26225000000000000000000000000000 : ℝ)*base79 + (42500141024129/5245000000000000000000000000 : ℝ)*base82 + (21562269/5000000000000000000000 : ℝ)*base90 + (21562269/5000000000000000000000 : ℝ)*base92 + (21562269/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56251693890938187981477993/52450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173429357/25000000000000 : ℝ)*(base19) + (1172528943/100000000000000 : ℝ)*(base23) + (16727541/12500000000000 : ℝ)*(upper2) + (138083/400000000000 : ℝ)*(upper3) + (327811197/100000000000000 : ℝ)*(upper5) + (2605882051525209/50000000000000 : ℝ)*(major0) + (2605882051525209/50000000000000 : ℝ)*(major1) + (2605882051525209/50000000000000 : ℝ)*(major2) + (24798655899/100000000000000 : ℝ)*(sp1) + (20399451729/100000000000000 : ℝ)*(sp2) + (866756562527663/12500000000000 : ℝ)*(sp4) + (3467013503923989/50000000000000 : ℝ)*(sp5) + (866753866030079/12500000000000 : ℝ)*(sp6) + (872368917532529/25000000000000 : ℝ)*(sp7) + (872368917532529/25000000000000 : ℝ)*(f.failure) + (866756562527663/12500000000000 : ℝ)*(f.sum) + (26060209954849/5245000000000000000000000000 : ℝ)*base66 + (465877454986419331/104900000000000000000000000000000 : ℝ)*base67 + (166333689620780669/104900000000000000000000000000000 : ℝ)*base70 + (346303087800780669/104900000000000000000000000000000 : ℝ)*base72 + (9191871231383/2622500000000000000000000000 : ℝ)*base73 + (1278088417443680669/104900000000000000000000000000000 : ℝ)*base76 + (987086070765080669/104900000000000000000000000000000 : ℝ)*base78 + (1657805662525319331/104900000000000000000000000000000 : ℝ)*base79 + (13639761412283/2622500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8798983/1250000000000000000000 : ℝ)*base89 + (8798983/1250000000000000000000 : ℝ)*base91 + (8798983/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1136_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14813/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1136_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1136_s5_0 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-433918453/2000000000 : ℝ)*x 0 + (5395068643/10000000000 : ℝ)*x 1 + (5263824773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433918453/2000000000 : ℝ)^8329 ≤ (659121940301/5000000000000 : ℝ)^6281 := by
    have hnat : (433918453 : ℕ)^8329*5000000000000^6281 ≤ 659121940301^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433918453 2000000000 659121940301 5000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395068643/10000000000 : ℝ)^8329 ≤ (44117528704993/100000000000000 : ℝ)^6281 := by
    have hnat : (5395068643 : ℕ)^8329*100000000000000^6281 ≤ 44117528704993^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395068643 10000000000 44117528704993 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263824773/10000000000 : ℝ)^8329 ≤ (5337504059369/12500000000000 : ℝ)^6281 := by
    have hnat : (5263824773 : ℕ)^8329*12500000000000^6281 ≤ 5337504059369^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263824773 10000000000 5337504059369 12500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433918453/2000000000 : ℝ), (5395068643/10000000000 : ℝ), (5263824773/10000000000 : ℝ)] ![(659121940301/5000000000000 : ℝ), (44117528704993/100000000000000 : ℝ), (5337504059369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433918453/2000000000 : ℝ)|^8329 ≤ (659121940301/5000000000000 : ℝ)^6281
        have hw : |(-433918453/2000000000 : ℝ)|=(433918453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395068643/10000000000 : ℝ)|^8329 ≤ (44117528704993/100000000000000 : ℝ)^6281
        have hw : |(5395068643/10000000000 : ℝ)|=(5395068643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263824773/10000000000 : ℝ)|^8329 ≤ (5337504059369/12500000000000 : ℝ)^6281
        have hw : |(5263824773/10000000000 : ℝ)|=(5263824773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_1 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345263117/10000000000 : ℝ)*x 0 + (-1118095447/5000000000 : ℝ)*x 1 + (2631912389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345263117/10000000000 : ℝ)^8329 ≤ (4357826609337/10000000000000 : ℝ)^6281 := by
    have hnat : (5345263117 : ℕ)^8329*10000000000000^6281 ≤ 4357826609337^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345263117 10000000000 4357826609337 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118095447/5000000000 : ℝ)^8329 ≤ (2744340272853/20000000000000 : ℝ)^6281 := by
    have hnat : (1118095447 : ℕ)^8329*20000000000000^6281 ≤ 2744340272853^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118095447 5000000000 2744340272853 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631912389/5000000000 : ℝ)^8329 ≤ (42700032528737/100000000000000 : ℝ)^6281 := by
    have hnat : (2631912389 : ℕ)^8329*100000000000000^6281 ≤ 42700032528737^6281*5000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631912389 5000000000 42700032528737 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345263117/10000000000 : ℝ), (-1118095447/5000000000 : ℝ), (2631912389/5000000000 : ℝ)] ![(4357826609337/10000000000000 : ℝ), (2744340272853/20000000000000 : ℝ), (42700032528737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345263117/10000000000 : ℝ)|^8329 ≤ (4357826609337/10000000000000 : ℝ)^6281
        have hw : |(5345263117/10000000000 : ℝ)|=(5345263117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118095447/5000000000 : ℝ)|^8329 ≤ (2744340272853/20000000000000 : ℝ)^6281
        have hw : |(-1118095447/5000000000 : ℝ)|=(1118095447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631912389/5000000000 : ℝ)|^8329 ≤ (42700032528737/100000000000000 : ℝ)^6281
        have hw : |(2631912389/5000000000 : ℝ)|=(2631912389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_2 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534526323/1000000000 : ℝ)*x 0 + (5263824677/10000000000 : ℝ)*x 1 + (-2236190877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534526323/1000000000 : ℝ)^8329 ≤ (4357826731501/10000000000000 : ℝ)^6281 := by
    have hnat : (534526323 : ℕ)^8329*10000000000000^6281 ≤ 4357826731501^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534526323 1000000000 4357826731501 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263824677/10000000000 : ℝ)^8329 ≤ (42700031442281/100000000000000 : ℝ)^6281 := by
    have hnat : (5263824677 : ℕ)^8329*100000000000000^6281 ≤ 42700031442281^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263824677 10000000000 42700031442281 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236190877/10000000000 : ℝ)^8329 ≤ (13721701225937/100000000000000 : ℝ)^6281 := by
    have hnat : (2236190877 : ℕ)^8329*100000000000000^6281 ≤ 13721701225937^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236190877 10000000000 13721701225937 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534526323/1000000000 : ℝ), (5263824677/10000000000 : ℝ), (-2236190877/10000000000 : ℝ)] ![(4357826731501/10000000000000 : ℝ), (42700031442281/100000000000000 : ℝ), (13721701225937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534526323/1000000000 : ℝ)|^8329 ≤ (4357826731501/10000000000000 : ℝ)^6281
        have hw : |(534526323/1000000000 : ℝ)|=(534526323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263824677/10000000000 : ℝ)|^8329 ≤ (42700031442281/100000000000000 : ℝ)^6281
        have hw : |(5263824677/10000000000 : ℝ)|=(5263824677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236190877/10000000000 : ℝ)|^8329 ≤ (13721701225937/100000000000000 : ℝ)^6281
        have hw : |(-2236190877/10000000000 : ℝ)|=(2236190877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_3 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436542259/1000000000 : ℝ)*x 0 + (423696357/1000000000 : ℝ)*x 1 + (4497762759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436542259/1000000000 : ℝ)^8329 ≤ (6663191229441/20000000000000 : ℝ)^6281 := by
    have hnat : (436542259 : ℕ)^8329*20000000000000^6281 ≤ 6663191229441^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436542259 1000000000 6663191229441 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423696357/1000000000 : ℝ)^8329 ≤ (1601110043319/5000000000000 : ℝ)^6281 := by
    have hnat : (423696357 : ℕ)^8329*5000000000000^6281 ≤ 1601110043319^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423696357 1000000000 1601110043319 5000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497762759/10000000000 : ℝ)^8329 ≤ (8665460743837/25000000000000 : ℝ)^6281 := by
    have hnat : (4497762759 : ℕ)^8329*25000000000000^6281 ≤ 8665460743837^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497762759 10000000000 8665460743837 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436542259/1000000000 : ℝ), (423696357/1000000000 : ℝ), (4497762759/10000000000 : ℝ)] ![(6663191229441/20000000000000 : ℝ), (1601110043319/5000000000000 : ℝ), (8665460743837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436542259/1000000000 : ℝ)|^8329 ≤ (6663191229441/20000000000000 : ℝ)^6281
        have hw : |(436542259/1000000000 : ℝ)|=(436542259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423696357/1000000000 : ℝ)|^8329 ≤ (1601110043319/5000000000000 : ℝ)^6281
        have hw : |(423696357/1000000000 : ℝ)|=(423696357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497762759/10000000000 : ℝ)|^8329 ≤ (8665460743837/25000000000000 : ℝ)^6281
        have hw : |(4497762759/10000000000 : ℝ)|=(4497762759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_4 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2169597673/10000000000 : ℝ)*x 0 + (658020503/1250000000 : ℝ)*x 1 + (67434101/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169597673/10000000000 : ℝ)^8329 ≤ (13182482379131/100000000000000 : ℝ)^6281 := by
    have hnat : (2169597673 : ℕ)^8329*100000000000000^6281 ≤ 13182482379131^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169597673 10000000000 13182482379131 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658020503/1250000000 : ℝ)^8329 ≤ (42703681833629/100000000000000 : ℝ)^6281 := by
    have hnat : (658020503 : ℕ)^8329*100000000000000^6281 ≤ 42703681833629^6281*1250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658020503 1250000000 42703681833629 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67434101/125000000 : ℝ)^8329 ≤ (44113835773389/100000000000000 : ℝ)^6281 := by
    have hnat : (67434101 : ℕ)^8329*100000000000000^6281 ≤ 44113835773389^6281*125000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67434101 125000000 44113835773389 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2169597673/10000000000 : ℝ), (658020503/1250000000 : ℝ), (67434101/125000000 : ℝ)] ![(13182482379131/100000000000000 : ℝ), (42703681833629/100000000000000 : ℝ), (44113835773389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2169597673/10000000000 : ℝ)|^8329 ≤ (13182482379131/100000000000000 : ℝ)^6281
        have hw : |(-2169597673/10000000000 : ℝ)|=(2169597673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658020503/1250000000 : ℝ)|^8329 ≤ (42703681833629/100000000000000 : ℝ)^6281
        have hw : |(658020503/1250000000 : ℝ)|=(658020503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67434101/125000000 : ℝ)|^8329 ≤ (44113835773389/100000000000000 : ℝ)^6281
        have hw : |(67434101/125000000 : ℝ)|=(67434101/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_5 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212481089/400000000 : ℝ)*x 0 + (-2105287519/10000000000 : ℝ)*x 1 + (5394728067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212481089/400000000 : ℝ)^8329 ≤ (10804829596981/25000000000000 : ℝ)^6281 := by
    have hnat : (212481089 : ℕ)^8329*25000000000000^6281 ≤ 10804829596981^6281*400000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212481089 400000000 10804829596981 25000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105287519/10000000000 : ℝ)^8329 ≤ (2533369193519/20000000000000 : ℝ)^6281 := by
    have hnat : (2105287519 : ℕ)^8329*20000000000000^6281 ≤ 2533369193519^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105287519 10000000000 2533369193519 20000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394728067/10000000000 : ℝ)^8329 ≤ (44113835632423/100000000000000 : ℝ)^6281 := by
    have hnat : (5394728067 : ℕ)^8329*100000000000000^6281 ≤ 44113835632423^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394728067 10000000000 44113835632423 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212481089/400000000 : ℝ), (-2105287519/10000000000 : ℝ), (5394728067/10000000000 : ℝ)] ![(10804829596981/25000000000000 : ℝ), (2533369193519/20000000000000 : ℝ), (44113835632423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212481089/400000000 : ℝ)|^8329 ≤ (10804829596981/25000000000000 : ℝ)^6281
        have hw : |(212481089/400000000 : ℝ)|=(212481089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105287519/10000000000 : ℝ)|^8329 ≤ (2533369193519/20000000000000 : ℝ)^6281
        have hw : |(-2105287519/10000000000 : ℝ)|=(2105287519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394728067/10000000000 : ℝ)|^8329 ≤ (44113835632423/100000000000000 : ℝ)^6281
        have hw : |(5394728067/10000000000 : ℝ)|=(5394728067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_6 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312027219/10000000000 : ℝ)*x 0 + (539472807/1000000000 : ℝ)*x 1 + (-2105287523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312027219/10000000000 : ℝ)^8329 ≤ (4321931832319/10000000000000 : ℝ)^6281 := by
    have hnat : (5312027219 : ℕ)^8329*10000000000000^6281 ≤ 4321931832319^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312027219 10000000000 4321931832319 10000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539472807/1000000000 : ℝ)^8329 ≤ (22056917832477/50000000000000 : ℝ)^6281 := by
    have hnat : (539472807 : ℕ)^8329*50000000000000^6281 ≤ 22056917832477^6281*1000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539472807 1000000000 22056917832477 50000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105287523/10000000000 : ℝ)^8329 ≤ (12666845999509/100000000000000 : ℝ)^6281 := by
    have hnat : (2105287523 : ℕ)^8329*100000000000000^6281 ≤ 12666845999509^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105287523 10000000000 12666845999509 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312027219/10000000000 : ℝ), (539472807/1000000000 : ℝ), (-2105287523/10000000000 : ℝ)] ![(4321931832319/10000000000000 : ℝ), (22056917832477/50000000000000 : ℝ), (12666845999509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312027219/10000000000 : ℝ)|^8329 ≤ (4321931832319/10000000000000 : ℝ)^6281
        have hw : |(5312027219/10000000000 : ℝ)|=(5312027219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539472807/1000000000 : ℝ)|^8329 ≤ (22056917832477/50000000000000 : ℝ)^6281
        have hw : |(539472807/1000000000 : ℝ)|=(539472807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105287523/10000000000 : ℝ)|^8329 ≤ (12666845999509/100000000000000 : ℝ)^6281
        have hw : |(-2105287523/10000000000 : ℝ)|=(2105287523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1136_s5_7 (p : ℝ) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873086633/2000000000 : ℝ)*x 0 + (4497088517/10000000000 : ℝ)*x 1 + (105941009/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873086633/2000000000 : ℝ)^8329 ≤ (166580315843/500000000000 : ℝ)^6281 := by
    have hnat : (873086633 : ℕ)^8329*500000000000^6281 ≤ 166580315843^6281*2000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873086633 2000000000 166580315843 500000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497088517/10000000000 : ℝ)^8329 ≤ (34654952893789/100000000000000 : ℝ)^6281 := by
    have hnat : (4497088517 : ℕ)^8329*100000000000000^6281 ≤ 34654952893789^6281*10000000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497088517 10000000000 34654952893789 100000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105941009/250000000 : ℝ)^8329 ≤ (1601449196397/5000000000000 : ℝ)^6281 := by
    have hnat : (105941009 : ℕ)^8329*5000000000000^6281 ≤ 1601449196397^6281*250000000^8329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105941009 250000000 1601449196397 5000000000000 8329 6281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8329/2048 : ℝ)) 8329 6281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873086633/2000000000 : ℝ), (4497088517/10000000000 : ℝ), (105941009/250000000 : ℝ)] ![(166580315843/500000000000 : ℝ), (34654952893789/100000000000000 : ℝ), (1601449196397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873086633/2000000000 : ℝ)|^8329 ≤ (166580315843/500000000000 : ℝ)^6281
        have hw : |(873086633/2000000000 : ℝ)|=(873086633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497088517/10000000000 : ℝ)|^8329 ≤ (34654952893789/100000000000000 : ℝ)^6281
        have hw : |(4497088517/10000000000 : ℝ)|=(4497088517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105941009/250000000 : ℝ)|^8329 ≤ (1601449196397/5000000000000 : ℝ)^6281
        have hw : |(105941009/250000000 : ℝ)|=(105941009/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1136_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5653/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7043/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2791/25000 : ℝ) ^ (1041/256 : ℝ) ≤ (2685830444661187/20000000000000000000 : ℝ) := by
    have hpowers : (2791/25000 : ℝ)^1041 ≤ (2685830444661187/20000000000000000000 : ℝ)^256 := by
      have hnat : (2791 : ℕ)^1041*20000000000000000000^256 ≤ 2685830444661187^256*25000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2791 25000 2685830444661187 20000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2791/25000 : ℝ)) (X := (2685830444661187/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (1041/256 : ℝ) ≤ (36075098911269979/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^1041 ≤ (36075098911269979/100000000000000000000 : ℝ)^256 := by
      have hnat : (2847 : ℕ)^1041*100000000000000000000^256 ≤ 36075098911269979^256*20000^1041 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 36075098911269979 100000000000000000000 1041 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (36075098911269979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002685830444661187/10000000000000000000 : ℝ) ≤ (5000330212764851/5000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (10002685830444661187/10000000000000000000 : ℝ)^256 ≤ (5000330212764851/5000000000000000 : ℝ)^1041 := by
      have hnat : (10002685830444661187 : ℕ)^256*5000000000000000^1041 ≤ 5000330212764851^1041*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002685830444661187 10000000000000000000 5000330212764851 5000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330212764851/5000000000000000 : ℝ)) (X := (10002685830444661187/10000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024752125567287957/50000000000000000000 : ℝ) ≤ (1250152146055767/1250000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50024752125567287957/50000000000000000000 : ℝ)^256 ≤ (1250152146055767/1250000000000000 : ℝ)^1041 := by
      have hnat : (50024752125567287957 : ℕ)^256*1250000000000000^1041 ≤ 1250152146055767^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024752125567287957 50000000000000000000 1250152146055767 1250000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250152146055767/1250000000000000 : ℝ)) (X := (50024752125567287957/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036075098911269979/50000000000000000000 : ℝ) ≤ (1000177391136257/1000000000000000 : ℝ) ^ (1041/256 : ℝ) := by
    have hpowers : (50036075098911269979/50000000000000000000 : ℝ)^256 ≤ (1000177391136257/1000000000000000 : ℝ)^1041 := by
      have hnat : (50036075098911269979 : ℕ)^256*1000000000000000^1041 ≤ 1000177391136257^1041*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036075098911269979 50000000000000000000 1000177391136257 1000000000000000 256 1041 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000177391136257/1000000000000000 : ℝ)) (X := (50036075098911269979/50000000000000000000 : ℝ)) (by norm_num) 1041 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2685830444661187/20000000000000000000 : ℝ) ≤ ((3069959721096357649/3071000000000000000 : ℝ)+2*(278371458217/153550000000000 : ℝ)*(2791/25000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (3069959721096357649/3071000000000000000 : ℝ)+2*(278371458217/153550000000000 : ℝ)*(2791/25000 : ℝ)=(5000330212764851/5000000000000000 : ℝ) by norm_num, show 1+2*(2685830444661187/20000000000000000000 : ℝ)=(10002685830444661187/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36075098911269979/100000000000000000000 : ℝ)+(2685830444661187/20000000000000000000 : ℝ) ≤ ((3069959721096357649/3071000000000000000 : ℝ)+(278371458217/153550000000000 : ℝ)*((2847/20000 : ℝ)+(2791/25000 : ℝ)))^(1041/256 : ℝ) := by
    rw [show (3069959721096357649/3071000000000000000 : ℝ)+(278371458217/153550000000000 : ℝ)*((2847/20000 : ℝ)+(2791/25000 : ℝ))=(1250152146055767/1250000000000000 : ℝ) by norm_num, show 1+(36075098911269979/100000000000000000000 : ℝ)+(2685830444661187/20000000000000000000 : ℝ)=(50024752125567287957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36075098911269979/100000000000000000000 : ℝ) ≤ ((3069959721096357649/3071000000000000000 : ℝ)+2*(278371458217/153550000000000 : ℝ)*(2847/20000 : ℝ))^(1041/256 : ℝ) := by
    rw [show (3069959721096357649/3071000000000000000 : ℝ)+2*(278371458217/153550000000000 : ℝ)*(2847/20000 : ℝ)=(1000177391136257/1000000000000000 : ℝ) by norm_num, show 1+2*(36075098911269979/100000000000000000000 : ℝ)=(50036075098911269979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3069959721096357649/3071000000000000000 : ℝ)*(X 1 0+X 2 0)+(278371458217/153550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3069959721096357649/3071000000000000000 : ℝ)) (alpha := (278371458217/153550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3069959721096357649/3071000000000000000 : ℝ)*(X 0 1+X 2 1)+(278371458217/153550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3069959721096357649/3071000000000000000 : ℝ)) (alpha := (278371458217/153550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3069959721096357649/3071000000000000000 : ℝ)*(X 0 2+X 1 2)+(278371458217/153550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1041/256 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3069959721096357649/3071000000000000000 : ℝ)) (alpha := (278371458217/153550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-433918453/2000000000 : ℝ)*X 0 0+(5395068643/10000000000 : ℝ)*X 0 1+(5263824773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345263117/10000000000 : ℝ)*X 1 0+(-1118095447/5000000000 : ℝ)*X 1 1+(2631912389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534526323/1000000000 : ℝ)*X 2 0+(5263824677/10000000000 : ℝ)*X 2 1+(-2236190877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436542259/1000000000 : ℝ)*X 0 0+(423696357/1000000000 : ℝ)*X 0 1+(4497762759/10000000000 : ℝ)*X 0 2+(436542259/1000000000 : ℝ)*X 1 0+(423696357/1000000000 : ℝ)*X 1 1+(4497762759/10000000000 : ℝ)*X 1 2+(436542259/1000000000 : ℝ)*X 2 0+(423696357/1000000000 : ℝ)*X 2 1+(4497762759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2169597673/10000000000 : ℝ)*X 0 0+(658020503/1250000000 : ℝ)*X 0 1+(67434101/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212481089/400000000 : ℝ)*X 1 0+(-2105287519/10000000000 : ℝ)*X 1 1+(5394728067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312027219/10000000000 : ℝ)*X 2 0+(539472807/1000000000 : ℝ)*X 2 1+(-2105287523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873086633/2000000000 : ℝ)*X 0 0+(4497088517/10000000000 : ℝ)*X 0 1+(105941009/250000000 : ℝ)*X 0 2+(873086633/2000000000 : ℝ)*X 1 0+(4497088517/10000000000 : ℝ)*X 1 1+(105941009/250000000 : ℝ)*X 1 2+(873086633/2000000000 : ℝ)*X 2 0+(4497088517/10000000000 : ℝ)*X 2 1+(105941009/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1136_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81186659457146618205458067/7677500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (981373069/50000000000000 : ℝ)*(base19) + (1862040143/100000000000000 : ℝ)*(base23) + (69965203/50000000000000 : ℝ)*(lower2) + (264886331/100000000000000 : ℝ)*(upper3) + (63301957/50000000000000 : ℝ)*(upper5) + (572696436011461/10000000000000 : ℝ)*(major0) + (572696436011461/10000000000000 : ℝ)*(major1) + (572696436011461/10000000000000 : ℝ)*(major2) + (3809727662371973/50000000000000 : ℝ)*(sp0) + (7619504431325453/100000000000000 : ℝ)*(sp1) + (952438066503931/12500000000000 : ℝ)*(sp2) + (3834392318209197/100000000000000 : ℝ)*(sp3) + (10213865529/20000000000000 : ℝ)*(sp4) + (29655461029/100000000000000 : ℝ)*(sp7) + (1917210986835113/50000000000000 : ℝ)*(f.failure) + (7619506394071591/100000000000000 : ℝ)*(f.sum) + (1190540648527/767750000000000000000000000 : ℝ)*base65 + (203535435499354811/30710000000000000000000000000000 : ℝ)*base68 + (731246395093154811/30710000000000000000000000000000 : ℝ)*base70 + (437678240511604811/30710000000000000000000000000000 : ℝ)*base72 + (1204737503777/3071000000000000000000000000 : ℝ)*base73 + (102679706337885189/30710000000000000000000000000000 : ℝ)*base75 + (218219668109294811/30710000000000000000000000000000 : ℝ)*base78 + (178233882251334811/30710000000000000000000000000000 : ℝ)*base80 + (8560111819391/3071000000000000000000000000 : ℝ)*base81 + (13695951/2500000000000000000000 : ℝ)*base89 + (13695951/2500000000000000000000 : ℝ)*base91 + (13695951/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278965822377067766201857413/76775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183195013/25000000000000 : ℝ)*(base19) + (193808717/25000000000000 : ℝ)*(base23) + (72630907/100000000000000 : ℝ)*(upper3) + (5997311/25000000000000 : ℝ)*(lower4) + (72827333/100000000000000 : ℝ)*(upper5) + (2878352377403121/50000000000000 : ℝ)*(major0) + (2878352377403121/50000000000000 : ℝ)*(major1) + (2878352377403121/50000000000000 : ℝ)*(major2) + (2433833387/12500000000000 : ℝ)*(sp1) + (4084173347/20000000000000 : ℝ)*(sp2) + (1914768770390781/25000000000000 : ℝ)*(sp4) + (306362195124639/4000000000000 : ℝ)*(sp5) + (95738173568269/1250000000000 : ℝ)*(sp6) + (3854334306931007/100000000000000 : ℝ)*(sp7) + (3854334306931007/100000000000000 : ℝ)*(f.failure) + (1914768770390781/25000000000000 : ℝ)*(f.sum) + (11368413993537/15355000000000000000000000000 : ℝ)*base66 + (973493908657712529/153550000000000000000000000000000 : ℝ)*base67 + (529417690392037471/153550000000000000000000000000000 : ℝ)*base70 + (2072287395164862529/153550000000000000000000000000000 : ℝ)*base71 + (8007308563839/7677500000000000000000000000 : ℝ)*base73 + (515896492177812529/153550000000000000000000000000000 : ℝ)*base75 + (753193728381787471/153550000000000000000000000000000 : ℝ)*base78 + (7234581911490262529/153550000000000000000000000000000 : ℝ)*base79 + (46909315986547/15355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7185289/5000000000000000000000 : ℝ)*base89 + (7185289/5000000000000000000000 : ℝ)*base91 + (7185289/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1136_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1136_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1136_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1136_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1136_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1136_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1041/256 : ℝ) ≤ p) (hpb : p ≤ (8329/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74678327/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (413/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1136_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
