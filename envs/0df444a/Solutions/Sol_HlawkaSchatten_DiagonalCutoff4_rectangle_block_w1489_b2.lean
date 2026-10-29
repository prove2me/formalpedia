-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1489_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:38.311793+00:00
-- url     : https://prove2.me/submissions/43c78b67-9bfa-480e-8b2f-2582f4012fd0

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
theorem support_rectangle_w1489_s6_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902537581/10000000000 : ℝ)*x 0 + (5436241093/10000000000 : ℝ)*x 1 + (326024297/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902537581/10000000000 : ℝ)^4475 ≤ (11627677508559/100000000000000 : ℝ)^3451 := by
    have hnat : (1902537581 : ℕ)^4475*100000000000000^3451 ≤ 11627677508559^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902537581 10000000000 11627677508559 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436241093/10000000000 : ℝ)^4475 ≤ (22684283566501/50000000000000 : ℝ)^3451 := by
    have hnat : (5436241093 : ℕ)^4475*50000000000000^3451 ≤ 22684283566501^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436241093 10000000000 22684283566501 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326024297/625000000 : ℝ)^4475 ≤ (10750938832711/25000000000000 : ℝ)^3451 := by
    have hnat : (326024297 : ℕ)^4475*25000000000000^3451 ≤ 10750938832711^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326024297 625000000 10750938832711 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902537581/10000000000 : ℝ), (5436241093/10000000000 : ℝ), (326024297/625000000 : ℝ)] ![(11627677508559/100000000000000 : ℝ), (22684283566501/50000000000000 : ℝ), (10750938832711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902537581/10000000000 : ℝ)|^4475 ≤ (11627677508559/100000000000000 : ℝ)^3451
        have hw : |(-1902537581/10000000000 : ℝ)|=(1902537581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436241093/10000000000 : ℝ)|^4475 ≤ (22684283566501/50000000000000 : ℝ)^3451
        have hw : |(5436241093/10000000000 : ℝ)|=(5436241093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326024297/625000000 : ℝ)|^4475 ≤ (10750938832711/25000000000000 : ℝ)^3451
        have hw : |(326024297/625000000 : ℝ)|=(326024297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676419143/5000000000 : ℝ)*x 0 + (-2015189123/10000000000 : ℝ)*x 1 + (5216388679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676419143/5000000000 : ℝ)^4475 ≤ (44468050259021/100000000000000 : ℝ)^3451 := by
    have hnat : (2676419143 : ℕ)^4475*100000000000000^3451 ≤ 44468050259021^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676419143 5000000000 44468050259021 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015189123/10000000000 : ℝ)^4475 ≤ (12528195187353/100000000000000 : ℝ)^3451 := by
    have hnat : (2015189123 : ℕ)^4475*100000000000000^3451 ≤ 12528195187353^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015189123 10000000000 12528195187353 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216388679/10000000000 : ℝ)^4475 ≤ (43003754550461/100000000000000 : ℝ)^3451 := by
    have hnat : (5216388679 : ℕ)^4475*100000000000000^3451 ≤ 43003754550461^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216388679 10000000000 43003754550461 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676419143/5000000000 : ℝ), (-2015189123/10000000000 : ℝ), (5216388679/10000000000 : ℝ)] ![(44468050259021/100000000000000 : ℝ), (12528195187353/100000000000000 : ℝ), (43003754550461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676419143/5000000000 : ℝ)|^4475 ≤ (44468050259021/100000000000000 : ℝ)^3451
        have hw : |(2676419143/5000000000 : ℝ)|=(2676419143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015189123/10000000000 : ℝ)|^4475 ≤ (12528195187353/100000000000000 : ℝ)^3451
        have hw : |(-2015189123/10000000000 : ℝ)|=(2015189123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216388679/10000000000 : ℝ)|^4475 ≤ (43003754550461/100000000000000 : ℝ)^3451
        have hw : |(5216388679/10000000000 : ℝ)|=(5216388679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267641913/500000000 : ℝ)*x 0 + (652048587/1250000000 : ℝ)*x 1 + (-2015189133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267641913/500000000 : ℝ)^4475 ≤ (44468049978939/100000000000000 : ℝ)^3451 := by
    have hnat : (267641913 : ℕ)^4475*100000000000000^3451 ≤ 44468049978939^3451*500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267641913 500000000 44468049978939 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652048587/1250000000 : ℝ)^4475 ≤ (21501877366097/50000000000000 : ℝ)^3451 := by
    have hnat : (652048587 : ℕ)^4475*50000000000000^3451 ≤ 21501877366097^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652048587 1250000000 21501877366097 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015189133/10000000000 : ℝ)^4475 ≤ (12528195267969/100000000000000 : ℝ)^3451 := by
    have hnat : (2015189133 : ℕ)^4475*100000000000000^3451 ≤ 12528195267969^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015189133 10000000000 12528195267969 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267641913/500000000 : ℝ), (652048587/1250000000 : ℝ), (-2015189133/10000000000 : ℝ)] ![(44468049978939/100000000000000 : ℝ), (21501877366097/50000000000000 : ℝ), (12528195267969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267641913/500000000 : ℝ)|^4475 ≤ (44468049978939/100000000000000 : ℝ)^3451
        have hw : |(267641913/500000000 : ℝ)|=(267641913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652048587/1250000000 : ℝ)|^4475 ≤ (21501877366097/50000000000000 : ℝ)^3451
        have hw : |(652048587/1250000000 : ℝ)|=(652048587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015189133/10000000000 : ℝ)|^4475 ≤ (12528195267969/100000000000000 : ℝ)^3451
        have hw : |(-2015189133/10000000000 : ℝ)|=(2015189133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070151189/2500000000 : ℝ)*x 0 + (252590761/625000000 : ℝ)*x 1 + (4531917253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070151189/2500000000 : ℝ)^4475 ≤ (16639232009841/50000000000000 : ℝ)^3451 := by
    have hnat : (1070151189 : ℕ)^4475*50000000000000^3451 ≤ 16639232009841^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070151189 2500000000 16639232009841 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252590761/625000000 : ℝ)^4475 ≤ (30887804241843/100000000000000 : ℝ)^3451 := by
    have hnat : (252590761 : ℕ)^4475*100000000000000^3451 ≤ 30887804241843^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252590761 625000000 30887804241843 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531917253/10000000000 : ℝ)^4475 ≤ (35833731723953/100000000000000 : ℝ)^3451 := by
    have hnat : (4531917253 : ℕ)^4475*100000000000000^3451 ≤ 35833731723953^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531917253 10000000000 35833731723953 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070151189/2500000000 : ℝ), (252590761/625000000 : ℝ), (4531917253/10000000000 : ℝ)] ![(16639232009841/50000000000000 : ℝ), (30887804241843/100000000000000 : ℝ), (35833731723953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070151189/2500000000 : ℝ)|^4475 ≤ (16639232009841/50000000000000 : ℝ)^3451
        have hw : |(1070151189/2500000000 : ℝ)|=(1070151189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252590761/625000000 : ℝ)|^4475 ≤ (30887804241843/100000000000000 : ℝ)^3451
        have hw : |(252590761/625000000 : ℝ)|=(252590761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531917253/10000000000 : ℝ)|^4475 ≤ (35833731723953/100000000000000 : ℝ)^3451
        have hw : |(4531917253/10000000000 : ℝ)|=(4531917253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-951283973/5000000000 : ℝ)*x 0 + (2608757621/5000000000 : ℝ)*x 1 + (543510601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951283973/5000000000 : ℝ)^4475 ≤ (11627918156487/100000000000000 : ℝ)^3451 := by
    have hnat : (951283973 : ℕ)^4475*100000000000000^3451 ≤ 11627918156487^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951283973 5000000000 11627918156487 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608757621/5000000000 : ℝ)^4475 ≤ (21507899041759/50000000000000 : ℝ)^3451 := by
    have hnat : (2608757621 : ℕ)^4475*50000000000000^3451 ≤ 21507899041759^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608757621 5000000000 21507899041759 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543510601/1000000000 : ℝ)^4475 ≤ (22678141866433/50000000000000 : ℝ)^3451 := by
    have hnat : (543510601 : ℕ)^4475*50000000000000^3451 ≤ 22678141866433^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543510601 1000000000 22678141866433 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951283973/5000000000 : ℝ), (2608757621/5000000000 : ℝ), (543510601/1000000000 : ℝ)] ![(11627918156487/100000000000000 : ℝ), (21507899041759/50000000000000 : ℝ), (22678141866433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951283973/5000000000 : ℝ)|^4475 ≤ (11627918156487/100000000000000 : ℝ)^3451
        have hw : |(-951283973/5000000000 : ℝ)|=(951283973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608757621/5000000000 : ℝ)|^4475 ≤ (21507899041759/50000000000000 : ℝ)^3451
        have hw : |(2608757621/5000000000 : ℝ)|=(2608757621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543510601/1000000000 : ℝ)|^4475 ≤ (22678141866433/50000000000000 : ℝ)^3451
        have hw : |(543510601/1000000000 : ℝ)|=(543510601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661916753/1250000000 : ℝ)*x 0 + (-71858879/400000000 : ℝ)*x 1 + (27175529/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661916753/1250000000 : ℝ)^4475 ≤ (21924790880781/50000000000000 : ℝ)^3451 := by
    have hnat : (661916753 : ℕ)^4475*50000000000000^3451 ≤ 21924790880781^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661916753 1250000000 21924790880781 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71858879/400000000 : ℝ)^4475 ≤ (1079413675759/10000000000000 : ℝ)^3451 := by
    have hnat : (71858879 : ℕ)^4475*10000000000000^3451 ≤ 1079413675759^3451*400000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71858879 400000000 1079413675759 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27175529/50000000 : ℝ)^4475 ≤ (45356281460403/100000000000000 : ℝ)^3451 := by
    have hnat : (27175529 : ℕ)^4475*100000000000000^3451 ≤ 45356281460403^3451*50000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27175529 50000000 45356281460403 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661916753/1250000000 : ℝ), (-71858879/400000000 : ℝ), (27175529/50000000 : ℝ)] ![(21924790880781/50000000000000 : ℝ), (1079413675759/10000000000000 : ℝ), (45356281460403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661916753/1250000000 : ℝ)|^4475 ≤ (21924790880781/50000000000000 : ℝ)^3451
        have hw : |(661916753/1250000000 : ℝ)|=(661916753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71858879/400000000 : ℝ)|^4475 ≤ (1079413675759/10000000000000 : ℝ)^3451
        have hw : |(-71858879/400000000 : ℝ)|=(71858879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27175529/50000000 : ℝ)|^4475 ≤ (45356281460403/100000000000000 : ℝ)^3451
        have hw : |(27175529/50000000 : ℝ)|=(27175529/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295334331/10000000000 : ℝ)*x 0 + (1087021177/2000000000 : ℝ)*x 1 + (-449117859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295334331/10000000000 : ℝ)^4475 ≤ (5481198132263/12500000000000 : ℝ)^3451 := by
    have hnat : (5295334331 : ℕ)^4475*12500000000000^3451 ≤ 5481198132263^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295334331 10000000000 5481198132263 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087021177/2000000000 : ℝ)^4475 ≤ (45356282380209/100000000000000 : ℝ)^3451 := by
    have hnat : (1087021177 : ℕ)^4475*100000000000000^3451 ≤ 45356282380209^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087021177 2000000000 45356282380209 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449117859/2500000000 : ℝ)^4475 ≤ (431765302321/4000000000000 : ℝ)^3451 := by
    have hnat : (449117859 : ℕ)^4475*4000000000000^3451 ≤ 431765302321^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449117859 2500000000 431765302321 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295334331/10000000000 : ℝ), (1087021177/2000000000 : ℝ), (-449117859/2500000000 : ℝ)] ![(5481198132263/12500000000000 : ℝ), (45356282380209/100000000000000 : ℝ), (431765302321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295334331/10000000000 : ℝ)|^4475 ≤ (5481198132263/12500000000000 : ℝ)^3451
        have hw : |(5295334331/10000000000 : ℝ)|=(5295334331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087021177/2000000000 : ℝ)|^4475 ≤ (45356282380209/100000000000000 : ℝ)^3451
        have hw : |(1087021177/2000000000 : ℝ)|=(1087021177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449117859/2500000000 : ℝ)|^4475 ≤ (431765302321/4000000000000 : ℝ)^3451
        have hw : |(-449117859/2500000000 : ℝ)|=(449117859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s6_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535083963/1250000000 : ℝ)*x 0 + (283087769/625000000 : ℝ)*x 1 + (1010995863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535083963/1250000000 : ℝ)^4475 ≤ (33279138928091/100000000000000 : ℝ)^3451 := by
    have hnat : (535083963 : ℕ)^4475*100000000000000^3451 ≤ 33279138928091^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535083963 1250000000 33279138928091 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283087769/625000000 : ℝ)^4475 ≤ (447599601891/1250000000000 : ℝ)^3451 := by
    have hnat : (283087769 : ℕ)^4475*1250000000000^3451 ≤ 447599601891^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283087769 625000000 447599601891 1250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010995863/2500000000 : ℝ)^4475 ≤ (15456446452553/50000000000000 : ℝ)^3451 := by
    have hnat : (1010995863 : ℕ)^4475*50000000000000^3451 ≤ 15456446452553^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010995863 2500000000 15456446452553 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535083963/1250000000 : ℝ), (283087769/625000000 : ℝ), (1010995863/2500000000 : ℝ)] ![(33279138928091/100000000000000 : ℝ), (447599601891/1250000000000 : ℝ), (15456446452553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535083963/1250000000 : ℝ)|^4475 ≤ (33279138928091/100000000000000 : ℝ)^3451
        have hw : |(535083963/1250000000 : ℝ)|=(535083963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283087769/625000000 : ℝ)|^4475 ≤ (447599601891/1250000000000 : ℝ)^3451
        have hw : |(283087769/625000000 : ℝ)|=(283087769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010995863/2500000000 : ℝ)|^4475 ≤ (15456446452553/50000000000000 : ℝ)^3451
        have hw : |(1010995863/2500000000 : ℝ)|=(1010995863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1353/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10823/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10823/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10823/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10823/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10823/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10823/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10823/100000 : ℝ) ^ (4473/1024 : ℝ) ≤ (3025813450496907/50000000000000000000 : ℝ) := by
    have hpowers : (10823/100000 : ℝ)^4473 ≤ (3025813450496907/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10823 : ℕ)^4473*50000000000000000000^1024 ≤ 3025813450496907^1024*100000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10823 100000 3025813450496907 50000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10823/100000 : ℝ)) (X := (3025813450496907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4473/1024 : ℝ) ≤ (14442223439136741/50000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4473 ≤ (14442223439136741/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4473*50000000000000000000^1024 ≤ 14442223439136741^1024*100000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 14442223439136741 50000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (14442223439136741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003025813450496907/25000000000000000000 : ℝ) ≤ (10000277065808499/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25003025813450496907/25000000000000000000 : ℝ)^1024 ≤ (10000277065808499/10000000000000000 : ℝ)^4473 := by
      have hnat : (25003025813450496907 : ℕ)^1024*10000000000000000^4473 ≤ 10000277065808499^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003025813450496907 25000000000000000000 10000277065808499 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000277065808499/10000000000000000 : ℝ)) (X := (25003025813450496907/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126091752305602103/3125000000000000000 : ℝ) ≤ (2000159936159343/2000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (3126091752305602103/3125000000000000000 : ℝ)^1024 ≤ (2000159936159343/2000000000000000 : ℝ)^4473 := by
      have hnat : (3126091752305602103 : ℕ)^1024*2000000000000000^4473 ≤ 2000159936159343^4473*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126091752305602103 3125000000000000000 2000159936159343 2000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000159936159343/2000000000000000 : ℝ)) (X := (3126091752305602103/3125000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014442223439136741/25000000000000000000 : ℝ) ≤ (10001322295784931/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25014442223439136741/25000000000000000000 : ℝ)^1024 ≤ (10001322295784931/10000000000000000 : ℝ)^4473 := by
      have hnat : (25014442223439136741 : ℕ)^1024*10000000000000000^4473 ≤ 10001322295784931^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014442223439136741 25000000000000000000 10001322295784931 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001322295784931/10000000000000000 : ℝ)) (X := (25014442223439136741/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3025813450496907/50000000000000000000 : ℝ) ≤ ((121223899724920437/121250000000000000 : ℝ)+2*(21775624509/19400000000000 : ℝ)*(10823/100000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (121223899724920437/121250000000000000 : ℝ)+2*(21775624509/19400000000000 : ℝ)*(10823/100000 : ℝ)=(10000277065808499/10000000000000000 : ℝ) by norm_num, show 1+2*(3025813450496907/50000000000000000000 : ℝ)=(25003025813450496907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14442223439136741/50000000000000000000 : ℝ)+(3025813450496907/50000000000000000000 : ℝ) ≤ ((121223899724920437/121250000000000000 : ℝ)+(21775624509/19400000000000 : ℝ)*((15479/100000 : ℝ)+(10823/100000 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (121223899724920437/121250000000000000 : ℝ)+(21775624509/19400000000000 : ℝ)*((15479/100000 : ℝ)+(10823/100000 : ℝ))=(2000159936159343/2000000000000000 : ℝ) by norm_num, show 1+(14442223439136741/50000000000000000000 : ℝ)+(3025813450496907/50000000000000000000 : ℝ)=(3126091752305602103/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14442223439136741/50000000000000000000 : ℝ) ≤ ((121223899724920437/121250000000000000 : ℝ)+2*(21775624509/19400000000000 : ℝ)*(15479/100000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (121223899724920437/121250000000000000 : ℝ)+2*(21775624509/19400000000000 : ℝ)*(15479/100000 : ℝ)=(10001322295784931/10000000000000000 : ℝ) by norm_num, show 1+2*(14442223439136741/50000000000000000000 : ℝ)=(25014442223439136741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (121223899724920437/121250000000000000 : ℝ)*(X 1 0+X 2 0)+(21775624509/19400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10823/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (121223899724920437/121250000000000000 : ℝ)) (alpha := (21775624509/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (121223899724920437/121250000000000000 : ℝ)*(X 0 1+X 2 1)+(21775624509/19400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10823/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (121223899724920437/121250000000000000 : ℝ)) (alpha := (21775624509/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (121223899724920437/121250000000000000 : ℝ)*(X 0 2+X 1 2)+(21775624509/19400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10823/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (121223899724920437/121250000000000000 : ℝ)) (alpha := (21775624509/19400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1902537581/10000000000 : ℝ)*X 0 0+(5436241093/10000000000 : ℝ)*X 0 1+(326024297/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676419143/5000000000 : ℝ)*X 1 0+(-2015189123/10000000000 : ℝ)*X 1 1+(5216388679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267641913/500000000 : ℝ)*X 2 0+(652048587/1250000000 : ℝ)*X 2 1+(-2015189133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1070151189/2500000000 : ℝ)*X 0 0+(252590761/625000000 : ℝ)*X 0 1+(4531917253/10000000000 : ℝ)*X 0 2+(1070151189/2500000000 : ℝ)*X 1 0+(252590761/625000000 : ℝ)*X 1 1+(4531917253/10000000000 : ℝ)*X 1 2+(1070151189/2500000000 : ℝ)*X 2 0+(252590761/625000000 : ℝ)*X 2 1+(4531917253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-951283973/5000000000 : ℝ)*X 0 0+(2608757621/5000000000 : ℝ)*X 0 1+(543510601/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661916753/1250000000 : ℝ)*X 1 0+(-71858879/400000000 : ℝ)*X 1 1+(27175529/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295334331/10000000000 : ℝ)*X 2 0+(1087021177/2000000000 : ℝ)*X 2 1+(-449117859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535083963/1250000000 : ℝ)*X 0 0+(283087769/625000000 : ℝ)*X 0 1+(1010995863/2500000000 : ℝ)*X 0 2+(535083963/1250000000 : ℝ)*X 1 0+(283087769/625000000 : ℝ)*X 1 1+(1010995863/2500000000 : ℝ)*X 1 2+(535083963/1250000000 : ℝ)*X 2 0+(283087769/625000000 : ℝ)*X 2 1+(1010995863/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16880967831757953609761151/3031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (974521381/100000000000000 : ℝ)*(base19) + (177114043/20000000000000 : ℝ)*(base23) + (35787929/100000000000000 : ℝ)*(lower2) + (65851763/50000000000000 : ℝ)*(upper3) + (34250847/50000000000000 : ℝ)*(upper5) + (1646857734943647/50000000000000 : ℝ)*(major0) + (1646857734943647/50000000000000 : ℝ)*(major1) + (1646857734943647/50000000000000 : ℝ)*(major2) + (4548522323772943/100000000000000 : ℝ)*(sp0) + (4548535123441791/100000000000000 : ℝ)*(sp1) + (4548535212392957/100000000000000 : ℝ)*(sp2) + (2038887450605921/100000000000000 : ℝ)*(sp3) + (13774190229/100000000000000 : ℝ)*(sp4) + (7205572849/100000000000000 : ℝ)*(sp7) + (203889465617877/10000000000000 : ℝ)*(f.failure) + (4548536097963171/100000000000000 : ℝ)*(f.sum) + (32352772897/30312500000000000000000000 : ℝ)*base66 + (71319489905180011/6062500000000000000000000000000 : ℝ)*base68 + (98367757290555011/6062500000000000000000000000000 : ℝ)*base70 + (53689993857242511/6062500000000000000000000000000 : ℝ)*base72 + (273844287077/121250000000000000000000000 : ℝ)*base73 + (83208904434992511/6062500000000000000000000000000 : ℝ)*base76 + (62340724208367511/6062500000000000000000000000000 : ℝ)*base78 + (74057902694867511/6062500000000000000000000000000 : ℝ)*base80 + (656463506523/485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2744967/1000000000000000000000 : ℝ)*base89 + (2744967/1000000000000000000000 : ℝ)*base91 + (2744967/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (539751552967678210157439/60625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85139077/4000000000000 : ℝ)*(base19) + (1407508431/50000000000000 : ℝ)*(base23) + (486295253/100000000000000 : ℝ)*(lower1) + (53192417/50000000000000 : ℝ)*(upper2) + (388821081/100000000000000 : ℝ)*(upper3) + (180684333/100000000000000 : ℝ)*(upper5) + (33279082924167/1000000000000 : ℝ)*(major0) + (33279082924167/1000000000000 : ℝ)*(major1) + (33279082924167/1000000000000 : ℝ)*(major2) + (20184949427/100000000000000 : ℝ)*(sp2) + (4595755394614193/100000000000000 : ℝ)*(sp4) + (4595753266137267/100000000000000 : ℝ)*(sp5) + (143616637332747/3125000000000 : ℝ)*(sp6) + (1030030446724289/50000000000000 : ℝ)*(sp7) + (1030030446724289/50000000000000 : ℝ)*(f.failure) + (4595755394614193/100000000000000 : ℝ)*(f.sum) + (46396711829/12125000000000000000000000 : ℝ)*base65 + (481592293837229/121250000000000000000000000000 : ℝ)*base67 + (1433959904467229/121250000000000000000000000000 : ℝ)*base69 + (1610357055719729/121250000000000000000000000000 : ℝ)*base71 + (185810786509/97000000000000000000000000 : ℝ)*base74 + (2469162253229729/121250000000000000000000000000 : ℝ)*base75 + (1765605939354729/121250000000000000000000000000 : ℝ)*base77 + (580924837559729/121250000000000000000000000000 : ℝ)*base79 + (424372289107/97000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (67930581/5000000000000000000000 : ℝ)*base90 + (67930581/5000000000000000000000 : ℝ)*base92 + (67930581/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1353/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1489_box_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-842350041/5000000000 : ℝ)*x 0 + (2702662703/5000000000 : ℝ)*x 1 + (337832829/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842350041/5000000000 : ℝ)^4475 ≤ (9931436284913/100000000000000 : ℝ)^3451 := by
    have hnat : (842350041 : ℕ)^4475*100000000000000^3451 ≤ 9931436284913^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842350041 5000000000 9931436284913 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702662703/5000000000 : ℝ)^4475 ≤ (11258570653847/25000000000000 : ℝ)^3451 := by
    have hnat : (2702662703 : ℕ)^4475*25000000000000^3451 ≤ 11258570653847^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702662703 5000000000 11258570653847 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337832829/625000000 : ℝ)^4475 ≤ (45034281081273/100000000000000 : ℝ)^3451 := by
    have hnat : (337832829 : ℕ)^4475*100000000000000^3451 ≤ 45034281081273^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337832829 625000000 45034281081273 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-842350041/5000000000 : ℝ), (2702662703/5000000000 : ℝ), (337832829/625000000 : ℝ)] ![(9931436284913/100000000000000 : ℝ), (11258570653847/25000000000000 : ℝ), (45034281081273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-842350041/5000000000 : ℝ)|^4475 ≤ (9931436284913/100000000000000 : ℝ)^3451
        have hw : |(-842350041/5000000000 : ℝ)|=(842350041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702662703/5000000000 : ℝ)|^4475 ≤ (11258570653847/25000000000000 : ℝ)^3451
        have hw : |(2702662703/5000000000 : ℝ)|=(2702662703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337832829/625000000 : ℝ)|^4475 ≤ (45034281081273/100000000000000 : ℝ)^3451
        have hw : |(337832829/625000000 : ℝ)|=(337832829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270412837/10000000000 : ℝ)*x 0 + (-1871658947/10000000000 : ℝ)*x 1 + (2702662667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270412837/10000000000 : ℝ)^4475 ≤ (21791083548509/50000000000000 : ℝ)^3451 := by
    have hnat : (5270412837 : ℕ)^4475*50000000000000^3451 ≤ 21791083548509^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270412837 10000000000 21791083548509 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1871658947/10000000000 : ℝ)^4475 ≤ (11383551049621/100000000000000 : ℝ)^3451 := by
    have hnat : (1871658947 : ℕ)^4475*100000000000000^3451 ≤ 11383551049621^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871658947 10000000000 11383551049621 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702662667/5000000000 : ℝ)^4475 ≤ (45034281837527/100000000000000 : ℝ)^3451 := by
    have hnat : (2702662667 : ℕ)^4475*100000000000000^3451 ≤ 45034281837527^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702662667 5000000000 45034281837527 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270412837/10000000000 : ℝ), (-1871658947/10000000000 : ℝ), (2702662667/5000000000 : ℝ)] ![(21791083548509/50000000000000 : ℝ), (11383551049621/100000000000000 : ℝ), (45034281837527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270412837/10000000000 : ℝ)|^4475 ≤ (21791083548509/50000000000000 : ℝ)^3451
        have hw : |(5270412837/10000000000 : ℝ)|=(5270412837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1871658947/10000000000 : ℝ)|^4475 ≤ (11383551049621/100000000000000 : ℝ)^3451
        have hw : |(-1871658947/10000000000 : ℝ)|=(1871658947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702662667/5000000000 : ℝ)|^4475 ≤ (45034281837527/100000000000000 : ℝ)^3451
        have hw : |(2702662667/5000000000 : ℝ)|=(2702662667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635206403/5000000000 : ℝ)*x 0 + (5405325387/10000000000 : ℝ)*x 1 + (-1871658917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635206403/5000000000 : ℝ)^4475 ≤ (680971355697/1562500000000 : ℝ)^3451 := by
    have hnat : (2635206403 : ℕ)^4475*1562500000000^3451 ≤ 680971355697^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635206403 5000000000 680971355697 1562500000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405325387/10000000000 : ℝ)^4475 ≤ (45034282410119/100000000000000 : ℝ)^3451 := by
    have hnat : (5405325387 : ℕ)^4475*100000000000000^3451 ≤ 45034282410119^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405325387 10000000000 45034282410119 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871658917/10000000000 : ℝ)^4475 ≤ (5691775406509/50000000000000 : ℝ)^3451 := by
    have hnat : (1871658917 : ℕ)^4475*50000000000000^3451 ≤ 5691775406509^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871658917 10000000000 5691775406509 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635206403/5000000000 : ℝ), (5405325387/10000000000 : ℝ), (-1871658917/10000000000 : ℝ)] ![(680971355697/1562500000000 : ℝ), (45034282410119/100000000000000 : ℝ), (5691775406509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635206403/5000000000 : ℝ)|^4475 ≤ (680971355697/1562500000000 : ℝ)^3451
        have hw : |(2635206403/5000000000 : ℝ)|=(2635206403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405325387/10000000000 : ℝ)|^4475 ≤ (45034282410119/100000000000000 : ℝ)^3451
        have hw : |(5405325387/10000000000 : ℝ)|=(5405325387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871658917/10000000000 : ℝ)|^4475 ≤ (5691775406509/50000000000000 : ℝ)^3451
        have hw : |(-1871658917/10000000000 : ℝ)|=(1871658917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (896951863/2000000000 : ℝ)*x 0 + (167426531/400000000 : ℝ)*x 1 + (837132653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896951863/2000000000 : ℝ)^4475 ≤ (7070192335571/20000000000000 : ℝ)^3451 := by
    have hnat : (896951863 : ℕ)^4475*20000000000000^3451 ≤ 7070192335571^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896951863 2000000000 7070192335571 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167426531/400000000 : ℝ)^4475 ≤ (2020282450403/6250000000000 : ℝ)^3451 := by
    have hnat : (167426531 : ℕ)^4475*6250000000000^3451 ≤ 2020282450403^3451*400000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167426531 400000000 2020282450403 6250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837132653/2000000000 : ℝ)^4475 ≤ (16162259553153/50000000000000 : ℝ)^3451 := by
    have hnat : (837132653 : ℕ)^4475*50000000000000^3451 ≤ 16162259553153^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837132653 2000000000 16162259553153 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896951863/2000000000 : ℝ), (167426531/400000000 : ℝ), (837132653/2000000000 : ℝ)] ![(7070192335571/20000000000000 : ℝ), (2020282450403/6250000000000 : ℝ), (16162259553153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896951863/2000000000 : ℝ)|^4475 ≤ (7070192335571/20000000000000 : ℝ)^3451
        have hw : |(896951863/2000000000 : ℝ)|=(896951863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167426531/400000000 : ℝ)|^4475 ≤ (2020282450403/6250000000000 : ℝ)^3451
        have hw : |(167426531/400000000 : ℝ)|=(167426531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(837132653/2000000000 : ℝ)|^4475 ≤ (16162259553153/50000000000000 : ℝ)^3451
        have hw : |(837132653/2000000000 : ℝ)|=(837132653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-531458471/2500000000 : ℝ)*x 0 + (262140083/500000000 : ℝ)*x 1 + (5242802239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531458471/2500000000 : ℝ)^4475 ≤ (13427342578849/100000000000000 : ℝ)^3451 := by
    have hnat : (531458471 : ℕ)^4475*100000000000000^3451 ≤ 13427342578849^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531458471 2500000000 13427342578849 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262140083/500000000 : ℝ)^4475 ≤ (2164316280371/5000000000000 : ℝ)^3451 := by
    have hnat : (262140083 : ℕ)^4475*5000000000000^3451 ≤ 2164316280371^3451*500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262140083 500000000 2164316280371 5000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242802239/10000000000 : ℝ)^4475 ≤ (4328633180631/10000000000000 : ℝ)^3451 := by
    have hnat : (5242802239 : ℕ)^4475*10000000000000^3451 ≤ 4328633180631^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242802239 10000000000 4328633180631 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531458471/2500000000 : ℝ), (262140083/500000000 : ℝ), (5242802239/10000000000 : ℝ)] ![(13427342578849/100000000000000 : ℝ), (2164316280371/5000000000000 : ℝ), (4328633180631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531458471/2500000000 : ℝ)|^4475 ≤ (13427342578849/100000000000000 : ℝ)^3451
        have hw : |(-531458471/2500000000 : ℝ)|=(531458471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262140083/500000000 : ℝ)|^4475 ≤ (2164316280371/5000000000000 : ℝ)^3451
        have hw : |(262140083/500000000 : ℝ)|=(262140083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242802239/10000000000 : ℝ)|^4475 ≤ (4328633180631/10000000000000 : ℝ)^3451
        have hw : |(5242802239/10000000000 : ℝ)|=(5242802239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691884047/5000000000 : ℝ)*x 0 + (-484583099/2500000000 : ℝ)*x 1 + (5242802179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691884047/5000000000 : ℝ)^4475 ≤ (44801523442131/100000000000000 : ℝ)^3451 := by
    have hnat : (2691884047 : ℕ)^4475*100000000000000^3451 ≤ 44801523442131^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691884047 5000000000 44801523442131 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484583099/2500000000 : ℝ)^4475 ≤ (1191214537753/10000000000000 : ℝ)^3451 := by
    have hnat : (484583099 : ℕ)^4475*10000000000000^3451 ≤ 1191214537753^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484583099 2500000000 1191214537753 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242802179/10000000000 : ℝ)^4475 ≤ (21643165581969/50000000000000 : ℝ)^3451 := by
    have hnat : (5242802179 : ℕ)^4475*50000000000000^3451 ≤ 21643165581969^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242802179 10000000000 21643165581969 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691884047/5000000000 : ℝ), (-484583099/2500000000 : ℝ), (5242802179/10000000000 : ℝ)] ![(44801523442131/100000000000000 : ℝ), (1191214537753/10000000000000 : ℝ), (21643165581969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691884047/5000000000 : ℝ)|^4475 ≤ (44801523442131/100000000000000 : ℝ)^3451
        have hw : |(2691884047/5000000000 : ℝ)|=(2691884047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484583099/2500000000 : ℝ)|^4475 ≤ (1191214537753/10000000000000 : ℝ)^3451
        have hw : |(-484583099/2500000000 : ℝ)|=(484583099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242802179/10000000000 : ℝ)|^4475 ≤ (21643165581969/50000000000000 : ℝ)^3451
        have hw : |(5242802179/10000000000 : ℝ)|=(5242802179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383768061/10000000000 : ℝ)*x 0 + (2621400957/5000000000 : ℝ)*x 1 + (-484583199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383768061/10000000000 : ℝ)^4475 ≤ (22400761543017/50000000000000 : ℝ)^3451 := by
    have hnat : (5383768061 : ℕ)^4475*50000000000000^3451 ≤ 22400761543017^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383768061 10000000000 22400761543017 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621400957/5000000000 : ℝ)^4475 ≤ (8657265665359/20000000000000 : ℝ)^3451 := by
    have hnat : (2621400957 : ℕ)^4475*20000000000000^3451 ≤ 8657265665359^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621400957 5000000000 8657265665359 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484583199/2500000000 : ℝ)^4475 ≤ (5956074282587/50000000000000 : ℝ)^3451 := by
    have hnat : (484583199 : ℕ)^4475*50000000000000^3451 ≤ 5956074282587^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484583199 2500000000 5956074282587 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383768061/10000000000 : ℝ), (2621400957/5000000000 : ℝ), (-484583199/2500000000 : ℝ)] ![(22400761543017/50000000000000 : ℝ), (8657265665359/20000000000000 : ℝ), (5956074282587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383768061/10000000000 : ℝ)|^4475 ≤ (22400761543017/50000000000000 : ℝ)^3451
        have hw : |(5383768061/10000000000 : ℝ)|=(5383768061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621400957/5000000000 : ℝ)|^4475 ≤ (8657265665359/20000000000000 : ℝ)^3451
        have hw : |(2621400957/5000000000 : ℝ)|=(2621400957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-484583199/2500000000 : ℝ)|^4475 ≤ (5956074282587/50000000000000 : ℝ)^3451
        have hw : |(-484583199/2500000000 : ℝ)|=(484583199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2037072663/5000000000 : ℝ)*x 0 + (439083289/1000000000 : ℝ)*x 1 + (87816657/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037072663/5000000000 : ℝ)^4475 ≤ (3901524925829/12500000000000 : ℝ)^3451 := by
    have hnat : (2037072663 : ℕ)^4475*12500000000000^3451 ≤ 3901524925829^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037072663 5000000000 3901524925829 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439083289/1000000000 : ℝ)^4475 ≤ (34393900489603/100000000000000 : ℝ)^3451 := by
    have hnat : (439083289 : ℕ)^4475*100000000000000^3451 ≤ 34393900489603^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439083289 1000000000 34393900489603 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87816657/200000000 : ℝ)^4475 ≤ (34393900083307/100000000000000 : ℝ)^3451 := by
    have hnat : (87816657 : ℕ)^4475*100000000000000^3451 ≤ 34393900083307^3451*200000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87816657 200000000 34393900083307 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2037072663/5000000000 : ℝ), (439083289/1000000000 : ℝ), (87816657/200000000 : ℝ)] ![(3901524925829/12500000000000 : ℝ), (34393900489603/100000000000000 : ℝ), (34393900083307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2037072663/5000000000 : ℝ)|^4475 ≤ (3901524925829/12500000000000 : ℝ)^3451
        have hw : |(2037072663/5000000000 : ℝ)|=(2037072663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(439083289/1000000000 : ℝ)|^4475 ≤ (34393900489603/100000000000000 : ℝ)^3451
        have hw : |(439083289/1000000000 : ℝ)|=(439083289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87816657/200000000 : ℝ)|^4475 ≤ (34393900083307/100000000000000 : ℝ)^3451
        have hw : |(87816657/200000000 : ℝ)|=(87816657/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_8 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032740771/10000000000 : ℝ)*x 0 + (5129201077/10000000000 : ℝ)*x 1 + (1356461479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032740771/10000000000 : ℝ)^4475 ≤ (12669871867287/100000000000000 : ℝ)^3451 := by
    have hnat : (2032740771 : ℕ)^4475*100000000000000^3451 ≤ 12669871867287^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032740771 10000000000 12669871867287 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129201077/10000000000 : ℝ)^4475 ≤ (10518506215321/25000000000000 : ℝ)^3451 := by
    have hnat : (5129201077 : ℕ)^4475*25000000000000^3451 ≤ 10518506215321^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129201077 10000000000 10518506215321 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356461479/2500000000 : ℝ)^4475 ≤ (45256103258531/100000000000000 : ℝ)^3451 := by
    have hnat : (1356461479 : ℕ)^4475*100000000000000^3451 ≤ 45256103258531^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356461479 2500000000 45256103258531 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032740771/10000000000 : ℝ), (5129201077/10000000000 : ℝ), (1356461479/2500000000 : ℝ)] ![(12669871867287/100000000000000 : ℝ), (10518506215321/25000000000000 : ℝ), (45256103258531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032740771/10000000000 : ℝ)|^4475 ≤ (12669871867287/100000000000000 : ℝ)^3451
        have hw : |(-2032740771/10000000000 : ℝ)|=(2032740771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129201077/10000000000 : ℝ)|^4475 ≤ (10518506215321/25000000000000 : ℝ)^3451
        have hw : |(5129201077/10000000000 : ℝ)|=(5129201077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356461479/2500000000 : ℝ)|^4475 ≤ (45256103258531/100000000000000 : ℝ)^3451
        have hw : |(1356461479/2500000000 : ℝ)|=(1356461479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_9 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314023333/2500000000 : ℝ)*x 0 + (-3725977/20000000 : ℝ)*x 1 + (2712922867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314023333/2500000000 : ℝ)^4475 ≤ (43428682406551/100000000000000 : ℝ)^3451 := by
    have hnat : (1314023333 : ℕ)^4475*100000000000000^3451 ≤ 43428682406551^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314023333 2500000000 43428682406551 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3725977/20000000 : ℝ)^4475 ≤ (11315216285547/100000000000000 : ℝ)^3451 := by
    have hnat : (3725977 : ℕ)^4475*100000000000000^3451 ≤ 11315216285547^3451*20000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725977 20000000 11315216285547 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712922867/5000000000 : ℝ)^4475 ≤ (45256101290059/100000000000000 : ℝ)^3451 := by
    have hnat : (2712922867 : ℕ)^4475*100000000000000^3451 ≤ 45256101290059^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712922867 5000000000 45256101290059 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314023333/2500000000 : ℝ), (-3725977/20000000 : ℝ), (2712922867/5000000000 : ℝ)] ![(43428682406551/100000000000000 : ℝ), (11315216285547/100000000000000 : ℝ), (45256101290059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314023333/2500000000 : ℝ)|^4475 ≤ (43428682406551/100000000000000 : ℝ)^3451
        have hw : |(1314023333/2500000000 : ℝ)|=(1314023333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3725977/20000000 : ℝ)|^4475 ≤ (11315216285547/100000000000000 : ℝ)^3451
        have hw : |(-3725977/20000000 : ℝ)|=(3725977/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712922867/5000000000 : ℝ)|^4475 ≤ (45256101290059/100000000000000 : ℝ)^3451
        have hw : |(2712922867/5000000000 : ℝ)|=(2712922867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_10 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314023221/2500000000 : ℝ)*x 0 + (339115389/625000000 : ℝ)*x 1 + (-1862988437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314023221/2500000000 : ℝ)^4475 ≤ (5428584700821/12500000000000 : ℝ)^3451 := by
    have hnat : (1314023221 : ℕ)^4475*12500000000000^3451 ≤ 5428584700821^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314023221 2500000000 5428584700821 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339115389/625000000 : ℝ)^4475 ≤ (45256106589791/100000000000000 : ℝ)^3451 := by
    have hnat : (339115389 : ℕ)^4475*100000000000000^3451 ≤ 45256106589791^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339115389 625000000 45256106589791 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862988437/10000000000 : ℝ)^4475 ≤ (2828803947341/25000000000000 : ℝ)^3451 := by
    have hnat : (1862988437 : ℕ)^4475*25000000000000^3451 ≤ 2828803947341^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862988437 10000000000 2828803947341 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314023221/2500000000 : ℝ), (339115389/625000000 : ℝ), (-1862988437/10000000000 : ℝ)] ![(5428584700821/12500000000000 : ℝ), (45256106589791/100000000000000 : ℝ), (2828803947341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314023221/2500000000 : ℝ)|^4475 ≤ (5428584700821/12500000000000 : ℝ)^3451
        have hw : |(1314023221/2500000000 : ℝ)|=(1314023221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339115389/625000000 : ℝ)|^4475 ≤ (45256106589791/100000000000000 : ℝ)^3451
        have hw : |(339115389/625000000 : ℝ)|=(339115389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1862988437/10000000000 : ℝ)|^4475 ≤ (2828803947341/25000000000000 : ℝ)^3451
        have hw : |(-1862988437/10000000000 : ℝ)|=(1862988437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_11 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2267724911/5000000000 : ℝ)*x 0 + (2079863341/5000000000 : ℝ)*x 1 + (2079863109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2267724911/5000000000 : ℝ)^4475 ≤ (17934977970729/50000000000000 : ℝ)^3451 := by
    have hnat : (2267724911 : ℕ)^4475*50000000000000^3451 ≤ 17934977970729^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267724911 5000000000 17934977970729 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079863341/5000000000 : ℝ)^4475 ≤ (6413004868549/20000000000000 : ℝ)^3451 := by
    have hnat : (2079863341 : ℕ)^4475*20000000000000^3451 ≤ 6413004868549^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079863341 5000000000 6413004868549 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079863109/5000000000 : ℝ)^4475 ≤ (32065019704723/100000000000000 : ℝ)^3451 := by
    have hnat : (2079863109 : ℕ)^4475*100000000000000^3451 ≤ 32065019704723^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079863109 5000000000 32065019704723 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2267724911/5000000000 : ℝ), (2079863341/5000000000 : ℝ), (2079863109/5000000000 : ℝ)] ![(17934977970729/50000000000000 : ℝ), (6413004868549/20000000000000 : ℝ), (32065019704723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2267724911/5000000000 : ℝ)|^4475 ≤ (17934977970729/50000000000000 : ℝ)^3451
        have hw : |(2267724911/5000000000 : ℝ)|=(2267724911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079863341/5000000000 : ℝ)|^4475 ≤ (6413004868549/20000000000000 : ℝ)^3451
        have hw : |(2079863341/5000000000 : ℝ)|=(2079863341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2079863109/5000000000 : ℝ)|^4475 ≤ (32065019704723/100000000000000 : ℝ)^3451
        have hw : |(2079863109/5000000000 : ℝ)|=(2079863109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_12 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1777871397/10000000000 : ℝ)*x 0 + (5515192173/10000000000 : ℝ)*x 1 + (1306949467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777871397/10000000000 : ℝ)^4475 ≤ (2662358841281/25000000000000 : ℝ)^3451 := by
    have hnat : (1777871397 : ℕ)^4475*25000000000000^3451 ≤ 2662358841281^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777871397 10000000000 2662358841281 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515192173/10000000000 : ℝ)^4475 ≤ (11556201093271/25000000000000 : ℝ)^3451 := by
    have hnat : (5515192173 : ℕ)^4475*25000000000000^3451 ≤ 11556201093271^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515192173 10000000000 11556201093271 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306949467/2500000000 : ℝ)^4475 ≤ (4312576024949/10000000000000 : ℝ)^3451 := by
    have hnat : (1306949467 : ℕ)^4475*10000000000000^3451 ≤ 4312576024949^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306949467 2500000000 4312576024949 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1777871397/10000000000 : ℝ), (5515192173/10000000000 : ℝ), (1306949467/2500000000 : ℝ)] ![(2662358841281/25000000000000 : ℝ), (11556201093271/25000000000000 : ℝ), (4312576024949/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1777871397/10000000000 : ℝ)|^4475 ≤ (2662358841281/25000000000000 : ℝ)^3451
        have hw : |(-1777871397/10000000000 : ℝ)|=(1777871397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515192173/10000000000 : ℝ)|^4475 ≤ (11556201093271/25000000000000 : ℝ)^3451
        have hw : |(5515192173/10000000000 : ℝ)|=(5515192173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306949467/2500000000 : ℝ)|^4475 ≤ (4312576024949/10000000000000 : ℝ)^3451
        have hw : |(1306949467/2500000000 : ℝ)|=(1306949467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_13 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394232139/10000000000 : ℝ)*x 0 + (-1944305761/10000000000 : ℝ)*x 1 + (653474717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394232139/10000000000 : ℝ)^4475 ≤ (22457235816073/50000000000000 : ℝ)^3451 := by
    have hnat : (5394232139 : ℕ)^4475*50000000000000^3451 ≤ 22457235816073^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394232139 10000000000 22457235816073 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944305761/10000000000 : ℝ)^4475 ≤ (11959769527723/100000000000000 : ℝ)^3451 := by
    have hnat : (1944305761 : ℕ)^4475*100000000000000^3451 ≤ 11959769527723^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944305761 10000000000 11959769527723 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653474717/1250000000 : ℝ)^4475 ≤ (43125758837473/100000000000000 : ℝ)^3451 := by
    have hnat : (653474717 : ℕ)^4475*100000000000000^3451 ≤ 43125758837473^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653474717 1250000000 43125758837473 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394232139/10000000000 : ℝ), (-1944305761/10000000000 : ℝ), (653474717/1250000000 : ℝ)] ![(22457235816073/50000000000000 : ℝ), (11959769527723/100000000000000 : ℝ), (43125758837473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394232139/10000000000 : ℝ)|^4475 ≤ (22457235816073/50000000000000 : ℝ)^3451
        have hw : |(5394232139/10000000000 : ℝ)|=(5394232139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944305761/10000000000 : ℝ)|^4475 ≤ (11959769527723/100000000000000 : ℝ)^3451
        have hw : |(-1944305761/10000000000 : ℝ)|=(1944305761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653474717/1250000000 : ℝ)|^4475 ≤ (43125758837473/100000000000000 : ℝ)^3451
        have hw : |(653474717/1250000000 : ℝ)|=(653474717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_14 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697116047/5000000000 : ℝ)*x 0 + (2613898931/5000000000 : ℝ)*x 1 + (-486076413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697116047/5000000000 : ℝ)^4475 ≤ (44914471146279/100000000000000 : ℝ)^3451 := by
    have hnat : (2697116047 : ℕ)^4475*100000000000000^3451 ≤ 44914471146279^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697116047 5000000000 44914471146279 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613898931/5000000000 : ℝ)^4475 ≤ (10781440046327/25000000000000 : ℝ)^3451 := by
    have hnat : (2613898931 : ℕ)^4475*25000000000000^3451 ≤ 10781440046327^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613898931 5000000000 10781440046327 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486076413/2500000000 : ℝ)^4475 ≤ (1494971082287/12500000000000 : ℝ)^3451 := by
    have hnat : (486076413 : ℕ)^4475*12500000000000^3451 ≤ 1494971082287^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486076413 2500000000 1494971082287 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697116047/5000000000 : ℝ), (2613898931/5000000000 : ℝ), (-486076413/2500000000 : ℝ)] ![(44914471146279/100000000000000 : ℝ), (10781440046327/25000000000000 : ℝ), (1494971082287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697116047/5000000000 : ℝ)|^4475 ≤ (44914471146279/100000000000000 : ℝ)^3451
        have hw : |(2697116047/5000000000 : ℝ)|=(2697116047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613898931/5000000000 : ℝ)|^4475 ≤ (10781440046327/25000000000000 : ℝ)^3451
        have hw : |(2613898931/5000000000 : ℝ)|=(2613898931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-486076413/2500000000 : ℝ)|^4475 ≤ (1494971082287/12500000000000 : ℝ)^3451
        have hw : |(-486076413/2500000000 : ℝ)|=(486076413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_box_15 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4035377683/10000000000 : ℝ)*x 0 + (2204876123/5000000000 : ℝ)*x 1 + (2204875851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035377683/10000000000 : ℝ)^4475 ≤ (6165523223279/20000000000000 : ℝ)^3451 := by
    have hnat : (4035377683 : ℕ)^4475*20000000000000^3451 ≤ 6165523223279^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035377683 10000000000 6165523223279 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204876123/5000000000 : ℝ)^4475 ≤ (17293097351273/50000000000000 : ℝ)^3451 := by
    have hnat : (2204876123 : ℕ)^4475*50000000000000^3451 ≤ 17293097351273^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204876123 5000000000 17293097351273 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204875851/5000000000 : ℝ)^4475 ≤ (17293094584933/50000000000000 : ℝ)^3451 := by
    have hnat : (2204875851 : ℕ)^4475*50000000000000^3451 ≤ 17293094584933^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204875851 5000000000 17293094584933 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035377683/10000000000 : ℝ), (2204876123/5000000000 : ℝ), (2204875851/5000000000 : ℝ)] ![(6165523223279/20000000000000 : ℝ), (17293097351273/50000000000000 : ℝ), (17293094584933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035377683/10000000000 : ℝ)|^4475 ≤ (6165523223279/20000000000000 : ℝ)^3451
        have hw : |(4035377683/10000000000 : ℝ)|=(4035377683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2204876123/5000000000 : ℝ)|^4475 ≤ (17293097351273/50000000000000 : ℝ)^3451
        have hw : |(2204876123/5000000000 : ℝ)|=(2204876123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204875851/5000000000 : ℝ)|^4475 ≤ (17293094584933/50000000000000 : ℝ)^3451
        have hw : |(2204875851/5000000000 : ℝ)|=(2204875851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1353/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(1991/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1463/2500 : ℝ) ∧ (20017/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85853/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1353/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1353/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1353/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1353/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1353/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1353/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1353/12500 : ℝ) ^ (4473/1024 : ℝ) ≤ (3027034859196593/50000000000000000000 : ℝ) := by
    have hpowers : (1353/12500 : ℝ)^4473 ≤ (3027034859196593/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1353 : ℕ)^4473*50000000000000000000^1024 ≤ 3027034859196593^1024*12500^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1353 12500 3027034859196593 50000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1353/12500 : ℝ)) (X := (3027034859196593/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4473/1024 : ℝ) ≤ (28876296592319909/100000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4473 ≤ (28876296592319909/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4473*100000000000000000000^1024 ≤ 28876296592319909^1024*50000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 28876296592319909 100000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (28876296592319909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003027034859196593/25000000000000000000 : ℝ) ≤ (1250034647205559/1250000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25003027034859196593/25000000000000000000 : ℝ)^1024 ≤ (1250034647205559/1250000000000000 : ℝ)^4473 := by
      have hnat : (25003027034859196593 : ℕ)^1024*1250000000000000^4473 ≤ 1250034647205559^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003027034859196593 25000000000000000000 1250034647205559 1250000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250034647205559/1250000000000000 : ℝ)) (X := (25003027034859196593/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006986073262142619/20000000000000000000 : ℝ) ≤ (10000799550171317/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (20006986073262142619/20000000000000000000 : ℝ)^1024 ≤ (10000799550171317/10000000000000000 : ℝ)^4473 := by
      have hnat : (20006986073262142619 : ℕ)^1024*10000000000000000^4473 ≤ 10000799550171317^4473*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006986073262142619 20000000000000000000 10000799550171317 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000799550171317/10000000000000000 : ℝ)) (X := (20006986073262142619/20000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028876296592319909/50000000000000000000 : ℝ) ≤ (5000660961349081/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (50028876296592319909/50000000000000000000 : ℝ)^1024 ≤ (5000660961349081/5000000000000000 : ℝ)^4473 := by
      have hnat : (50028876296592319909 : ℕ)^1024*5000000000000000^4473 ≤ 5000660961349081^4473*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028876296592319909 50000000000000000000 5000660961349081 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000660961349081/5000000000000000 : ℝ)) (X := (50028876296592319909/50000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3027034859196593/50000000000000000000 : ℝ) ≤ ((55925458731125279/55937500000000000 : ℝ)+2*(8036500413/7160000000000 : ℝ)*(1353/12500 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (55925458731125279/55937500000000000 : ℝ)+2*(8036500413/7160000000000 : ℝ)*(1353/12500 : ℝ)=(1250034647205559/1250000000000000 : ℝ) by norm_num, show 1+2*(3027034859196593/50000000000000000000 : ℝ)=(25003027034859196593/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28876296592319909/100000000000000000000 : ℝ)+(3027034859196593/50000000000000000000 : ℝ) ≤ ((55925458731125279/55937500000000000 : ℝ)+(8036500413/7160000000000 : ℝ)*((7739/50000 : ℝ)+(1353/12500 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (55925458731125279/55937500000000000 : ℝ)+(8036500413/7160000000000 : ℝ)*((7739/50000 : ℝ)+(1353/12500 : ℝ))=(10000799550171317/10000000000000000 : ℝ) by norm_num, show 1+(28876296592319909/100000000000000000000 : ℝ)+(3027034859196593/50000000000000000000 : ℝ)=(20006986073262142619/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28876296592319909/100000000000000000000 : ℝ) ≤ ((55925458731125279/55937500000000000 : ℝ)+2*(8036500413/7160000000000 : ℝ)*(7739/50000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (55925458731125279/55937500000000000 : ℝ)+2*(8036500413/7160000000000 : ℝ)*(7739/50000 : ℝ)=(5000660961349081/5000000000000000 : ℝ) by norm_num, show 1+2*(28876296592319909/100000000000000000000 : ℝ)=(50028876296592319909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55925458731125279/55937500000000000 : ℝ)*(X 1 0+X 2 0)+(8036500413/7160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (1353/12500 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (55925458731125279/55937500000000000 : ℝ)) (alpha := (8036500413/7160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55925458731125279/55937500000000000 : ℝ)*(X 0 1+X 2 1)+(8036500413/7160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (1353/12500 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (55925458731125279/55937500000000000 : ℝ)) (alpha := (8036500413/7160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55925458731125279/55937500000000000 : ℝ)*(X 0 2+X 1 2)+(8036500413/7160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (1353/12500 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (55925458731125279/55937500000000000 : ℝ)) (alpha := (8036500413/7160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-842350041/5000000000 : ℝ)*X 0 0+(2702662703/5000000000 : ℝ)*X 0 1+(337832829/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270412837/10000000000 : ℝ)*X 1 0+(-1871658947/10000000000 : ℝ)*X 1 1+(2702662667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635206403/5000000000 : ℝ)*X 2 0+(5405325387/10000000000 : ℝ)*X 2 1+(-1871658917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((896951863/2000000000 : ℝ)*X 0 0+(167426531/400000000 : ℝ)*X 0 1+(837132653/2000000000 : ℝ)*X 0 2+(896951863/2000000000 : ℝ)*X 1 0+(167426531/400000000 : ℝ)*X 1 1+(837132653/2000000000 : ℝ)*X 1 2+(896951863/2000000000 : ℝ)*X 2 0+(167426531/400000000 : ℝ)*X 2 1+(837132653/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-531458471/2500000000 : ℝ)*X 0 0+(262140083/500000000 : ℝ)*X 0 1+(5242802239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2691884047/5000000000 : ℝ)*X 1 0+(-484583099/2500000000 : ℝ)*X 1 1+(5242802179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5383768061/10000000000 : ℝ)*X 2 0+(2621400957/5000000000 : ℝ)*X 2 1+(-484583199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2037072663/5000000000 : ℝ)*X 0 0+(439083289/1000000000 : ℝ)*X 0 1+(87816657/200000000 : ℝ)*X 0 2+(2037072663/5000000000 : ℝ)*X 1 0+(439083289/1000000000 : ℝ)*X 1 1+(87816657/200000000 : ℝ)*X 1 2+(2037072663/5000000000 : ℝ)*X 2 0+(439083289/1000000000 : ℝ)*X 2 1+(87816657/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2032740771/10000000000 : ℝ)*X 0 0+(5129201077/10000000000 : ℝ)*X 0 1+(1356461479/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314023333/2500000000 : ℝ)*X 1 0+(-3725977/20000000 : ℝ)*X 1 1+(2712922867/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314023221/2500000000 : ℝ)*X 2 0+(339115389/625000000 : ℝ)*X 2 1+(-1862988437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2267724911/5000000000 : ℝ)*X 0 0+(2079863341/5000000000 : ℝ)*X 0 1+(2079863109/5000000000 : ℝ)*X 0 2+(2267724911/5000000000 : ℝ)*X 1 0+(2079863341/5000000000 : ℝ)*X 1 1+(2079863109/5000000000 : ℝ)*X 1 2+(2267724911/5000000000 : ℝ)*X 2 0+(2079863341/5000000000 : ℝ)*X 2 1+(2079863109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1777871397/10000000000 : ℝ)*X 0 0+(5515192173/10000000000 : ℝ)*X 0 1+(1306949467/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5394232139/10000000000 : ℝ)*X 1 0+(-1944305761/10000000000 : ℝ)*X 1 1+(653474717/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697116047/5000000000 : ℝ)*X 2 0+(2613898931/5000000000 : ℝ)*X 2 1+(-486076413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4035377683/10000000000 : ℝ)*X 0 0+(2204876123/5000000000 : ℝ)*X 0 1+(2204875851/5000000000 : ℝ)*X 0 2+(4035377683/10000000000 : ℝ)*X 1 0+(2204876123/5000000000 : ℝ)*X 1 1+(2204875851/5000000000 : ℝ)*X 1 2+(4035377683/10000000000 : ℝ)*X 2 0+(2204876123/5000000000 : ℝ)*X 2 1+(2204875851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1991/3125 : ℝ) ≤ (-57019649356968980442441417/89500000000000000000000000 : ℝ) := by norm_num
    linear_combination (85527467/100000000000000 : ℝ)*(upper1) + (64482787/50000000000000 : ℝ)*(lower4) + (27365241/100000000000000 : ℝ)*(upper5) + (109459344184387/5000000000000 : ℝ)*(major0) + (109459344184387/5000000000000 : ℝ)*(major1) + (109459344184387/5000000000000 : ℝ)*(major2) + (2930304127/50000000000000 : ℝ)*(sp2) + (26644559/1562500000000 : ℝ)*(sp3) + (761110443521877/25000000000000 : ℝ)*(sp4) + (1522198473433771/50000000000000 : ℝ)*(sp5) + (304444124451499/10000000000000 : ℝ)*(sp6) + (1355161325476049/100000000000000 : ℝ)*(sp7) + (5331035737/100000000000000 : ℝ)*(sp12) + (25079127851/50000000000000 : ℝ)*(sp13) + (54206521229113/4000000000000 : ℝ)*(f.failure) + (761111776280811/25000000000000 : ℝ)*(f.sum) + (330654617523/179000000000000000000000000 : ℝ)*base65 + (70964419074163/69921875000000000000000000000 : ℝ)*base68 + (8308139425196429/559375000000000000000000000000 : ℝ)*base70 + (1645913795309821/559375000000000000000000000000 : ℝ)*base71 + (336358819193/89500000000000000000000000 : ℝ)*base73 + (1484841536440179/559375000000000000000000000000 : ℝ)*base76 + (2956851850772321/559375000000000000000000000000 : ℝ)*base77 + (792525014647321/559375000000000000000000000000 : ℝ)*base79 + (108660331941/89500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (650323/400000000000000000000 : ℝ)*base89 + (650323/400000000000000000000 : ℝ)*base91 + (650323/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1463/2500 : ℝ) ≤ (818396496982962383677092179589/1398437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5048523/100000000000000 : ℝ)*(upper0) + (6518727/100000000000000 : ℝ)*(upper3) + (395747/6250000000000 : ℝ)*(upper4) + (1131933031992953/50000000000000 : ℝ)*(major0) + (1131933031992953/50000000000000 : ℝ)*(major1) + (1131933031992953/50000000000000 : ℝ)*(major2) + (1553416023071051/50000000000000 : ℝ)*(sp0) + (194177036793247/6250000000000 : ℝ)*(sp1) + (1553415590226187/50000000000000 : ℝ)*(sp2) + (1401390953644197/100000000000000 : ℝ)*(sp3) + (771168331/100000000000000 : ℝ)*(sp5) + (544851977/25000000000000 : ℝ)*(sp6) + (160911/39062500000 : ℝ)*(sp7) + (656859091/50000000000000 : ℝ)*(sp8) + (1401391365576357/100000000000000 : ℝ)*(f.failure) + (3106833359860283/100000000000000 : ℝ)*(f.sum) + (308354766449/89500000000000000000000000 : ℝ)*base65 + (9350146885697851/5593750000000000000000000000000 : ℝ)*base68 + (22606528013072851/5593750000000000000000000000000 : ℝ)*base70 + (43544827732802149/5593750000000000000000000000000 : ℝ)*base71 + (509741825089/44750000000000000000000000 : ℝ)*base74 + (15740478083399/5593750000000000000000000000000 : ℝ)*base75 + (69368324856989649/5593750000000000000000000000000 : ℝ)*base77 + (21079689642552149/5593750000000000000000000000000 : ℝ)*base79 + (14346025447/11187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (71234953/10000000000000000000000 : ℝ)*base90 + (71234953/10000000000000000000000 : ℝ)*base92 + (71234953/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20017/25000 : ℝ) ≤ (279934840387821049908486367311/349609375000000000000000000000 : ℝ) := by norm_num
    linear_combination (19804501/25000000000000 : ℝ)*(upper1) + (772781/1562500000000 : ℝ)*(upper2) + (1981719/6250000000000 : ℝ)*(lower5) + (1230192957115921/50000000000000 : ℝ)*(major0) + (1230192957115921/50000000000000 : ℝ)*(major1) + (1230192957115921/50000000000000 : ℝ)*(major2) + (10835376477/25000000000000 : ℝ)*(sp1) + (114265615689/100000000000000 : ℝ)*(sp2) + (3757474069/20000000000000 : ℝ)*(sp3) + (3882866517/100000000000000 : ℝ)*(sp4) + (134841419403153/4000000000000 : ℝ)*(sp8) + (1685498013219717/50000000000000 : ℝ)*(sp9) + (842731275582413/25000000000000 : ℝ)*(sp10) + (304604684786821/20000000000000 : ℝ)*(sp11) + (30460844226089/2000000000000 : ℝ)*(f.failure) + (1685519683972671/50000000000000 : ℝ)*(f.sum) + (140093338699/35800000000000000000000000 : ℝ)*base65 + (19487107444074543/5593750000000000000000000000000 : ℝ)*base67 + (39010305466199543/5593750000000000000000000000000 : ℝ)*base69 + (41814527907168293/5593750000000000000000000000000 : ℝ)*base71 + (110619943681/89500000000000000000000000 : ℝ)*base73 + (29102165649480793/5593750000000000000000000000000 : ℝ)*base75 + (90504124262730793/5593750000000000000000000000000 : ℝ)*base77 + (56748653933637043/5593750000000000000000000000000 : ℝ)*base79 + (253324389911/179000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (77219/200000000000000000000 : ℝ)*base89 + (77219/200000000000000000000 : ℝ)*base91 + (77219/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-85853/100000 : ℝ) ≤ (-2401124013501105928976683195653/2796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2394919/25000000000000 : ℝ)*(lower0) + (5276523/50000000000000 : ℝ)*(upper1) + (5656617/10000000000000 : ℝ)*(lower2) + (13637119/20000000000000 : ℝ)*(upper3) + (866491/100000000000000 : ℝ)*(upper5) + (624726141789857/25000000000000 : ℝ)*(major0) + (624726141789857/25000000000000 : ℝ)*(major1) + (624726141789857/25000000000000 : ℝ)*(major2) + (69021204033/100000000000000 : ℝ)*(sp5) + (2733294057/20000000000000 : ℝ)*(sp7) + (3479539633400519/100000000000000 : ℝ)*(sp12) + (1739735306098243/50000000000000 : ℝ)*(sp13) + (3479539633400519/100000000000000 : ℝ)*(sp14) + (154687258246743/10000000000000 : ℝ)*(sp15) + (309377249787543/20000000000000 : ℝ)*(f.failure) + (3479539633400519/100000000000000 : ℝ)*(f.sum) + (81800809179/179000000000000000000000000 : ℝ)*base65 + (733816929325443/349609375000000000000000000000 : ℝ)*base68 + (1108750542650419/2796875000000000000000000000000 : ℝ)*base70 + (6889241324931669/2796875000000000000000000000000 : ℝ)*base72 + (533636840759/89500000000000000000000000 : ℝ)*base73 + (172033993356693/349609375000000000000000000000 : ℝ)*base76 + (10951618719775419/2796875000000000000000000000000 : ℝ)*base78 + (7400769037443331/2796875000000000000000000000000 : ℝ)*base79 + (83746966661/44750000000000000000000000 : ℝ)*base81 + (61853/2000000000000000000000 : ℝ)*base89 + (61853/2000000000000000000000 : ℝ)*base91 + (61853/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1489_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1353/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1991/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(1463/2500 : ℝ) else (20017/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85853/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1489_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1489_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1991/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(1463/2500 : ℝ) else (20017/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85853/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1489_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1489_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1991/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(1463/2500 : ℝ) else (20017/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85853/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1489_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
