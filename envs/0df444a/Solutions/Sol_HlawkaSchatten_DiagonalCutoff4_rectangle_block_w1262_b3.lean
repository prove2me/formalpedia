-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:55:00.58526+00:00
-- url     : https://prove2.me/submissions/2371bef2-22b2-417e-9ca1-3f5cb0dca444

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
theorem support_rectangle_w1262_box_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987719803/10000000000 : ℝ)*x 0 + (83977141/156250000 : ℝ)*x 1 + (4198857/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987719803/10000000000 : ℝ)^8455 ≤ (474388460009/4000000000000 : ℝ)^6407 := by
    have hnat : (1987719803 : ℕ)^8455*4000000000000^6407 ≤ 474388460009^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987719803 10000000000 474388460009 4000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83977141/156250000 : ℝ)^8455 ≤ (22035072294483/50000000000000 : ℝ)^6407 := by
    have hnat : (83977141 : ℕ)^8455*50000000000000^6407 ≤ 22035072294483^6407*156250000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83977141 156250000 22035072294483 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4198857/7812500 : ℝ)^8455 ≤ (44070143896431/100000000000000 : ℝ)^6407 := by
    have hnat : (4198857 : ℕ)^8455*100000000000000^6407 ≤ 44070143896431^6407*7812500^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198857 7812500 44070143896431 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987719803/10000000000 : ℝ), (83977141/156250000 : ℝ), (4198857/7812500 : ℝ)] ![(474388460009/4000000000000 : ℝ), (22035072294483/50000000000000 : ℝ), (44070143896431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987719803/10000000000 : ℝ)|^8455 ≤ (474388460009/4000000000000 : ℝ)^6407
        have hw : |(-1987719803/10000000000 : ℝ)|=(1987719803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(83977141/156250000 : ℝ)|^8455 ≤ (22035072294483/50000000000000 : ℝ)^6407
        have hw : |(83977141/156250000 : ℝ)|=(83977141/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4198857/7812500 : ℝ)|^8455 ≤ (44070143896431/100000000000000 : ℝ)^6407
        have hw : |(4198857/7812500 : ℝ)|=(4198857/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296930493/10000000000 : ℝ)*x 0 + (-2093243319/10000000000 : ℝ)*x 1 + (5374537037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296930493/10000000000 : ℝ)^8455 ≤ (5404039823883/12500000000000 : ℝ)^6407 := by
    have hnat : (5296930493 : ℕ)^8455*12500000000000^6407 ≤ 5404039823883^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296930493 10000000000 5404039823883 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093243319/10000000000 : ℝ)^8455 ≤ (3174384166051/25000000000000 : ℝ)^6407 := by
    have hnat : (2093243319 : ℕ)^8455*25000000000000^6407 ≤ 3174384166051^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093243319 10000000000 3174384166051 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374537037/10000000000 : ℝ)^8455 ≤ (22035072364819/50000000000000 : ℝ)^6407 := by
    have hnat : (5374537037 : ℕ)^8455*50000000000000^6407 ≤ 22035072364819^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374537037 10000000000 22035072364819 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296930493/10000000000 : ℝ), (-2093243319/10000000000 : ℝ), (5374537037/10000000000 : ℝ)] ![(5404039823883/12500000000000 : ℝ), (3174384166051/25000000000000 : ℝ), (22035072364819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296930493/10000000000 : ℝ)|^8455 ≤ (5404039823883/12500000000000 : ℝ)^6407
        have hw : |(5296930493/10000000000 : ℝ)|=(5296930493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093243319/10000000000 : ℝ)|^8455 ≤ (3174384166051/25000000000000 : ℝ)^6407
        have hw : |(-2093243319/10000000000 : ℝ)|=(2093243319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374537037/10000000000 : ℝ)|^8455 ≤ (22035072364819/50000000000000 : ℝ)^6407
        have hw : |(5374537037/10000000000 : ℝ)|=(5374537037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296930227/10000000000 : ℝ)*x 0 + (1343634269/2500000000 : ℝ)*x 1 + (-261655453/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296930227/10000000000 : ℝ)^8455 ≤ (43232315726063/100000000000000 : ℝ)^6407 := by
    have hnat : (5296930227 : ℕ)^8455*100000000000000^6407 ≤ 43232315726063^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296930227 10000000000 43232315726063 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343634269/2500000000 : ℝ)^8455 ≤ (11017536287913/25000000000000 : ℝ)^6407 := by
    have hnat : (1343634269 : ℕ)^8455*25000000000000^6407 ≤ 11017536287913^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343634269 2500000000 11017536287913 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261655453/1250000000 : ℝ)^8455 ≤ (6348769552857/50000000000000 : ℝ)^6407 := by
    have hnat : (261655453 : ℕ)^8455*50000000000000^6407 ≤ 6348769552857^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261655453 1250000000 6348769552857 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296930227/10000000000 : ℝ), (1343634269/2500000000 : ℝ), (-261655453/1250000000 : ℝ)] ![(43232315726063/100000000000000 : ℝ), (11017536287913/25000000000000 : ℝ), (6348769552857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296930227/10000000000 : ℝ)|^8455 ≤ (43232315726063/100000000000000 : ℝ)^6407
        have hw : |(5296930227/10000000000 : ℝ)|=(5296930227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343634269/2500000000 : ℝ)|^8455 ≤ (11017536287913/25000000000000 : ℝ)^6407
        have hw : |(1343634269/2500000000 : ℝ)|=(1343634269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261655453/1250000000 : ℝ)|^8455 ≤ (6348769552857/50000000000000 : ℝ)^6407
        have hw : |(-261655453/1250000000 : ℝ)|=(261655453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4454370587/10000000000 : ℝ)*x 0 + (429690327/1000000000 : ℝ)*x 1 + (4296902999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4454370587/10000000000 : ℝ)^8455 ≤ (17198507945459/50000000000000 : ℝ)^6407 := by
    have hnat : (4454370587 : ℕ)^8455*50000000000000^6407 ≤ 17198507945459^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454370587 10000000000 17198507945459 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429690327/1000000000 : ℝ)^8455 ≤ (4100186676907/12500000000000 : ℝ)^6407 := by
    have hnat : (429690327 : ℕ)^8455*12500000000000^6407 ≤ 4100186676907^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429690327 1000000000 4100186676907 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4296902999/10000000000 : ℝ)^8455 ≤ (16400745342617/50000000000000 : ℝ)^6407 := by
    have hnat : (4296902999 : ℕ)^8455*50000000000000^6407 ≤ 16400745342617^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296902999 10000000000 16400745342617 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4454370587/10000000000 : ℝ), (429690327/1000000000 : ℝ), (4296902999/10000000000 : ℝ)] ![(17198507945459/50000000000000 : ℝ), (4100186676907/12500000000000 : ℝ), (16400745342617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4454370587/10000000000 : ℝ)|^8455 ≤ (17198507945459/50000000000000 : ℝ)^6407
        have hw : |(4454370587/10000000000 : ℝ)|=(4454370587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(429690327/1000000000 : ℝ)|^8455 ≤ (4100186676907/12500000000000 : ℝ)^6407
        have hw : |(429690327/1000000000 : ℝ)|=(429690327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4296902999/10000000000 : ℝ)|^8455 ≤ (16400745342617/50000000000000 : ℝ)^6407
        have hw : |(4296902999/10000000000 : ℝ)|=(4296902999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-558811113/2500000000 : ℝ)*x 0 + (330155353/625000000 : ℝ)*x 1 + (5282485643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558811113/2500000000 : ℝ)^8455 ≤ (13846388768251/100000000000000 : ℝ)^6407 := by
    have hnat : (558811113 : ℕ)^8455*100000000000000^6407 ≤ 13846388768251^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558811113 2500000000 13846388768251 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330155353/625000000 : ℝ)^8455 ≤ (861536112653/2000000000000 : ℝ)^6407 := by
    have hnat : (330155353 : ℕ)^8455*2000000000000^6407 ≤ 861536112653^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330155353 625000000 861536112653 2000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282485643/10000000000 : ℝ)^8455 ≤ (10769201394711/25000000000000 : ℝ)^6407 := by
    have hnat : (5282485643 : ℕ)^8455*25000000000000^6407 ≤ 10769201394711^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282485643 10000000000 10769201394711 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-558811113/2500000000 : ℝ), (330155353/625000000 : ℝ), (5282485643/10000000000 : ℝ)] ![(13846388768251/100000000000000 : ℝ), (861536112653/2000000000000 : ℝ), (10769201394711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-558811113/2500000000 : ℝ)|^8455 ≤ (13846388768251/100000000000000 : ℝ)^6407
        have hw : |(-558811113/2500000000 : ℝ)|=(558811113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330155353/625000000 : ℝ)|^8455 ≤ (861536112653/2000000000000 : ℝ)^6407
        have hw : |(330155353/625000000 : ℝ)|=(330155353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282485643/10000000000 : ℝ)|^8455 ≤ (10769201394711/25000000000000 : ℝ)^6407
        have hw : |(5282485643/10000000000 : ℝ)|=(5282485643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2680895837/5000000000 : ℝ)*x 0 + (-21297911/100000000 : ℝ)*x 1 + (5282485671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680895837/5000000000 : ℝ)^8455 ≤ (2745767567133/6250000000000 : ℝ)^6407 := by
    have hnat : (2680895837 : ℕ)^8455*6250000000000^6407 ≤ 2745767567133^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680895837 5000000000 2745767567133 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21297911/100000000 : ℝ)^8455 ≤ (6495456519089/50000000000000 : ℝ)^6407 := by
    have hnat : (21297911 : ℕ)^8455*50000000000000^6407 ≤ 6495456519089^6407*100000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21297911 100000000 6495456519089 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282485671/10000000000 : ℝ)^8455 ≤ (269230036751/625000000000 : ℝ)^6407 := by
    have hnat : (5282485671 : ℕ)^8455*625000000000^6407 ≤ 269230036751^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282485671 10000000000 269230036751 625000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680895837/5000000000 : ℝ), (-21297911/100000000 : ℝ), (5282485671/10000000000 : ℝ)] ![(2745767567133/6250000000000 : ℝ), (6495456519089/50000000000000 : ℝ), (269230036751/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680895837/5000000000 : ℝ)|^8455 ≤ (2745767567133/6250000000000 : ℝ)^6407
        have hw : |(2680895837/5000000000 : ℝ)|=(2680895837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21297911/100000000 : ℝ)|^8455 ≤ (6495456519089/50000000000000 : ℝ)^6407
        have hw : |(-21297911/100000000 : ℝ)|=(21297911/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282485671/10000000000 : ℝ)|^8455 ≤ (269230036751/625000000000 : ℝ)^6407
        have hw : |(5282485671/10000000000 : ℝ)|=(5282485671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2680895847/5000000000 : ℝ)*x 0 + (528248563/1000000000 : ℝ)*x 1 + (-1064895563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680895847/5000000000 : ℝ)^8455 ≤ (43932281290381/100000000000000 : ℝ)^6407 := by
    have hnat : (2680895847 : ℕ)^8455*100000000000000^6407 ≤ 43932281290381^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680895847 5000000000 43932281290381 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528248563/1000000000 : ℝ)^8455 ≤ (43076805438947/100000000000000 : ℝ)^6407 := by
    have hnat : (528248563 : ℕ)^8455*100000000000000^6407 ≤ 43076805438947^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528248563 1000000000 43076805438947 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064895563/5000000000 : ℝ)^8455 ≤ (12990913247461/100000000000000 : ℝ)^6407 := by
    have hnat : (1064895563 : ℕ)^8455*100000000000000^6407 ≤ 12990913247461^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064895563 5000000000 12990913247461 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680895847/5000000000 : ℝ), (528248563/1000000000 : ℝ), (-1064895563/5000000000 : ℝ)] ![(43932281290381/100000000000000 : ℝ), (43076805438947/100000000000000 : ℝ), (12990913247461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680895847/5000000000 : ℝ)|^8455 ≤ (43932281290381/100000000000000 : ℝ)^6407
        have hw : |(2680895847/5000000000 : ℝ)|=(2680895847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528248563/1000000000 : ℝ)|^8455 ≤ (43076805438947/100000000000000 : ℝ)^6407
        have hw : |(528248563/1000000000 : ℝ)|=(528248563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064895563/5000000000 : ℝ)|^8455 ≤ (12990913247461/100000000000000 : ℝ)^6407
        have hw : |(-1064895563/5000000000 : ℝ)|=(1064895563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2120649077/5000000000 : ℝ)*x 0 + (2201709661/5000000000 : ℝ)*x 1 + (2201709731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120649077/5000000000 : ℝ)^8455 ≤ (16121247960977/50000000000000 : ℝ)^6407 := by
    have hnat : (2120649077 : ℕ)^8455*50000000000000^6407 ≤ 16121247960977^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120649077 5000000000 16121247960977 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201709661/5000000000 : ℝ)^8455 ≤ (8469687830027/25000000000000 : ℝ)^6407 := by
    have hnat : (2201709661 : ℕ)^8455*25000000000000^6407 ≤ 8469687830027^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201709661 5000000000 8469687830027 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201709731/5000000000 : ℝ)^8455 ≤ (16939376370767/50000000000000 : ℝ)^6407 := by
    have hnat : (2201709731 : ℕ)^8455*50000000000000^6407 ≤ 16939376370767^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201709731 5000000000 16939376370767 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120649077/5000000000 : ℝ), (2201709661/5000000000 : ℝ), (2201709731/5000000000 : ℝ)] ![(16121247960977/50000000000000 : ℝ), (8469687830027/25000000000000 : ℝ), (16939376370767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120649077/5000000000 : ℝ)|^8455 ≤ (16121247960977/50000000000000 : ℝ)^6407
        have hw : |(2120649077/5000000000 : ℝ)|=(2120649077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201709661/5000000000 : ℝ)|^8455 ≤ (8469687830027/25000000000000 : ℝ)^6407
        have hw : |(2201709661/5000000000 : ℝ)|=(2201709661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2201709731/5000000000 : ℝ)|^8455 ≤ (16939376370767/50000000000000 : ℝ)^6407
        have hw : |(2201709731/5000000000 : ℝ)|=(2201709731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_8 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091677873/5000000000 : ℝ)*x 0 + (652457501/1250000000 : ℝ)*x 1 + (1346037441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091677873/5000000000 : ℝ)^8455 ≤ (6711898844297/50000000000000 : ℝ)^6407 := by
    have hnat : (1091677873 : ℕ)^8455*50000000000000^6407 ≤ 6711898844297^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091677873 5000000000 6711898844297 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652457501/1250000000 : ℝ)^8455 ≤ (42402009747619/100000000000000 : ℝ)^6407 := by
    have hnat : (652457501 : ℕ)^8455*100000000000000^6407 ≤ 42402009747619^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652457501 1250000000 42402009747619 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346037441/2500000000 : ℝ)^8455 ≤ (8834838510241/20000000000000 : ℝ)^6407 := by
    have hnat : (1346037441 : ℕ)^8455*20000000000000^6407 ≤ 8834838510241^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346037441 2500000000 8834838510241 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091677873/5000000000 : ℝ), (652457501/1250000000 : ℝ), (1346037441/2500000000 : ℝ)] ![(6711898844297/50000000000000 : ℝ), (42402009747619/100000000000000 : ℝ), (8834838510241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091677873/5000000000 : ℝ)|^8455 ≤ (6711898844297/50000000000000 : ℝ)^6407
        have hw : |(-1091677873/5000000000 : ℝ)|=(1091677873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652457501/1250000000 : ℝ)|^8455 ≤ (42402009747619/100000000000000 : ℝ)^6407
        have hw : |(652457501/1250000000 : ℝ)|=(652457501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346037441/2500000000 : ℝ)|^8455 ≤ (8834838510241/20000000000000 : ℝ)^6407
        have hw : |(1346037441/2500000000 : ℝ)|=(1346037441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_9 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290153871/10000000000 : ℝ)*x 0 + (-65292503/312500000 : ℝ)*x 1 + (336509371/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290153871/10000000000 : ℝ)^8455 ≤ (43159344689419/100000000000000 : ℝ)^6407 := by
    have hnat : (5290153871 : ℕ)^8455*100000000000000^6407 ≤ 43159344689419^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290153871 10000000000 43159344689419 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65292503/312500000 : ℝ)^8455 ≤ (633323043841/5000000000000 : ℝ)^6407 := by
    have hnat : (65292503 : ℕ)^8455*5000000000000^6407 ≤ 633323043841^6407*312500000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65292503 312500000 633323043841 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336509371/625000000 : ℝ)^8455 ≤ (44174194413459/100000000000000 : ℝ)^6407 := by
    have hnat : (336509371 : ℕ)^8455*100000000000000^6407 ≤ 44174194413459^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336509371 625000000 44174194413459 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290153871/10000000000 : ℝ), (-65292503/312500000 : ℝ), (336509371/625000000 : ℝ)] ![(43159344689419/100000000000000 : ℝ), (633323043841/5000000000000 : ℝ), (44174194413459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290153871/10000000000 : ℝ)|^8455 ≤ (43159344689419/100000000000000 : ℝ)^6407
        have hw : |(5290153871/10000000000 : ℝ)|=(5290153871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65292503/312500000 : ℝ)|^8455 ≤ (633323043841/5000000000000 : ℝ)^6407
        have hw : |(-65292503/312500000 : ℝ)|=(65292503/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336509371/625000000 : ℝ)|^8455 ≤ (44174194413459/100000000000000 : ℝ)^6407
        have hw : |(336509371/625000000 : ℝ)|=(336509371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_10 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322538513/2500000000 : ℝ)*x 0 + (5384149757/10000000000 : ℝ)*x 1 + (-65292503/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322538513/2500000000 : ℝ)^8455 ≤ (8631869327623/20000000000000 : ℝ)^6407 := by
    have hnat : (1322538513 : ℕ)^8455*20000000000000^6407 ≤ 8631869327623^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322538513 2500000000 8631869327623 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384149757/10000000000 : ℝ)^8455 ≤ (5521774059427/12500000000000 : ℝ)^6407 := by
    have hnat : (5384149757 : ℕ)^8455*12500000000000^6407 ≤ 5521774059427^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384149757 10000000000 5521774059427 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65292503/312500000 : ℝ)^8455 ≤ (633323043841/5000000000000 : ℝ)^6407 := by
    have hnat : (65292503 : ℕ)^8455*5000000000000^6407 ≤ 633323043841^6407*312500000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65292503 312500000 633323043841 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322538513/2500000000 : ℝ), (5384149757/10000000000 : ℝ), (-65292503/312500000 : ℝ)] ![(8631869327623/20000000000000 : ℝ), (5521774059427/12500000000000 : ℝ), (633323043841/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322538513/2500000000 : ℝ)|^8455 ≤ (8631869327623/20000000000000 : ℝ)^6407
        have hw : |(1322538513/2500000000 : ℝ)|=(1322538513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384149757/10000000000 : ℝ)|^8455 ≤ (5521774059427/12500000000000 : ℝ)^6407
        have hw : |(5384149757/10000000000 : ℝ)|=(5384149757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65292503/312500000 : ℝ)|^8455 ≤ (633323043841/5000000000000 : ℝ)^6407
        have hw : |(-65292503/312500000 : ℝ)|=(65292503/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_11 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4476349179/10000000000 : ℝ)*x 0 + (4285773363/10000000000 : ℝ)*x 1 + (267860829/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476349179/10000000000 : ℝ)^8455 ≤ (34621164033927/100000000000000 : ℝ)^6407 := by
    have hnat : (4476349179 : ℕ)^8455*100000000000000^6407 ≤ 34621164033927^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476349179 10000000000 34621164033927 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4285773363/10000000000 : ℝ)^8455 ≤ (16344709235651/50000000000000 : ℝ)^6407 := by
    have hnat : (4285773363 : ℕ)^8455*50000000000000^6407 ≤ 16344709235651^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285773363 10000000000 16344709235651 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267860829/625000000 : ℝ)^8455 ≤ (16344708737407/50000000000000 : ℝ)^6407 := by
    have hnat : (267860829 : ℕ)^8455*50000000000000^6407 ≤ 16344708737407^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267860829 625000000 16344708737407 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476349179/10000000000 : ℝ), (4285773363/10000000000 : ℝ), (267860829/625000000 : ℝ)] ![(34621164033927/100000000000000 : ℝ), (16344709235651/50000000000000 : ℝ), (16344708737407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476349179/10000000000 : ℝ)|^8455 ≤ (34621164033927/100000000000000 : ℝ)^6407
        have hw : |(4476349179/10000000000 : ℝ)|=(4476349179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4285773363/10000000000 : ℝ)|^8455 ≤ (16344709235651/50000000000000 : ℝ)^6407
        have hw : |(4285773363/10000000000 : ℝ)|=(4285773363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(267860829/625000000 : ℝ)|^8455 ≤ (16344708737407/50000000000000 : ℝ)^6407
        have hw : |(267860829/625000000 : ℝ)|=(267860829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_12 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039857053/10000000000 : ℝ)*x 0 + (2718083609/5000000000 : ℝ)*x 1 + (2637199741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039857053/10000000000 : ℝ)^8455 ≤ (1533991801719/12500000000000 : ℝ)^6407 := by
    have hnat : (2039857053 : ℕ)^8455*12500000000000^6407 ≤ 1533991801719^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039857053 10000000000 1533991801719 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718083609/5000000000 : ℝ)^8455 ≤ (22369128083211/50000000000000 : ℝ)^6407 := by
    have hnat : (2718083609 : ℕ)^8455*50000000000000^6407 ≤ 22369128083211^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718083609 5000000000 22369128083211 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637199741/5000000000 : ℝ)^8455 ≤ (42989809408347/100000000000000 : ℝ)^6407 := by
    have hnat : (2637199741 : ℕ)^8455*100000000000000^6407 ≤ 42989809408347^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637199741 5000000000 42989809408347 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039857053/10000000000 : ℝ), (2718083609/5000000000 : ℝ), (2637199741/5000000000 : ℝ)] ![(1533991801719/12500000000000 : ℝ), (22369128083211/50000000000000 : ℝ), (42989809408347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039857053/10000000000 : ℝ)|^8455 ≤ (1533991801719/12500000000000 : ℝ)^6407
        have hw : |(-2039857053/10000000000 : ℝ)|=(2039857053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718083609/5000000000 : ℝ)|^8455 ≤ (22369128083211/50000000000000 : ℝ)^6407
        have hw : |(2718083609/5000000000 : ℝ)|=(2718083609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637199741/5000000000 : ℝ)|^8455 ≤ (42989809408347/100000000000000 : ℝ)^6407
        have hw : |(2637199741/5000000000 : ℝ)|=(2637199741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_13 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683743909/5000000000 : ℝ)*x 0 + (-2132945723/10000000000 : ℝ)*x 1 + (329649949/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683743909/5000000000 : ℝ)^8455 ≤ (21996941010009/50000000000000 : ℝ)^6407 := by
    have hnat : (2683743909 : ℕ)^8455*50000000000000^6407 ≤ 21996941010009^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683743909 5000000000 21996941010009 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132945723/10000000000 : ℝ)^8455 ≤ (13016311755553/100000000000000 : ℝ)^6407 := by
    have hnat : (2132945723 : ℕ)^8455*100000000000000^6407 ≤ 13016311755553^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132945723 10000000000 13016311755553 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329649949/625000000 : ℝ)^8455 ≤ (8597961240611/20000000000000 : ℝ)^6407 := by
    have hnat : (329649949 : ℕ)^8455*20000000000000^6407 ≤ 8597961240611^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329649949 625000000 8597961240611 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683743909/5000000000 : ℝ), (-2132945723/10000000000 : ℝ), (329649949/625000000 : ℝ)] ![(21996941010009/50000000000000 : ℝ), (13016311755553/100000000000000 : ℝ), (8597961240611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683743909/5000000000 : ℝ)|^8455 ≤ (21996941010009/50000000000000 : ℝ)^6407
        have hw : |(2683743909/5000000000 : ℝ)|=(2683743909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132945723/10000000000 : ℝ)|^8455 ≤ (13016311755553/100000000000000 : ℝ)^6407
        have hw : |(-2132945723/10000000000 : ℝ)|=(2132945723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329649949/625000000 : ℝ)|^8455 ≤ (8597961240611/20000000000000 : ℝ)^6407
        have hw : |(329649949/625000000 : ℝ)|=(329649949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_14 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367487699/10000000000 : ℝ)*x 0 + (659299909/1250000000 : ℝ)*x 1 + (-1066472883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367487699/10000000000 : ℝ)^8455 ≤ (21996940366437/50000000000000 : ℝ)^6407 := by
    have hnat : (5367487699 : ℕ)^8455*50000000000000^6407 ≤ 21996940366437^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367487699 10000000000 21996940366437 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659299909/1250000000 : ℝ)^8455 ≤ (2686862946849/6250000000000 : ℝ)^6407 := by
    have hnat : (659299909 : ℕ)^8455*6250000000000^6407 ≤ 2686862946849^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659299909 1250000000 2686862946849 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066472883/5000000000 : ℝ)^8455 ≤ (13016312101839/100000000000000 : ℝ)^6407 := by
    have hnat : (1066472883 : ℕ)^8455*100000000000000^6407 ≤ 13016312101839^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066472883 5000000000 13016312101839 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367487699/10000000000 : ℝ), (659299909/1250000000 : ℝ), (-1066472883/5000000000 : ℝ)] ![(21996940366437/50000000000000 : ℝ), (2686862946849/6250000000000 : ℝ), (13016312101839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367487699/10000000000 : ℝ)|^8455 ≤ (21996940366437/50000000000000 : ℝ)^6407
        have hw : |(5367487699/10000000000 : ℝ)|=(5367487699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659299909/1250000000 : ℝ)|^8455 ≤ (2686862946849/6250000000000 : ℝ)^6407
        have hw : |(659299909/1250000000 : ℝ)|=(659299909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066472883/5000000000 : ℝ)|^8455 ≤ (13016312101839/100000000000000 : ℝ)^6407
        have hw : |(-1066472883/5000000000 : ℝ)|=(1066472883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_box_15 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (844469781/2000000000 : ℝ)*x 0 + (882554229/2000000000 : ℝ)*x 1 + (4412771301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844469781/2000000000 : ℝ)^8455 ≤ (8013133101423/25000000000000 : ℝ)^6407 := by
    have hnat : (844469781 : ℕ)^8455*25000000000000^6407 ≤ 8013133101423^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844469781 2000000000 8013133101423 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882554229/2000000000 : ℝ)^8455 ≤ (33973732997433/100000000000000 : ℝ)^6407 := by
    have hnat : (882554229 : ℕ)^8455*100000000000000^6407 ≤ 33973732997433^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882554229 2000000000 33973732997433 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412771301/10000000000 : ℝ)^8455 ≤ (16986867291191/50000000000000 : ℝ)^6407 := by
    have hnat : (4412771301 : ℕ)^8455*50000000000000^6407 ≤ 16986867291191^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412771301 10000000000 16986867291191 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844469781/2000000000 : ℝ), (882554229/2000000000 : ℝ), (4412771301/10000000000 : ℝ)] ![(8013133101423/25000000000000 : ℝ), (33973732997433/100000000000000 : ℝ), (16986867291191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844469781/2000000000 : ℝ)|^8455 ≤ (8013133101423/25000000000000 : ℝ)^6407
        have hw : |(844469781/2000000000 : ℝ)|=(844469781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882554229/2000000000 : ℝ)|^8455 ≤ (33973732997433/100000000000000 : ℝ)^6407
        have hw : |(882554229/2000000000 : ℝ)|=(882554229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412771301/10000000000 : ℝ)|^8455 ≤ (16986867291191/50000000000000 : ℝ)^6407
        have hw : |(4412771301/10000000000 : ℝ)|=(4412771301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62251/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29697/50000 : ℝ) ∧ (10021/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83389/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11503/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (1659603538852203/12500000000000000000 : ℝ) := by
    have hpowers : (11503/100000 : ℝ)^4227 ≤ (1659603538852203/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11503 : ℕ)^4227*12500000000000000000^1024 ≤ 1659603538852203^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11503 100000 1659603538852203 12500000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11503/100000 : ℝ)) (X := (1659603538852203/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (4227/1024 : ℝ) ≤ (12066338146063/39062500000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^4227 ≤ (12066338146063/39062500000000000 : ℝ)^1024 := by
      have hnat : (7057 : ℕ)^4227*39062500000000000^1024 ≤ 12066338146063^1024*50000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 12066338146063 39062500000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (12066338146063/39062500000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251659603538852203/6250000000000000000 : ℝ) ≤ (10000643203436587/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (6251659603538852203/6250000000000000000 : ℝ)^1024 ≤ (10000643203436587/10000000000000000 : ℝ)^4227 := by
      have hnat : (6251659603538852203 : ℕ)^1024*10000000000000000^4227 ≤ 10000643203436587^4227*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251659603538852203 6250000000000000000 10000643203436587 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000643203436587/10000000000000000 : ℝ)) (X := (6251659603538852203/6250000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505520831745592363/12500000000000000000 : ℝ) ≤ (1250133720982889/1250000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (12505520831745592363/12500000000000000000 : ℝ)^1024 ≤ (1250133720982889/1250000000000000 : ℝ)^4227 := by
      have hnat : (12505520831745592363 : ℕ)^1024*1250000000000000^4227 ≤ 1250133720982889^4227*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505520831745592363 12500000000000000000 1250133720982889 1250000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250133720982889/1250000000000000 : ℝ)) (X := (12505520831745592363/12500000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (19543316338146063/19531250000000000 : ℝ) ≤ (10001496332289637/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (19543316338146063/19531250000000000 : ℝ)^1024 ≤ (10001496332289637/10000000000000000 : ℝ)^4227 := by
      have hnat : (19543316338146063 : ℕ)^1024*10000000000000000^4227 ≤ 10001496332289637^4227*19531250000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19543316338146063 19531250000000000 10001496332289637 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001496332289637/10000000000000000 : ℝ)) (X := (19543316338146063/19531250000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1659603538852203/12500000000000000000 : ℝ) ≤ ((26101865862976294507/26110000000000000000 : ℝ)+2*(17062577061/10444000000000 : ℝ)*(11503/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (26101865862976294507/26110000000000000000 : ℝ)+2*(17062577061/10444000000000 : ℝ)*(11503/100000 : ℝ)=(10000643203436587/10000000000000000 : ℝ) by norm_num, show 1+2*(1659603538852203/12500000000000000000 : ℝ)=(6251659603538852203/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12066338146063/39062500000000000 : ℝ)+(1659603538852203/12500000000000000000 : ℝ) ≤ ((26101865862976294507/26110000000000000000 : ℝ)+(17062577061/10444000000000 : ℝ)*((7057/50000 : ℝ)+(11503/100000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (26101865862976294507/26110000000000000000 : ℝ)+(17062577061/10444000000000 : ℝ)*((7057/50000 : ℝ)+(11503/100000 : ℝ))=(1250133720982889/1250000000000000 : ℝ) by norm_num, show 1+(12066338146063/39062500000000000 : ℝ)+(1659603538852203/12500000000000000000 : ℝ)=(12505520831745592363/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12066338146063/39062500000000000 : ℝ) ≤ ((26101865862976294507/26110000000000000000 : ℝ)+2*(17062577061/10444000000000 : ℝ)*(7057/50000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (26101865862976294507/26110000000000000000 : ℝ)+2*(17062577061/10444000000000 : ℝ)*(7057/50000 : ℝ)=(10001496332289637/10000000000000000 : ℝ) by norm_num, show 1+2*(12066338146063/39062500000000000 : ℝ)=(19543316338146063/19531250000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26101865862976294507/26110000000000000000 : ℝ)*(X 1 0+X 2 0)+(17062577061/10444000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (26101865862976294507/26110000000000000000 : ℝ)) (alpha := (17062577061/10444000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26101865862976294507/26110000000000000000 : ℝ)*(X 0 1+X 2 1)+(17062577061/10444000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (26101865862976294507/26110000000000000000 : ℝ)) (alpha := (17062577061/10444000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26101865862976294507/26110000000000000000 : ℝ)*(X 0 2+X 1 2)+(17062577061/10444000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (26101865862976294507/26110000000000000000 : ℝ)) (alpha := (17062577061/10444000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1987719803/10000000000 : ℝ)*X 0 0+(83977141/156250000 : ℝ)*X 0 1+(4198857/7812500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296930493/10000000000 : ℝ)*X 1 0+(-2093243319/10000000000 : ℝ)*X 1 1+(5374537037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296930227/10000000000 : ℝ)*X 2 0+(1343634269/2500000000 : ℝ)*X 2 1+(-261655453/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4454370587/10000000000 : ℝ)*X 0 0+(429690327/1000000000 : ℝ)*X 0 1+(4296902999/10000000000 : ℝ)*X 0 2+(4454370587/10000000000 : ℝ)*X 1 0+(429690327/1000000000 : ℝ)*X 1 1+(4296902999/10000000000 : ℝ)*X 1 2+(4454370587/10000000000 : ℝ)*X 2 0+(429690327/1000000000 : ℝ)*X 2 1+(4296902999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-558811113/2500000000 : ℝ)*X 0 0+(330155353/625000000 : ℝ)*X 0 1+(5282485643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2680895837/5000000000 : ℝ)*X 1 0+(-21297911/100000000 : ℝ)*X 1 1+(5282485671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2680895847/5000000000 : ℝ)*X 2 0+(528248563/1000000000 : ℝ)*X 2 1+(-1064895563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120649077/5000000000 : ℝ)*X 0 0+(2201709661/5000000000 : ℝ)*X 0 1+(2201709731/5000000000 : ℝ)*X 0 2+(2120649077/5000000000 : ℝ)*X 1 0+(2201709661/5000000000 : ℝ)*X 1 1+(2201709731/5000000000 : ℝ)*X 1 2+(2120649077/5000000000 : ℝ)*X 2 0+(2201709661/5000000000 : ℝ)*X 2 1+(2201709731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1091677873/5000000000 : ℝ)*X 0 0+(652457501/1250000000 : ℝ)*X 0 1+(1346037441/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290153871/10000000000 : ℝ)*X 1 0+(-65292503/312500000 : ℝ)*X 1 1+(336509371/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322538513/2500000000 : ℝ)*X 2 0+(5384149757/10000000000 : ℝ)*X 2 1+(-65292503/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4476349179/10000000000 : ℝ)*X 0 0+(4285773363/10000000000 : ℝ)*X 0 1+(267860829/625000000 : ℝ)*X 0 2+(4476349179/10000000000 : ℝ)*X 1 0+(4285773363/10000000000 : ℝ)*X 1 1+(267860829/625000000 : ℝ)*X 1 2+(4476349179/10000000000 : ℝ)*X 2 0+(4285773363/10000000000 : ℝ)*X 2 1+(267860829/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2039857053/10000000000 : ℝ)*X 0 0+(2718083609/5000000000 : ℝ)*X 0 1+(2637199741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683743909/5000000000 : ℝ)*X 1 0+(-2132945723/10000000000 : ℝ)*X 1 1+(329649949/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367487699/10000000000 : ℝ)*X 2 0+(659299909/1250000000 : ℝ)*X 2 1+(-1066472883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((844469781/2000000000 : ℝ)*X 0 0+(882554229/2000000000 : ℝ)*X 0 1+(4412771301/10000000000 : ℝ)*X 0 2+(844469781/2000000000 : ℝ)*X 1 0+(882554229/2000000000 : ℝ)*X 1 1+(4412771301/10000000000 : ℝ)*X 1 2+(844469781/2000000000 : ℝ)*X 2 0+(882554229/2000000000 : ℝ)*X 2 1+(4412771301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62251/100000 : ℝ) ≤ (-812649211422001355332520826839607/1305500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4447427/20000000000000 : ℝ)*(upper0) + (1618587/12500000000000 : ℝ)*(upper1) + (11716161/50000000000000 : ℝ)*(upper2) + (7025887/25000000000000 : ℝ)*(upper3) + (61112597/100000000000000 : ℝ)*(upper5) + (4019673347199767/100000000000000 : ℝ)*(major0) + (4019673347199767/100000000000000 : ℝ)*(major1) + (4019673347199767/100000000000000 : ℝ)*(major2) + (5281596963/100000000000000 : ℝ)*(sp2) + (4209277363/100000000000000 : ℝ)*(sp3) + (2706222546590927/50000000000000 : ℝ)*(sp4) + (2706222546590927/50000000000000 : ℝ)*(sp5) + (541243981158489/10000000000000 : ℝ)*(sp6) + (2647646765396737/100000000000000 : ℝ)*(sp7) + (26476509746741/1000000000000 : ℝ)*(f.failure) + (2706222546590927/50000000000000 : ℝ)*(f.sum) + (5300103826027/1305500000000000000000000000 : ℝ)*base65 + (5828231722845279869/2611000000000000000000000000000000 : ℝ)*base67 + (251323070827261720131/2611000000000000000000000000000000 : ℝ)*base70 + (7250525776396279869/2611000000000000000000000000000000 : ℝ)*base71 + (7612191907629/2611000000000000000000000000 : ℝ)*base74 + (101475409809493720131/2611000000000000000000000000000000 : ℝ)*base76 + (34982163920081279869/2611000000000000000000000000000000 : ℝ)*base77 + (4069463438789279869/2611000000000000000000000000000000 : ℝ)*base79 + (175762479079667/1305500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (141569/25000000000000000000 : ℝ)*base90 + (141569/25000000000000000000 : ℝ)*base92 + (141569/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29697/50000 : ℝ) ≤ (193853909552300892956063880506973/326375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31811193/25000000000000 : ℝ)*(lower0) + (2424751/25000000000000 : ℝ)*(upper1) + (8083747/4000000000000 : ℝ)*(upper2) + (10336567/20000000000000 : ℝ)*(upper3) + (18276167/100000000000000 : ℝ)*(lower5) + (2042896484652213/50000000000000 : ℝ)*(major0) + (2042896484652213/50000000000000 : ℝ)*(major1) + (2042896484652213/50000000000000 : ℝ)*(major2) + (5460585054450259/100000000000000 : ℝ)*(sp0) + (5460585047641489/100000000000000 : ℝ)*(sp1) + (218420049375033/4000000000000 : ℝ)*(sp2) + (2691202195579261/100000000000000 : ℝ)*(sp3) + (680877/10000000000000 : ℝ)*(sp5) + (41910037217/50000000000000 : ℝ)*(sp10) + (2691202195579261/100000000000000 : ℝ)*(f.failure) + (5460585054450259/100000000000000 : ℝ)*(f.sum) + (11770547319/6527500000000000000000000 : ℝ)*base66 + (8849690955233206009/1305500000000000000000000000000000 : ℝ)*base68 + (38389635926444706009/1305500000000000000000000000000000 : ℝ)*base70 + (496607336187793991/1305500000000000000000000000000000 : ℝ)*base71 + (4958075795261/2611000000000000000000000000 : ℝ)*base73 + (15691416732021206009/1305500000000000000000000000000000 : ℝ)*base76 + (9653738436435206009/1305500000000000000000000000000000 : ℝ)*base78 + (21593604694454206009/1305500000000000000000000000000000 : ℝ)*base80 + (3679872666781/522200000000000000000000000 : ℝ)*base81 + (1032249/2500000000000000000000 : ℝ)*base90 + (1032249/2500000000000000000000 : ℝ)*base92 + (1032249/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10021/12500 : ℝ) ≤ (1046622471422752210572865339541949/1305500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40880057/50000000000000 : ℝ)*(upper0) + (9963019/12500000000000 : ℝ)*(upper1) + (31111/800000000000 : ℝ)*(upper3) + (3071023/5000000000000 : ℝ)*(upper4) + (4552306915400931/100000000000000 : ℝ)*(major0) + (4552306915400931/100000000000000 : ℝ)*(major1) + (4552306915400931/100000000000000 : ℝ)*(major2) + (37528968957/20000000000000 : ℝ)*(sp1) + (115910514569/100000000000000 : ℝ)*(sp2) + (25707858277/100000000000000 : ℝ)*(sp3) + (6079408003775723/100000000000000 : ℝ)*(sp8) + (6079220358930937/100000000000000 : ℝ)*(sp9) + (3039646046630577/50000000000000 : ℝ)*(sp10) + (299845670613523/10000000000000 : ℝ)*(sp11) + (749620603498377/25000000000000 : ℝ)*(f.failure) + (6079408003775723/100000000000000 : ℝ)*(f.sum) + (7945803262917/1305500000000000000000000000 : ℝ)*base65 + (12799421577011486017/2611000000000000000000000000000000 : ℝ)*base67 + (2733450715849513983/2611000000000000000000000000000000 : ℝ)*base70 + (5311123611604486017/2611000000000000000000000000000000 : ℝ)*base71 + (626318087889/326375000000000000000000000 : ℝ)*base73 + (3977312068604513983/2611000000000000000000000000000000 : ℝ)*base76 + (933685402775486017/2611000000000000000000000000000000 : ℝ)*base77 + (16374105023793486017/2611000000000000000000000000000000 : ℝ)*base79 + (8443885205261/1305500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1362693/625000000000000000000 : ℝ)*base90 + (1362693/625000000000000000000 : ℝ)*base92 + (1362693/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83389/100000 : ℝ) ≤ (-1088614379972047113449541549794289/1305500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23583827/50000000000000 : ℝ)*(upper3) + (72333471/100000000000000 : ℝ)*(lower4) + (67050643/100000000000000 : ℝ)*(upper5) + (4587938745369391/100000000000000 : ℝ)*(major0) + (4587938745369391/100000000000000 : ℝ)*(major1) + (4587938745369391/100000000000000 : ℝ)*(major2) + (8262282899/50000000000000 : ℝ)*(sp4) + (302659198123/100000000000000 : ℝ)*(sp5) + (300508916793/100000000000000 : ℝ)*(sp6) + (151700278601/100000000000000 : ℝ)*(sp7) + (618170441437391/10000000000000 : ℝ)*(sp12) + (1236283655948317/20000000000000 : ℝ)*(sp13) + (1545355107505729/25000000000000 : ℝ)*(sp14) + (3021800444013051/100000000000000 : ℝ)*(sp15) + (755488036072913/25000000000000 : ℝ)*(f.failure) + (6181720938939709/100000000000000 : ℝ)*(f.sum) + (822754211921/1305500000000000000000000000 : ℝ)*base65 + (1124683848264264763/2611000000000000000000000000000000 : ℝ)*base68 + (7445244724670264763/2611000000000000000000000000000000 : ℝ)*base70 + (2620509120595735237/2611000000000000000000000000000000 : ℝ)*base71 + (4329044124227/2611000000000000000000000000 : ℝ)*base74 + (14094697330100735237/2611000000000000000000000000000000 : ℝ)*base75 + (14270802353938264763/2611000000000000000000000000000000 : ℝ)*base78 + (16996305993902264763/2611000000000000000000000000000000 : ℝ)*base80 + (2392738517013/1305500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1800083/625000000000000000000 : ℝ)*base89 + (1800083/625000000000000000000 : ℝ)*base91 + (1800083/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1262_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29697/50000 : ℝ) else (10021/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83389/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1262_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1262_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29697/50000 : ℝ) else (10021/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83389/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1262_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29697/50000 : ℝ) else (10021/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83389/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
