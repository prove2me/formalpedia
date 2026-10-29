-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1559_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:58.606311+00:00
-- url     : https://prove2.me/submissions/c27e9114-6f5f-40c9-922f-81f9a92788b7

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
theorem support_rectangle_w1559_s0_0 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-818550073/5000000000 : ℝ)*x 0 + (5877546699/10000000000 : ℝ)*x 1 + (1218727983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818550073/5000000000 : ℝ)^4615 ≤ (977154051467/10000000000000 : ℝ)^3591 := by
    have hnat : (818550073 : ℕ)^4615*10000000000000^3591 ≤ 977154051467^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818550073 5000000000 977154051467 10000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5877546699/10000000000 : ℝ)^4615 ≤ (50510382748411/100000000000000 : ℝ)^3591 := by
    have hnat : (5877546699 : ℕ)^4615*100000000000000^3591 ≤ 50510382748411^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5877546699 10000000000 50510382748411 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218727983/2500000000 : ℝ)^4615 ≤ (19859038361677/50000000000000 : ℝ)^3591 := by
    have hnat : (1218727983 : ℕ)^4615*50000000000000^3591 ≤ 19859038361677^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218727983 2500000000 19859038361677 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-818550073/5000000000 : ℝ), (5877546699/10000000000 : ℝ), (1218727983/2500000000 : ℝ)] ![(977154051467/10000000000000 : ℝ), (50510382748411/100000000000000 : ℝ), (19859038361677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-818550073/5000000000 : ℝ)|^4615 ≤ (977154051467/10000000000000 : ℝ)^3591
        have hw : |(-818550073/5000000000 : ℝ)|=(818550073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5877546699/10000000000 : ℝ)|^4615 ≤ (50510382748411/100000000000000 : ℝ)^3591
        have hw : |(5877546699/10000000000 : ℝ)|=(5877546699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1218727983/2500000000 : ℝ)|^4615 ≤ (19859038361677/50000000000000 : ℝ)^3591
        have hw : |(1218727983/2500000000 : ℝ)|=(1218727983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_1 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093565971/2000000000 : ℝ)*x 0 + (-2195791823/10000000000 : ℝ)*x 1 + (4874911933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093565971/2000000000 : ℝ)^4615 ≤ (23015531968839/50000000000000 : ℝ)^3591 := by
    have hnat : (1093565971 : ℕ)^4615*50000000000000^3591 ≤ 23015531968839^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093565971 2000000000 23015531968839 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195791823/10000000000 : ℝ)^4615 ≤ (14250859306001/100000000000000 : ℝ)^3591 := by
    have hnat : (2195791823 : ℕ)^4615*100000000000000^3591 ≤ 14250859306001^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195791823 10000000000 14250859306001 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4874911933/10000000000 : ℝ)^4615 ≤ (1588723069353/4000000000000 : ℝ)^3591 := by
    have hnat : (4874911933 : ℕ)^4615*4000000000000^3591 ≤ 1588723069353^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4874911933 10000000000 1588723069353 4000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093565971/2000000000 : ℝ), (-2195791823/10000000000 : ℝ), (4874911933/10000000000 : ℝ)] ![(23015531968839/50000000000000 : ℝ), (14250859306001/100000000000000 : ℝ), (1588723069353/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093565971/2000000000 : ℝ)|^4615 ≤ (23015531968839/50000000000000 : ℝ)^3591
        have hw : |(1093565971/2000000000 : ℝ)|=(1093565971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195791823/10000000000 : ℝ)|^4615 ≤ (14250859306001/100000000000000 : ℝ)^3591
        have hw : |(-2195791823/10000000000 : ℝ)|=(2195791823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4874911933/10000000000 : ℝ)|^4615 ≤ (1588723069353/4000000000000 : ℝ)^3591
        have hw : |(4874911933/10000000000 : ℝ)|=(4874911933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_2 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5467829899/10000000000 : ℝ)*x 0 + (4874911883/10000000000 : ℝ)*x 1 + (-2195791829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5467829899/10000000000 : ℝ)^4615 ≤ (46031064413719/100000000000000 : ℝ)^3591 := by
    have hnat : (5467829899 : ℕ)^4615*100000000000000^3591 ≤ 46031064413719^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467829899 10000000000 46031064413719 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4874911883/10000000000 : ℝ)^4615 ≤ (39718076210287/100000000000000 : ℝ)^3591 := by
    have hnat : (4874911883 : ℕ)^4615*100000000000000^3591 ≤ 39718076210287^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4874911883 10000000000 39718076210287 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195791829/10000000000 : ℝ)^4615 ≤ (7125429678023/50000000000000 : ℝ)^3591 := by
    have hnat : (2195791829 : ℕ)^4615*50000000000000^3591 ≤ 7125429678023^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195791829 10000000000 7125429678023 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5467829899/10000000000 : ℝ), (4874911883/10000000000 : ℝ), (-2195791829/10000000000 : ℝ)] ![(46031064413719/100000000000000 : ℝ), (39718076210287/100000000000000 : ℝ), (7125429678023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5467829899/10000000000 : ℝ)|^4615 ≤ (46031064413719/100000000000000 : ℝ)^3591
        have hw : |(5467829899/10000000000 : ℝ)|=(5467829899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4874911883/10000000000 : ℝ)|^4615 ≤ (39718076210287/100000000000000 : ℝ)^3591
        have hw : |(4874911883/10000000000 : ℝ)|=(4874911883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195791829/10000000000 : ℝ)|^4615 ≤ (7125429678023/50000000000000 : ℝ)^3591
        have hw : |(-2195791829/10000000000 : ℝ)|=(2195791829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_3 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4132700307/10000000000 : ℝ)*x 0 + (618518699/2000000000 : ℝ)*x 1 + (5441649691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132700307/10000000000 : ℝ)^4615 ≤ (32121823883529/100000000000000 : ℝ)^3591 := by
    have hnat : (4132700307 : ℕ)^4615*100000000000000^3591 ≤ 32121823883529^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132700307 10000000000 32121823883529 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618518699/2000000000 : ℝ)^4615 ≤ (2213016517463/10000000000000 : ℝ)^3591 := by
    have hnat : (618518699 : ℕ)^4615*10000000000000^3591 ≤ 2213016517463^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618518699 2000000000 2213016517463 10000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441649691/10000000000 : ℝ)^4615 ≤ (9149602187419/20000000000000 : ℝ)^3591 := by
    have hnat : (5441649691 : ℕ)^4615*20000000000000^3591 ≤ 9149602187419^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441649691 10000000000 9149602187419 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132700307/10000000000 : ℝ), (618518699/2000000000 : ℝ), (5441649691/10000000000 : ℝ)] ![(32121823883529/100000000000000 : ℝ), (2213016517463/10000000000000 : ℝ), (9149602187419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132700307/10000000000 : ℝ)|^4615 ≤ (32121823883529/100000000000000 : ℝ)^3591
        have hw : |(4132700307/10000000000 : ℝ)|=(4132700307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618518699/2000000000 : ℝ)|^4615 ≤ (2213016517463/10000000000000 : ℝ)^3591
        have hw : |(618518699/2000000000 : ℝ)|=(618518699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441649691/10000000000 : ℝ)|^4615 ≤ (9149602187419/20000000000000 : ℝ)^3591
        have hw : |(5441649691/10000000000 : ℝ)|=(5441649691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_4 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410059603/2500000000 : ℝ)*x 0 + (4900241761/10000000000 : ℝ)*x 1 + (1462829423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410059603/2500000000 : ℝ)^4615 ≤ (9795620292303/100000000000000 : ℝ)^3591 := by
    have hnat : (410059603 : ℕ)^4615*100000000000000^3591 ≤ 9795620292303^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410059603 2500000000 9795620292303 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4900241761/10000000000 : ℝ)^4615 ≤ (19991747619913/50000000000000 : ℝ)^3591 := by
    have hnat : (4900241761 : ℕ)^4615*50000000000000^3591 ≤ 19991747619913^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900241761 10000000000 19991747619913 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1462829423/2500000000 : ℝ)^4615 ≤ (50220884453667/100000000000000 : ℝ)^3591 := by
    have hnat : (1462829423 : ℕ)^4615*100000000000000^3591 ≤ 50220884453667^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462829423 2500000000 50220884453667 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410059603/2500000000 : ℝ), (4900241761/10000000000 : ℝ), (1462829423/2500000000 : ℝ)] ![(9795620292303/100000000000000 : ℝ), (19991747619913/50000000000000 : ℝ), (50220884453667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410059603/2500000000 : ℝ)|^4615 ≤ (9795620292303/100000000000000 : ℝ)^3591
        have hw : |(-410059603/2500000000 : ℝ)|=(410059603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4900241761/10000000000 : ℝ)|^4615 ≤ (19991747619913/50000000000000 : ℝ)^3591
        have hw : |(4900241761/10000000000 : ℝ)|=(4900241761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1462829423/2500000000 : ℝ)|^4615 ≤ (50220884453667/100000000000000 : ℝ)^3591
        have hw : |(1462829423/2500000000 : ℝ)|=(1462829423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_5 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038750581/2000000000 : ℝ)*x 0 + (-1219386361/10000000000 : ℝ)*x 1 + (5851317651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038750581/2000000000 : ℝ)^4615 ≤ (10771810215093/25000000000000 : ℝ)^3591 := by
    have hnat : (1038750581 : ℕ)^4615*25000000000000^3591 ≤ 10771810215093^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038750581 2000000000 10771810215093 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1219386361/10000000000 : ℝ)^4615 ≤ (3345937565293/50000000000000 : ℝ)^3591 := by
    have hnat : (1219386361 : ℕ)^4615*50000000000000^3591 ≤ 3345937565293^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219386361 10000000000 3345937565293 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5851317651/10000000000 : ℝ)^4615 ≤ (2008835360057/4000000000000 : ℝ)^3591 := by
    have hnat : (5851317651 : ℕ)^4615*4000000000000^3591 ≤ 2008835360057^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5851317651 10000000000 2008835360057 4000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038750581/2000000000 : ℝ), (-1219386361/10000000000 : ℝ), (5851317651/10000000000 : ℝ)] ![(10771810215093/25000000000000 : ℝ), (3345937565293/50000000000000 : ℝ), (2008835360057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038750581/2000000000 : ℝ)|^4615 ≤ (10771810215093/25000000000000 : ℝ)^3591
        have hw : |(1038750581/2000000000 : ℝ)|=(1038750581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1219386361/10000000000 : ℝ)|^4615 ≤ (3345937565293/50000000000000 : ℝ)^3591
        have hw : |(-1219386361/10000000000 : ℝ)|=(1219386361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5851317651/10000000000 : ℝ)|^4615 ≤ (2008835360057/4000000000000 : ℝ)^3591
        have hw : |(5851317651/10000000000 : ℝ)|=(5851317651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_6 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038750589/2000000000 : ℝ)*x 0 + (5851317827/10000000000 : ℝ)*x 1 + (-152423253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038750589/2000000000 : ℝ)^4615 ≤ (43087241286837/100000000000000 : ℝ)^3591 := by
    have hnat : (1038750589 : ℕ)^4615*100000000000000^3591 ≤ 43087241286837^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038750589 2000000000 43087241286837 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5851317827/10000000000 : ℝ)^4615 ≤ (12555221485689/25000000000000 : ℝ)^3591 := by
    have hnat : (5851317827 : ℕ)^4615*25000000000000^3591 ≤ 12555221485689^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5851317827 10000000000 12555221485689 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152423253/1250000000 : ℝ)^4615 ≤ (3345936376893/50000000000000 : ℝ)^3591 := by
    have hnat : (152423253 : ℕ)^4615*50000000000000^3591 ≤ 3345936376893^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152423253 1250000000 3345936376893 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038750589/2000000000 : ℝ), (5851317827/10000000000 : ℝ), (-152423253/1250000000 : ℝ)] ![(43087241286837/100000000000000 : ℝ), (12555221485689/25000000000000 : ℝ), (3345936376893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038750589/2000000000 : ℝ)|^4615 ≤ (43087241286837/100000000000000 : ℝ)^3591
        have hw : |(1038750589/2000000000 : ℝ)|=(1038750589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5851317827/10000000000 : ℝ)|^4615 ≤ (12555221485689/25000000000000 : ℝ)^3591
        have hw : |(5851317827/10000000000 : ℝ)|=(5851317827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152423253/1250000000 : ℝ)|^4615 ≤ (3345936376893/50000000000000 : ℝ)^3591
        have hw : |(-152423253/1250000000 : ℝ)|=(152423253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s0_7 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (828010439/2000000000 : ℝ)*x 0 + (1076460977/2000000000 : ℝ)*x 1 + (985639/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828010439/2000000000 : ℝ)^4615 ≤ (16097640304193/50000000000000 : ℝ)^3591 := by
    have hnat : (828010439 : ℕ)^4615*50000000000000^3591 ≤ 16097640304193^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828010439 2000000000 16097640304193 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076460977/2000000000 : ℝ)^4615 ≤ (22553914756591/50000000000000 : ℝ)^3591 := by
    have hnat : (1076460977 : ℕ)^4615*50000000000000^3591 ≤ 22553914756591^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076460977 2000000000 22553914756591 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985639/3125000 : ℝ)^4615 ≤ (11348444930067/50000000000000 : ℝ)^3591 := by
    have hnat : (985639 : ℕ)^4615*50000000000000^3591 ≤ 11348444930067^3591*3125000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985639 3125000 11348444930067 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828010439/2000000000 : ℝ), (1076460977/2000000000 : ℝ), (985639/3125000 : ℝ)] ![(16097640304193/50000000000000 : ℝ), (22553914756591/50000000000000 : ℝ), (11348444930067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828010439/2000000000 : ℝ)|^4615 ≤ (16097640304193/50000000000000 : ℝ)^3591
        have hw : |(828010439/2000000000 : ℝ)|=(828010439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076460977/2000000000 : ℝ)|^4615 ≤ (22553914756591/50000000000000 : ℝ)^3591
        have hw : |(1076460977/2000000000 : ℝ)|=(1076460977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(985639/3125000 : ℝ)|^4615 ≤ (11348444930067/50000000000000 : ℝ)^3591
        have hw : |(985639/3125000 : ℝ)|=(985639/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1559_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2489/10000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4613/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4613 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4613*1^1024 ≤ 0^1024*1^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4613/1024 : ℝ) ≤ (322371685699550089/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4613 ≤ (322371685699550089/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4613*20000000000000000000^1024 ≤ 322371685699550089^1024*5^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 322371685699550089 20000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (322371685699550089/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4613 := by
      have hnat : (1 : ℕ)^1024*1^4613 ≤ 1^4613*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20322371685699550089/20000000000000000000 : ℝ) ≤ (10035558019491009/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (20322371685699550089/20000000000000000000 : ℝ)^1024 ≤ (10035558019491009/10000000000000000 : ℝ)^4613 := by
      have hnat : (20322371685699550089 : ℕ)^1024*10000000000000000^4613 ≤ 10035558019491009^4613*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20322371685699550089 20000000000000000000 10035558019491009 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035558019491009/10000000000000000 : ℝ)) (X := (20322371685699550089/20000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10322371685699550089/10000000000000000000 : ℝ) ≤ (5035558019491009/5000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (10322371685699550089/10000000000000000000 : ℝ)^1024 ≤ (5035558019491009/5000000000000000 : ℝ)^4613 := by
      have hnat : (10322371685699550089 : ℕ)^1024*5000000000000000^4613 ≤ 5035558019491009^4613*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10322371685699550089 10000000000000000000 5035558019491009 5000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035558019491009/5000000000000000 : ℝ)) (X := (10322371685699550089/10000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35558019491009/4000000000000000 : ℝ)*(0 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35558019491009/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(322371685699550089/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35558019491009/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4613/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35558019491009/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035558019491009/10000000000000000 : ℝ) by norm_num, show 1+(322371685699550089/20000000000000000000 : ℝ)+(0 : ℝ)=(20322371685699550089/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(322371685699550089/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35558019491009/4000000000000000 : ℝ)*(2/5 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35558019491009/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035558019491009/5000000000000000 : ℝ) by norm_num, show 1+2*(322371685699550089/20000000000000000000 : ℝ)=(10322371685699550089/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35558019491009/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35558019491009/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35558019491009/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35558019491009/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35558019491009/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35558019491009/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-818550073/5000000000 : ℝ)*X 0 0+(5877546699/10000000000 : ℝ)*X 0 1+(1218727983/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1093565971/2000000000 : ℝ)*X 1 0+(-2195791823/10000000000 : ℝ)*X 1 1+(4874911933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5467829899/10000000000 : ℝ)*X 2 0+(4874911883/10000000000 : ℝ)*X 2 1+(-2195791829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4132700307/10000000000 : ℝ)*X 0 0+(618518699/2000000000 : ℝ)*X 0 1+(5441649691/10000000000 : ℝ)*X 0 2+(4132700307/10000000000 : ℝ)*X 1 0+(618518699/2000000000 : ℝ)*X 1 1+(5441649691/10000000000 : ℝ)*X 1 2+(4132700307/10000000000 : ℝ)*X 2 0+(618518699/2000000000 : ℝ)*X 2 1+(5441649691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-410059603/2500000000 : ℝ)*X 0 0+(4900241761/10000000000 : ℝ)*X 0 1+(1462829423/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038750581/2000000000 : ℝ)*X 1 0+(-1219386361/10000000000 : ℝ)*X 1 1+(5851317651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038750589/2000000000 : ℝ)*X 2 0+(5851317827/10000000000 : ℝ)*X 2 1+(-152423253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((828010439/2000000000 : ℝ)*X 0 0+(1076460977/2000000000 : ℝ)*X 0 1+(985639/3125000 : ℝ)*X 0 2+(828010439/2000000000 : ℝ)*X 1 0+(1076460977/2000000000 : ℝ)*X 1 1+(985639/3125000 : ℝ)*X 1 2+(828010439/2000000000 : ℝ)*X 2 0+(1076460977/2000000000 : ℝ)*X 2 1+(985639/3125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (241806342028689732559311/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46453227/100000000000000 : ℝ)*(base1) + (504820607/50000000000000 : ℝ)*(base19) + (508833593/50000000000000 : ℝ)*(base23) + (65216347/50000000000000 : ℝ)*(upper3) + (32729173/25000000000000 : ℝ)*(upper5) + (711542780841493/100000000000000 : ℝ)*(major0) + (711542780841493/100000000000000 : ℝ)*(major1) + (711542780841493/100000000000000 : ℝ)*(major2) + (124671960506287/12500000000000 : ℝ)*(sp0) + (498689180371663/50000000000000 : ℝ)*(sp1) + (199475670543471/20000000000000 : ℝ)*(sp2) + (26606524501351/6250000000000 : ℝ)*(sp3) + (233299217/6250000000000 : ℝ)*(sp4) + (795809683/50000000000000 : ℝ)*(sp7) + (3325828360111/781250000000 : ℝ)*(f.failure) + (997379370384541/100000000000000 : ℝ)*(f.sum) + (596024792763563/200000000000000000000000000000 : ℝ)*base66 + (110712202763563/400000000000000000000000000000 : ℝ)*base68 + (219201013163563/400000000000000000000000000000 : ℝ)*base70 + (1152783682836437/400000000000000000000000000000 : ℝ)*base71 + (1204792938763563/200000000000000000000000000000 : ℝ)*base74 + (2493029922036437/400000000000000000000000000000 : ℝ)*base75 + (315376083163563/400000000000000000000000000000 : ℝ)*base78 + (27927550363563/400000000000000000000000000000 : ℝ)*base80 + (732204464563563/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (724157/78125000000000000000 : ℝ)*base90 + (724157/78125000000000000000 : ℝ)*base92 + (724157/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7472694349898872434849/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246462379/12500000000000 : ℝ)*(base19) + (502141837/25000000000000 : ℝ)*(base23) + (12054571/25000000000000 : ℝ)*(base32) + (301265721/100000000000000 : ℝ)*(upper3) + (123351131/50000000000000 : ℝ)*(upper5) + (15002213650987/2000000000000 : ℝ)*(major0) + (15002213650987/2000000000000 : ℝ)*(major1) + (15002213650987/2000000000000 : ℝ)*(major2) + (1312002431/25000000000000 : ℝ)*(sp1) + (5793211949/100000000000000 : ℝ)*(sp2) + (1051440390932577/100000000000000 : ℝ)*(sp4) + (1051433171223821/100000000000000 : ℝ)*(sp5) + (205357927569/19531250000 : ℝ)*(sp6) + (14024394205799/3125000000000 : ℝ)*(sp7) + (448780662803851/100000000000000 : ℝ)*(f.failure) + (1051440390932577/100000000000000 : ℝ)*(f.sum) + (5027385668117/4000000000000000000000000000 : ℝ)*base66 + (6543871740117/8000000000000000000000000000 : ℝ)*base68 + (11640278996117/8000000000000000000000000000 : ℝ)*base70 + (9004143804117/8000000000000000000000000000 : ℝ)*base72 + (6592719312117/4000000000000000000000000000 : ℝ)*base74 + (35139068428117/8000000000000000000000000000 : ℝ)*base76 + (6186154387883/8000000000000000000000000000 : ℝ)*base77 + (50275587180117/8000000000000000000000000000 : ℝ)*base80 + (2963981360117/4000000000000000000000000000 : ℝ)*base82 + (91428287/10000000000000000000000 : ℝ)*base90 + (91428287/10000000000000000000000 : ℝ)*base92 + (91428287/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1559_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2489/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1559_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1559_s1_0 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-222312197/1250000000 : ℝ)*x 0 + (2770589419/5000000000 : ℝ)*x 1 + (2560097317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222312197/1250000000 : ℝ)^4615 ≤ (5434636122511/50000000000000 : ℝ)^3591 := by
    have hnat : (222312197 : ℕ)^4615*50000000000000^3591 ≤ 5434636122511^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222312197 1250000000 5434636122511 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770589419/5000000000 : ℝ)^4615 ≤ (11706537270717/25000000000000 : ℝ)^3591 := by
    have hnat : (2770589419 : ℕ)^4615*25000000000000^3591 ≤ 11706537270717^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770589419 5000000000 11706537270717 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2560097317/5000000000 : ℝ)^4615 ≤ (21152289325983/50000000000000 : ℝ)^3591 := by
    have hnat : (2560097317 : ℕ)^4615*50000000000000^3591 ≤ 21152289325983^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560097317 5000000000 21152289325983 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222312197/1250000000 : ℝ), (2770589419/5000000000 : ℝ), (2560097317/5000000000 : ℝ)] ![(5434636122511/50000000000000 : ℝ), (11706537270717/25000000000000 : ℝ), (21152289325983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222312197/1250000000 : ℝ)|^4615 ≤ (5434636122511/50000000000000 : ℝ)^3591
        have hw : |(-222312197/1250000000 : ℝ)|=(222312197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770589419/5000000000 : ℝ)|^4615 ≤ (11706537270717/25000000000000 : ℝ)^3591
        have hw : |(2770589419/5000000000 : ℝ)|=(2770589419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2560097317/5000000000 : ℝ)|^4615 ≤ (21152289325983/50000000000000 : ℝ)^3591
        have hw : |(2560097317/5000000000 : ℝ)|=(2560097317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_1 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378312399/10000000000 : ℝ)*x 0 + (-31233769/156250000 : ℝ)*x 1 + (5120194611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378312399/10000000000 : ℝ)^4615 ≤ (45064832588417/100000000000000 : ℝ)^3591 := by
    have hnat : (5378312399 : ℕ)^4615*100000000000000^3591 ≤ 45064832588417^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378312399 10000000000 45064832588417 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31233769/156250000 : ℝ)^4615 ≤ (12630588987237/100000000000000 : ℝ)^3591 := by
    have hnat : (31233769 : ℕ)^4615*100000000000000^3591 ≤ 12630588987237^3591*156250000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31233769 156250000 12630588987237 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5120194611/10000000000 : ℝ)^4615 ≤ (661009037621/1562500000000 : ℝ)^3591 := by
    have hnat : (5120194611 : ℕ)^4615*1562500000000^3591 ≤ 661009037621^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120194611 10000000000 661009037621 1562500000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378312399/10000000000 : ℝ), (-31233769/156250000 : ℝ), (5120194611/10000000000 : ℝ)] ![(45064832588417/100000000000000 : ℝ), (12630588987237/100000000000000 : ℝ), (661009037621/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378312399/10000000000 : ℝ)|^4615 ≤ (45064832588417/100000000000000 : ℝ)^3591
        have hw : |(5378312399/10000000000 : ℝ)|=(5378312399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31233769/156250000 : ℝ)|^4615 ≤ (12630588987237/100000000000000 : ℝ)^3591
        have hw : |(-31233769/156250000 : ℝ)|=(31233769/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5120194611/10000000000 : ℝ)|^4615 ≤ (661009037621/1562500000000 : ℝ)^3591
        have hw : |(5120194611/10000000000 : ℝ)|=(5120194611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_2 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378312359/10000000000 : ℝ)*x 0 + (2560097431/5000000000 : ℝ)*x 1 + (-1998960941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378312359/10000000000 : ℝ)^4615 ≤ (11266208039421/25000000000000 : ℝ)^3591 := by
    have hnat : (5378312359 : ℕ)^4615*25000000000000^3591 ≤ 11266208039421^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378312359 10000000000 11266208039421 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560097431/5000000000 : ℝ)^4615 ≤ (42304581072951/100000000000000 : ℝ)^3591 := by
    have hnat : (2560097431 : ℕ)^4615*100000000000000^3591 ≤ 42304581072951^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560097431 5000000000 42304581072951 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1998960941/10000000000 : ℝ)^4615 ≤ (1578823344267/12500000000000 : ℝ)^3591 := by
    have hnat : (1998960941 : ℕ)^4615*12500000000000^3591 ≤ 1578823344267^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998960941 10000000000 1578823344267 12500000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378312359/10000000000 : ℝ), (2560097431/5000000000 : ℝ), (-1998960941/10000000000 : ℝ)] ![(11266208039421/25000000000000 : ℝ), (42304581072951/100000000000000 : ℝ), (1578823344267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378312359/10000000000 : ℝ)|^4615 ≤ (11266208039421/25000000000000 : ℝ)^3591
        have hw : |(5378312359/10000000000 : ℝ)|=(5378312359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2560097431/5000000000 : ℝ)|^4615 ≤ (42304581072951/100000000000000 : ℝ)^3591
        have hw : |(2560097431/5000000000 : ℝ)|=(2560097431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1998960941/10000000000 : ℝ)|^4615 ≤ (1578823344267/12500000000000 : ℝ)^3591
        have hw : |(-1998960941/10000000000 : ℝ)|=(1998960941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_3 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116232353/5000000000 : ℝ)*x 0 + (3762667957/10000000000 : ℝ)*x 1 + (4748985337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116232353/5000000000 : ℝ)^4615 ≤ (33121782249881/100000000000000 : ℝ)^3591 := by
    have hnat : (2116232353 : ℕ)^4615*100000000000000^3591 ≤ 33121782249881^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116232353 5000000000 33121782249881 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3762667957/10000000000 : ℝ)^4615 ≤ (1138952011167/4000000000000 : ℝ)^3591 := by
    have hnat : (3762667957 : ℕ)^4615*4000000000000^3591 ≤ 1138952011167^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3762667957 10000000000 1138952011167 4000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4748985337/10000000000 : ℝ)^4615 ≤ (19202208731653/50000000000000 : ℝ)^3591 := by
    have hnat : (4748985337 : ℕ)^4615*50000000000000^3591 ≤ 19202208731653^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4748985337 10000000000 19202208731653 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116232353/5000000000 : ℝ), (3762667957/10000000000 : ℝ), (4748985337/10000000000 : ℝ)] ![(33121782249881/100000000000000 : ℝ), (1138952011167/4000000000000 : ℝ), (19202208731653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116232353/5000000000 : ℝ)|^4615 ≤ (33121782249881/100000000000000 : ℝ)^3591
        have hw : |(2116232353/5000000000 : ℝ)|=(2116232353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3762667957/10000000000 : ℝ)|^4615 ≤ (1138952011167/4000000000000 : ℝ)^3591
        have hw : |(3762667957/10000000000 : ℝ)|=(3762667957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4748985337/10000000000 : ℝ)|^4615 ≤ (19202208731653/50000000000000 : ℝ)^3591
        have hw : |(4748985337/10000000000 : ℝ)|=(4748985337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_4 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889361579/5000000000 : ℝ)*x 0 + (5124602937/10000000000 : ℝ)*x 1 + (2768352281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889361579/5000000000 : ℝ)^4615 ≤ (10871044049463/100000000000000 : ℝ)^3591 := by
    have hnat : (889361579 : ℕ)^4615*100000000000000^3591 ≤ 10871044049463^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889361579 5000000000 10871044049463 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124602937/10000000000 : ℝ)^4615 ≤ (5293924164881/12500000000000 : ℝ)^3591 := by
    have hnat : (5124602937 : ℕ)^4615*12500000000000^3591 ≤ 5293924164881^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124602937 10000000000 5293924164881 12500000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768352281/5000000000 : ℝ)^4615 ≤ (46777562614107/100000000000000 : ℝ)^3591 := by
    have hnat : (2768352281 : ℕ)^4615*100000000000000^3591 ≤ 46777562614107^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768352281 5000000000 46777562614107 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889361579/5000000000 : ℝ), (5124602937/10000000000 : ℝ), (2768352281/5000000000 : ℝ)] ![(10871044049463/100000000000000 : ℝ), (5293924164881/12500000000000 : ℝ), (46777562614107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889361579/5000000000 : ℝ)|^4615 ≤ (10871044049463/100000000000000 : ℝ)^3591
        have hw : |(-889361579/5000000000 : ℝ)|=(889361579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124602937/10000000000 : ℝ)|^4615 ≤ (5293924164881/12500000000000 : ℝ)^3591
        have hw : |(5124602937/10000000000 : ℝ)|=(5124602937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768352281/5000000000 : ℝ)|^4615 ≤ (46777562614107/100000000000000 : ℝ)^3591
        have hw : |(2768352281/5000000000 : ℝ)|=(2768352281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_5 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053368999/2000000000 : ℝ)*x 0 + (-316490823/2000000000 : ℝ)*x 1 + (2768351709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053368999/2000000000 : ℝ)^4615 ≤ (8773616055957/20000000000000 : ℝ)^3591 := by
    have hnat : (1053368999 : ℕ)^4615*20000000000000^3591 ≤ 8773616055957^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053368999 2000000000 8773616055957 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316490823/2000000000 : ℝ)^4615 ≤ (4677184758799/50000000000000 : ℝ)^3591 := by
    have hnat : (316490823 : ℕ)^4615*50000000000000^3591 ≤ 4677184758799^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316490823 2000000000 4677184758799 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768351709/5000000000 : ℝ)^4615 ≤ (11694387548191/25000000000000 : ℝ)^3591 := by
    have hnat : (2768351709 : ℕ)^4615*25000000000000^3591 ≤ 11694387548191^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768351709 5000000000 11694387548191 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053368999/2000000000 : ℝ), (-316490823/2000000000 : ℝ), (2768351709/5000000000 : ℝ)] ![(8773616055957/20000000000000 : ℝ), (4677184758799/50000000000000 : ℝ), (11694387548191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053368999/2000000000 : ℝ)|^4615 ≤ (8773616055957/20000000000000 : ℝ)^3591
        have hw : |(1053368999/2000000000 : ℝ)|=(1053368999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316490823/2000000000 : ℝ)|^4615 ≤ (4677184758799/50000000000000 : ℝ)^3591
        have hw : |(-316490823/2000000000 : ℝ)|=(316490823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768351709/5000000000 : ℝ)|^4615 ≤ (11694387548191/25000000000000 : ℝ)^3591
        have hw : |(2768351709/5000000000 : ℝ)|=(2768351709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_6 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053369461/2000000000 : ℝ)*x 0 + (1384175681/2500000000 : ℝ)*x 1 + (-1582451851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053369461/2000000000 : ℝ)^4615 ≤ (21934052503249/50000000000000 : ℝ)^3591 := by
    have hnat : (1053369461 : ℕ)^4615*50000000000000^3591 ≤ 21934052503249^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053369461 2000000000 21934052503249 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384175681/2500000000 : ℝ)^4615 ≤ (46777542657439/100000000000000 : ℝ)^3591 := by
    have hnat : (1384175681 : ℕ)^4615*100000000000000^3591 ≤ 46777542657439^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384175681 2500000000 46777542657439 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1582451851/10000000000 : ℝ)^4615 ≤ (935435231809/10000000000000 : ℝ)^3591 := by
    have hnat : (1582451851 : ℕ)^4615*10000000000000^3591 ≤ 935435231809^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582451851 10000000000 935435231809 10000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053369461/2000000000 : ℝ), (1384175681/2500000000 : ℝ), (-1582451851/10000000000 : ℝ)] ![(21934052503249/50000000000000 : ℝ), (46777542657439/100000000000000 : ℝ), (935435231809/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053369461/2000000000 : ℝ)|^4615 ≤ (21934052503249/50000000000000 : ℝ)^3591
        have hw : |(1053369461/2000000000 : ℝ)|=(1053369461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1384175681/2500000000 : ℝ)|^4615 ≤ (46777542657439/100000000000000 : ℝ)^3591
        have hw : |(1384175681/2500000000 : ℝ)|=(1384175681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1582451851/10000000000 : ℝ)|^4615 ≤ (935435231809/10000000000000 : ℝ)^3591
        have hw : |(-1582451851/10000000000 : ℝ)|=(1582451851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s1_7 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4232994019/10000000000 : ℝ)*x 0 + (592331873/1250000000 : ℝ)*x 1 + (1886576199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4232994019/10000000000 : ℝ)^4615 ≤ (16563552873091/50000000000000 : ℝ)^3591 := by
    have hnat : (4232994019 : ℕ)^4615*50000000000000^3591 ≤ 16563552873091^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232994019 10000000000 16563552873091 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592331873/1250000000 : ℝ)^4615 ≤ (19148544238291/50000000000000 : ℝ)^3591 := by
    have hnat : (592331873 : ℕ)^4615*50000000000000^3591 ≤ 19148544238291^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592331873 1250000000 19148544238291 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886576199/5000000000 : ℝ)^4615 ≤ (28575805760769/100000000000000 : ℝ)^3591 := by
    have hnat : (1886576199 : ℕ)^4615*100000000000000^3591 ≤ 28575805760769^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886576199 5000000000 28575805760769 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4232994019/10000000000 : ℝ), (592331873/1250000000 : ℝ), (1886576199/5000000000 : ℝ)] ![(16563552873091/50000000000000 : ℝ), (19148544238291/50000000000000 : ℝ), (28575805760769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4232994019/10000000000 : ℝ)|^4615 ≤ (16563552873091/50000000000000 : ℝ)^3591
        have hw : |(4232994019/10000000000 : ℝ)|=(4232994019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(592331873/1250000000 : ℝ)|^4615 ≤ (19148544238291/50000000000000 : ℝ)^3591
        have hw : |(592331873/1250000000 : ℝ)|=(592331873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1886576199/5000000000 : ℝ)|^4615 ≤ (28575805760769/100000000000000 : ℝ)^3591
        have hw : |(1886576199/5000000000 : ℝ)|=(1886576199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1559_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2489/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (559/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17857/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2489/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2489/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2489/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2489/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2489/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2489/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3413/100000 : ℝ) ^ (4613/1024 : ℝ) ≤ (4931520836729/20000000000000000000 : ℝ) := by
    have hpowers : (3413/100000 : ℝ)^4613 ≤ (4931520836729/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3413 : ℕ)^4613*20000000000000000000^1024 ≤ 4931520836729^1024*100000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3413 100000 4931520836729 20000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3413/100000 : ℝ)) (X := (4931520836729/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2489/10000 : ℝ) ^ (4613/1024 : ℝ) ≤ (19017916556908693/10000000000000000000 : ℝ) := by
    have hpowers : (2489/10000 : ℝ)^4613 ≤ (19017916556908693/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2489 : ℕ)^4613*10000000000000000000^1024 ≤ 19017916556908693^1024*10000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2489 10000 19017916556908693 10000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2489/10000 : ℝ)) (X := (19017916556908693/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000004931520836729/10000000000000000000 : ℝ) ≤ (5000000547352739/5000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (10000004931520836729/10000000000000000000 : ℝ)^1024 ≤ (5000000547352739/5000000000000000 : ℝ)^4613 := by
      have hnat : (10000004931520836729 : ℕ)^1024*5000000000000000^4613 ≤ 5000000547352739^4613*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000004931520836729 10000000000000000000 5000000547352739 5000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000547352739/5000000000000000 : ℝ)) (X := (10000004931520836729/10000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4007608152926930823/4000000000000000000 : ℝ) ≤ (10004219049766593/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (4007608152926930823/4000000000000000000 : ℝ)^1024 ≤ (10004219049766593/10000000000000000 : ℝ)^4613 := by
      have hnat : (4007608152926930823 : ℕ)^1024*10000000000000000^4613 ≤ 10004219049766593^4613*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4007608152926930823 4000000000000000000 10004219049766593 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004219049766593/10000000000000000 : ℝ)) (X := (4007608152926930823/4000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5019017916556908693/5000000000000000000 : ℝ) ≤ (2502109251206927/2500000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (5019017916556908693/5000000000000000000 : ℝ)^1024 ≤ (2502109251206927/2500000000000000 : ℝ)^4613 := by
      have hnat : (5019017916556908693 : ℕ)^1024*2500000000000000^4613 ≤ 2502109251206927^4613*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5019017916556908693 5000000000000000000 2502109251206927 2500000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502109251206927/2500000000000000 : ℝ)) (X := (5019017916556908693/5000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4931520836729/20000000000000000000 : ℝ) ≤ ((13421326984358898751/13423125000000000000 : ℝ)+2*(843591012223/429540000000000 : ℝ)*(3413/100000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (13421326984358898751/13423125000000000000 : ℝ)+2*(843591012223/429540000000000 : ℝ)*(3413/100000 : ℝ)=(5000000547352739/5000000000000000 : ℝ) by norm_num, show 1+2*(4931520836729/20000000000000000000 : ℝ)=(10000004931520836729/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19017916556908693/10000000000000000000 : ℝ)+(4931520836729/20000000000000000000 : ℝ) ≤ ((13421326984358898751/13423125000000000000 : ℝ)+(843591012223/429540000000000 : ℝ)*((2489/10000 : ℝ)+(3413/100000 : ℝ)))^(4613/1024 : ℝ) := by
    rw [show (13421326984358898751/13423125000000000000 : ℝ)+(843591012223/429540000000000 : ℝ)*((2489/10000 : ℝ)+(3413/100000 : ℝ))=(10004219049766593/10000000000000000 : ℝ) by norm_num, show 1+(19017916556908693/10000000000000000000 : ℝ)+(4931520836729/20000000000000000000 : ℝ)=(4007608152926930823/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19017916556908693/10000000000000000000 : ℝ) ≤ ((13421326984358898751/13423125000000000000 : ℝ)+2*(843591012223/429540000000000 : ℝ)*(2489/10000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (13421326984358898751/13423125000000000000 : ℝ)+2*(843591012223/429540000000000 : ℝ)*(2489/10000 : ℝ)=(2502109251206927/2500000000000000 : ℝ) by norm_num, show 1+2*(19017916556908693/10000000000000000000 : ℝ)=(5019017916556908693/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13421326984358898751/13423125000000000000 : ℝ)*(X 1 0+X 2 0)+(843591012223/429540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (3413/100000 : ℝ)) (hi := (2489/10000 : ℝ)) (c := (13421326984358898751/13423125000000000000 : ℝ)) (alpha := (843591012223/429540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13421326984358898751/13423125000000000000 : ℝ)*(X 0 1+X 2 1)+(843591012223/429540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (3413/100000 : ℝ)) (hi := (2489/10000 : ℝ)) (c := (13421326984358898751/13423125000000000000 : ℝ)) (alpha := (843591012223/429540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13421326984358898751/13423125000000000000 : ℝ)*(X 0 2+X 1 2)+(843591012223/429540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (3413/100000 : ℝ)) (hi := (2489/10000 : ℝ)) (c := (13421326984358898751/13423125000000000000 : ℝ)) (alpha := (843591012223/429540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-222312197/1250000000 : ℝ)*X 0 0+(2770589419/5000000000 : ℝ)*X 0 1+(2560097317/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378312399/10000000000 : ℝ)*X 1 0+(-31233769/156250000 : ℝ)*X 1 1+(5120194611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378312359/10000000000 : ℝ)*X 2 0+(2560097431/5000000000 : ℝ)*X 2 1+(-1998960941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2116232353/5000000000 : ℝ)*X 0 0+(3762667957/10000000000 : ℝ)*X 0 1+(4748985337/10000000000 : ℝ)*X 0 2+(2116232353/5000000000 : ℝ)*X 1 0+(3762667957/10000000000 : ℝ)*X 1 1+(4748985337/10000000000 : ℝ)*X 1 2+(2116232353/5000000000 : ℝ)*X 2 0+(3762667957/10000000000 : ℝ)*X 2 1+(4748985337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-889361579/5000000000 : ℝ)*X 0 0+(5124602937/10000000000 : ℝ)*X 0 1+(2768352281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053368999/2000000000 : ℝ)*X 1 0+(-316490823/2000000000 : ℝ)*X 1 1+(2768351709/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053369461/2000000000 : ℝ)*X 2 0+(1384175681/2500000000 : ℝ)*X 2 1+(-1582451851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4232994019/10000000000 : ℝ)*X 0 0+(592331873/1250000000 : ℝ)*X 0 1+(1886576199/5000000000 : ℝ)*X 0 2+(4232994019/10000000000 : ℝ)*X 1 0+(592331873/1250000000 : ℝ)*X 1 1+(1886576199/5000000000 : ℝ)*X 1 2+(4232994019/10000000000 : ℝ)*X 2 0+(592331873/1250000000 : ℝ)*X 2 1+(1886576199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104836065676503316629508209/55929687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (15922619/25000000000000 : ℝ)*(base1) + (10490347/2000000000000 : ℝ)*(base19) + (257138129/50000000000000 : ℝ)*(base23) + (117236409/100000000000000 : ℝ)*(upper5) + (847318042801707/50000000000000 : ℝ)*(major0) + (847318042801707/50000000000000 : ℝ)*(major1) + (847318042801707/50000000000000 : ℝ)*(major2) + (237538966675029/10000000000000 : ℝ)*(sp0) + (148462144351961/6250000000000 : ℝ)*(sp1) + (1187697339073781/50000000000000 : ℝ)*(sp2) + (126734371405923/12500000000000 : ℝ)*(sp3) + (2794682003/50000000000000 : ℝ)*(sp4) + (358275093/100000000000000 : ℝ)*(sp5) + (75254571/4000000000000 : ℝ)*(sp7) + (202775383260427/20000000000000 : ℝ)*(f.failure) + (118769759621191/5000000000000 : ℝ)*(f.sum) + (2129517340111/1431800000000000000000000000 : ℝ)*base65 + (606290392180270569/223718750000000000000000000000000 : ℝ)*base67 + (262612954952229431/223718750000000000000000000000000 : ℝ)*base70 + (732172199363958069/223718750000000000000000000000000 : ℝ)*base71 + (19520108842631/7159000000000000000000000000 : ℝ)*base73 + (852771912450833069/223718750000000000000000000000000 : ℝ)*base75 + (357310863968573181/223718750000000000000000000000000 : ℝ)*base78 + (529738802039083069/223718750000000000000000000000000 : ℝ)*base79 + (1360381216923/715900000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1937601/2000000000000000000000 : ℝ)*base89 + (1937601/2000000000000000000000 : ℝ)*base91 + (1937601/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94114666554937657614261429/22371875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415410467/100000000000000 : ℝ)*(base19) + (4422319/312500000000 : ℝ)*(base23) + (1085187/800000000000 : ℝ)*(lower2) + (15335773/5000000000000 : ℝ)*(upper5) + (173116650010179/10000000000000 : ℝ)*(major0) + (173116650010179/10000000000000 : ℝ)*(major1) + (173116650010179/10000000000000 : ℝ)*(major2) + (442693239/20000000000000 : ℝ)*(sp0) + (9119196577/100000000000000 : ℝ)*(sp2) + (574870701/50000000000000 : ℝ)*(sp3) + (303324762176961/12500000000000 : ℝ)*(sp4) + (303324986933927/12500000000000 : ℝ)*(sp5) + (1213294888271613/50000000000000 : ℝ)*(sp6) + (517865699676317/50000000000000 : ℝ)*(sp7) + (258933137273509/25000000000000 : ℝ)*(f.failure) + (1213300155440941/50000000000000 : ℝ)*(f.sum) + (174256920981/111859375000000000000000000 : ℝ)*base65 + (242399569393594107/44743750000000000000000000000000 : ℝ)*base68 + (209292078396744107/44743750000000000000000000000000 : ℝ)*base70 + (3369968102793393/44743750000000000000000000000000 : ℝ)*base71 + (297552878171/89487500000000000000000000 : ℝ)*base74 + (538119875001231607/44743750000000000000000000000000 : ℝ)*base76 + (192254001619499643/44743750000000000000000000000000 : ℝ)*base77 + (449307105113519107/44743750000000000000000000000000 : ℝ)*base80 + (5693548069767/7159000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13877967/2500000000000000000000 : ℝ)*base89 + (13877967/2500000000000000000000 : ℝ)*base91 + (13877967/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1559_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2489/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (559/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17857/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1559_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1559_s2_0 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1798110297/10000000000 : ℝ)*x 0 + (5444278547/10000000000 : ℝ)*x 1 + (2602164287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1798110297/10000000000 : ℝ)^4615 ≤ (11023556592279/100000000000000 : ℝ)^3591 := by
    have hnat : (1798110297 : ℕ)^4615*100000000000000^3591 ≤ 11023556592279^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798110297 10000000000 11023556592279 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444278547/10000000000 : ℝ)^4615 ≤ (45776415927257/100000000000000 : ℝ)^3591 := by
    have hnat : (5444278547 : ℕ)^4615*100000000000000^3591 ≤ 45776415927257^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444278547 10000000000 45776415927257 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602164287/5000000000 : ℝ)^4615 ≤ (21600013736893/50000000000000 : ℝ)^3591 := by
    have hnat : (2602164287 : ℕ)^4615*50000000000000^3591 ≤ 21600013736893^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602164287 5000000000 21600013736893 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1798110297/10000000000 : ℝ), (5444278547/10000000000 : ℝ), (2602164287/5000000000 : ℝ)] ![(11023556592279/100000000000000 : ℝ), (45776415927257/100000000000000 : ℝ), (21600013736893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1798110297/10000000000 : ℝ)|^4615 ≤ (11023556592279/100000000000000 : ℝ)^3591
        have hw : |(-1798110297/10000000000 : ℝ)|=(1798110297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444278547/10000000000 : ℝ)|^4615 ≤ (45776415927257/100000000000000 : ℝ)^3591
        have hw : |(5444278547/10000000000 : ℝ)|=(5444278547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602164287/5000000000 : ℝ)|^4615 ≤ (21600013736893/50000000000000 : ℝ)^3591
        have hw : |(2602164287/5000000000 : ℝ)|=(2602164287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_1 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353356569/10000000000 : ℝ)*x 0 + (-960663743/5000000000 : ℝ)*x 1 + (520432819/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353356569/10000000000 : ℝ)^4615 ≤ (699941846201/1562500000000 : ℝ)^3591 := by
    have hnat : (5353356569 : ℕ)^4615*1562500000000^3591 ≤ 699941846201^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353356569 10000000000 699941846201 1562500000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960663743/5000000000 : ℝ)^4615 ≤ (12003698453001/100000000000000 : ℝ)^3591 := by
    have hnat : (960663743 : ℕ)^4615*100000000000000^3591 ≤ 12003698453001^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960663743 5000000000 12003698453001 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520432819/1000000000 : ℝ)^4615 ≤ (675000365271/1562500000000 : ℝ)^3591 := by
    have hnat : (520432819 : ℕ)^4615*1562500000000^3591 ≤ 675000365271^3591*1000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520432819 1000000000 675000365271 1562500000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353356569/10000000000 : ℝ), (-960663743/5000000000 : ℝ), (520432819/1000000000 : ℝ)] ![(699941846201/1562500000000 : ℝ), (12003698453001/100000000000000 : ℝ), (675000365271/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353356569/10000000000 : ℝ)|^4615 ≤ (699941846201/1562500000000 : ℝ)^3591
        have hw : |(5353356569/10000000000 : ℝ)|=(5353356569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960663743/5000000000 : ℝ)|^4615 ≤ (12003698453001/100000000000000 : ℝ)^3591
        have hw : |(-960663743/5000000000 : ℝ)|=(960663743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520432819/1000000000 : ℝ)|^4615 ≤ (675000365271/1562500000000 : ℝ)^3591
        have hw : |(520432819/1000000000 : ℝ)|=(520432819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_2 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353356407/10000000000 : ℝ)*x 0 + (5204328181/10000000000 : ℝ)*x 1 + (-384265543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353356407/10000000000 : ℝ)^4615 ≤ (11199069103677/25000000000000 : ℝ)^3591 := by
    have hnat : (5353356407 : ℕ)^4615*25000000000000^3591 ≤ 11199069103677^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353356407 10000000000 11199069103677 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204328181/10000000000 : ℝ)^4615 ≤ (43200023281333/100000000000000 : ℝ)^3591 := by
    have hnat : (5204328181 : ℕ)^4615*100000000000000^3591 ≤ 43200023281333^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204328181 10000000000 43200023281333 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384265543/2000000000 : ℝ)^4615 ≤ (6001850145839/50000000000000 : ℝ)^3591 := by
    have hnat : (384265543 : ℕ)^4615*50000000000000^3591 ≤ 6001850145839^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384265543 2000000000 6001850145839 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353356407/10000000000 : ℝ), (5204328181/10000000000 : ℝ), (-384265543/2000000000 : ℝ)] ![(11199069103677/25000000000000 : ℝ), (43200023281333/100000000000000 : ℝ), (6001850145839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353356407/10000000000 : ℝ)|^4615 ≤ (11199069103677/25000000000000 : ℝ)^3591
        have hw : |(5353356407/10000000000 : ℝ)|=(5353356407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204328181/10000000000 : ℝ)|^4615 ≤ (43200023281333/100000000000000 : ℝ)^3591
        have hw : |(5204328181/10000000000 : ℝ)|=(5204328181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384265543/2000000000 : ℝ)|^4615 ≤ (6001850145839/50000000000000 : ℝ)^3591
        have hw : |(-384265543/2000000000 : ℝ)|=(384265543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_3 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246654593/10000000000 : ℝ)*x 0 + (3973160749/10000000000 : ℝ)*x 1 + (4535338357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246654593/10000000000 : ℝ)^4615 ≤ (33264560801861/100000000000000 : ℝ)^3591 := by
    have hnat : (4246654593 : ℕ)^4615*100000000000000^3591 ≤ 33264560801861^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246654593 10000000000 33264560801861 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3973160749/10000000000 : ℝ)^4615 ≤ (15268517408651/50000000000000 : ℝ)^3591 := by
    have hnat : (3973160749 : ℕ)^4615*50000000000000^3591 ≤ 15268517408651^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973160749 10000000000 15268517408651 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535338357/10000000000 : ℝ)^4615 ≤ (9049601092101/25000000000000 : ℝ)^3591 := by
    have hnat : (4535338357 : ℕ)^4615*25000000000000^3591 ≤ 9049601092101^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535338357 10000000000 9049601092101 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246654593/10000000000 : ℝ), (3973160749/10000000000 : ℝ), (4535338357/10000000000 : ℝ)] ![(33264560801861/100000000000000 : ℝ), (15268517408651/50000000000000 : ℝ), (9049601092101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246654593/10000000000 : ℝ)|^4615 ≤ (33264560801861/100000000000000 : ℝ)^3591
        have hw : |(4246654593/10000000000 : ℝ)|=(4246654593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3973160749/10000000000 : ℝ)|^4615 ≤ (15268517408651/50000000000000 : ℝ)^3591
        have hw : |(3973160749/10000000000 : ℝ)|=(3973160749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535338357/10000000000 : ℝ)|^4615 ≤ (9049601092101/25000000000000 : ℝ)^3591
        have hw : |(4535338357/10000000000 : ℝ)|=(4535338357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_4 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14385213/80000000 : ℝ)*x 0 + (325360551/625000000 : ℝ)*x 1 + (1360706613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14385213/80000000 : ℝ)^4615 ≤ (688992638101/6250000000000 : ℝ)^3591 := by
    have hnat : (14385213 : ℕ)^4615*6250000000000^3591 ≤ 688992638101^3591*80000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14385213 80000000 688992638101 6250000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325360551/625000000 : ℝ)^4615 ≤ (10803848080033/25000000000000 : ℝ)^3591 := by
    have hnat : (325360551 : ℕ)^4615*25000000000000^3591 ≤ 10803848080033^3591*625000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325360551 625000000 10803848080033 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360706613/2500000000 : ℝ)^4615 ≤ (45760725446059/100000000000000 : ℝ)^3591 := by
    have hnat : (1360706613 : ℕ)^4615*100000000000000^3591 ≤ 45760725446059^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360706613 2500000000 45760725446059 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14385213/80000000 : ℝ), (325360551/625000000 : ℝ), (1360706613/2500000000 : ℝ)] ![(688992638101/6250000000000 : ℝ), (10803848080033/25000000000000 : ℝ), (45760725446059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14385213/80000000 : ℝ)|^4615 ≤ (688992638101/6250000000000 : ℝ)^3591
        have hw : |(-14385213/80000000 : ℝ)|=(14385213/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325360551/625000000 : ℝ)|^4615 ≤ (10803848080033/25000000000000 : ℝ)^3591
        have hw : |(325360551/625000000 : ℝ)|=(325360551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360706613/2500000000 : ℝ)|^4615 ≤ (45760725446059/100000000000000 : ℝ)^3591
        have hw : |(1360706613/2500000000 : ℝ)|=(1360706613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_5 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289950079/10000000000 : ℝ)*x 0 + (-420707469/2500000000 : ℝ)*x 1 + (5442826767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289950079/10000000000 : ℝ)^4615 ≤ (44115556353763/100000000000000 : ℝ)^3591 := by
    have hnat : (5289950079 : ℕ)^4615*100000000000000^3591 ≤ 44115556353763^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289950079 10000000000 44115556353763 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420707469/2500000000 : ℝ)^4615 ≤ (3163660871/31250000000 : ℝ)^3591 := by
    have hnat : (420707469 : ℕ)^4615*31250000000^3591 ≤ 3163660871^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420707469 2500000000 3163660871 31250000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442826767/10000000000 : ℝ)^4615 ≤ (22880364424817/50000000000000 : ℝ)^3591 := by
    have hnat : (5442826767 : ℕ)^4615*50000000000000^3591 ≤ 22880364424817^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442826767 10000000000 22880364424817 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289950079/10000000000 : ℝ), (-420707469/2500000000 : ℝ), (5442826767/10000000000 : ℝ)] ![(44115556353763/100000000000000 : ℝ), (3163660871/31250000000 : ℝ), (22880364424817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289950079/10000000000 : ℝ)|^4615 ≤ (44115556353763/100000000000000 : ℝ)^3591
        have hw : |(5289950079/10000000000 : ℝ)|=(5289950079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420707469/2500000000 : ℝ)|^4615 ≤ (3163660871/31250000000 : ℝ)^3591
        have hw : |(-420707469/2500000000 : ℝ)|=(420707469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442826767/10000000000 : ℝ)|^4615 ≤ (22880364424817/50000000000000 : ℝ)^3591
        have hw : |(5442826767/10000000000 : ℝ)|=(5442826767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_6 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330621881/625000000 : ℝ)*x 0 + (340176751/625000000 : ℝ)*x 1 + (-1682828107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330621881/625000000 : ℝ)^4615 ≤ (44115556535961/100000000000000 : ℝ)^3591 := by
    have hnat : (330621881 : ℕ)^4615*100000000000000^3591 ≤ 44115556535961^3591*625000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330621881 625000000 44115556535961 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340176751/625000000 : ℝ)^4615 ≤ (22880371172539/50000000000000 : ℝ)^3591 := by
    have hnat : (340176751 : ℕ)^4615*50000000000000^3591 ≤ 22880371172539^3591*625000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340176751 625000000 22880371172539 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1682828107/10000000000 : ℝ)^4615 ≤ (10123701110423/100000000000000 : ℝ)^3591 := by
    have hnat : (1682828107 : ℕ)^4615*100000000000000^3591 ≤ 10123701110423^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682828107 10000000000 10123701110423 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330621881/625000000 : ℝ), (340176751/625000000 : ℝ), (-1682828107/10000000000 : ℝ)] ![(44115556535961/100000000000000 : ℝ), (22880371172539/50000000000000 : ℝ), (10123701110423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330621881/625000000 : ℝ)|^4615 ≤ (44115556535961/100000000000000 : ℝ)^3591
        have hw : |(330621881/625000000 : ℝ)|=(330621881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340176751/625000000 : ℝ)|^4615 ≤ (22880371172539/50000000000000 : ℝ)^3591
        have hw : |(340176751/625000000 : ℝ)|=(340176751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1682828107/10000000000 : ℝ)|^4615 ≤ (10123701110423/100000000000000 : ℝ)^3591
        have hw : |(-1682828107/10000000000 : ℝ)|=(1682828107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s2_7 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246752547/10000000000 : ℝ)*x 0 + (4531963479/10000000000 : ℝ)*x 1 + (2485353/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246752547/10000000000 : ℝ)^4615 ≤ (4158193360973/12500000000000 : ℝ)^3591 := by
    have hnat : (4246752547 : ℕ)^4615*12500000000000^3591 ≤ 4158193360973^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246752547 10000000000 4158193360973 12500000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531963479/10000000000 : ℝ)^4615 ≤ (3616379066847/10000000000000 : ℝ)^3591 := by
    have hnat : (4531963479 : ℕ)^4615*10000000000000^3591 ≤ 3616379066847^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531963479 10000000000 3616379066847 10000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2485353/6250000 : ℝ)^4615 ≤ (7642665609183/25000000000000 : ℝ)^3591 := by
    have hnat : (2485353 : ℕ)^4615*25000000000000^3591 ≤ 7642665609183^3591*6250000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485353 6250000 7642665609183 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246752547/10000000000 : ℝ), (4531963479/10000000000 : ℝ), (2485353/6250000 : ℝ)] ![(4158193360973/12500000000000 : ℝ), (3616379066847/10000000000000 : ℝ), (7642665609183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246752547/10000000000 : ℝ)|^4615 ≤ (4158193360973/12500000000000 : ℝ)^3591
        have hw : |(4246752547/10000000000 : ℝ)|=(4246752547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531963479/10000000000 : ℝ)|^4615 ≤ (3616379066847/10000000000000 : ℝ)^3591
        have hw : |(4531963479/10000000000 : ℝ)|=(4531963479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2485353/6250000 : ℝ)|^4615 ≤ (7642665609183/25000000000000 : ℝ)^3591
        have hw : |(2485353/6250000 : ℝ)|=(2485353/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1559_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2689/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7921/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (559/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (559/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (559/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (559/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (559/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (559/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (559/6250 : ℝ) ^ (4613/1024 : ℝ) ≤ (472839329080239/25000000000000000000 : ℝ) := by
    have hpowers : (559/6250 : ℝ)^4613 ≤ (472839329080239/25000000000000000000 : ℝ)^1024 := by
      have hnat : (559 : ℕ)^4613*25000000000000000000^1024 ≤ 472839329080239^1024*6250^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        559 6250 472839329080239 25000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (559/6250 : ℝ)) (X := (472839329080239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17857/100000 : ℝ) ^ (4613/1024 : ℝ) ≤ (10651848322767369/25000000000000000000 : ℝ) := by
    have hpowers : (17857/100000 : ℝ)^4613 ≤ (10651848322767369/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17857 : ℕ)^4613*25000000000000000000^1024 ≤ 10651848322767369^1024*100000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17857 100000 10651848322767369 25000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17857/100000 : ℝ)) (X := (10651848322767369/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500472839329080239/12500000000000000000 : ℝ) ≤ (2000016793595431/2000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (12500472839329080239/12500000000000000000 : ℝ)^1024 ≤ (2000016793595431/2000000000000000 : ℝ)^4613 := by
      have hnat : (12500472839329080239 : ℕ)^1024*2000000000000000^4613 ≤ 2000016793595431^4613*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500472839329080239 12500000000000000000 2000016793595431 2000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016793595431/2000000000000000 : ℝ)) (X := (12500472839329080239/12500000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126390585956480951/3125000000000000000 : ℝ) ≤ (2000197523671827/2000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (3126390585956480951/3125000000000000000 : ℝ)^1024 ≤ (2000197523671827/2000000000000000 : ℝ)^4613 := by
      have hnat : (3126390585956480951 : ℕ)^1024*2000000000000000^4613 ≤ 2000197523671827^4613*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126390585956480951 3125000000000000000 2000197523671827 2000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000197523671827/2000000000000000 : ℝ)) (X := (3126390585956480951/3125000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510651848322767369/12500000000000000000 : ℝ) ≤ (2000378253748223/2000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (12510651848322767369/12500000000000000000 : ℝ)^1024 ≤ (2000378253748223/2000000000000000 : ℝ)^4613 := by
      have hnat : (12510651848322767369 : ℕ)^1024*2000000000000000^4613 ≤ 2000378253748223^4613*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510651848322767369 12500000000000000000 2000378253748223 2000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000378253748223/2000000000000000 : ℝ)) (X := (12510651848322767369/12500000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(472839329080239/25000000000000000000 : ℝ) ≤ ((3564583356341900971/3565200000000000000 : ℝ)+2*(45182519099/44565000000000 : ℝ)*(559/6250 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (3564583356341900971/3565200000000000000 : ℝ)+2*(45182519099/44565000000000 : ℝ)*(559/6250 : ℝ)=(2000016793595431/2000000000000000 : ℝ) by norm_num, show 1+2*(472839329080239/25000000000000000000 : ℝ)=(12500472839329080239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10651848322767369/25000000000000000000 : ℝ)+(472839329080239/25000000000000000000 : ℝ) ≤ ((3564583356341900971/3565200000000000000 : ℝ)+(45182519099/44565000000000 : ℝ)*((17857/100000 : ℝ)+(559/6250 : ℝ)))^(4613/1024 : ℝ) := by
    rw [show (3564583356341900971/3565200000000000000 : ℝ)+(45182519099/44565000000000 : ℝ)*((17857/100000 : ℝ)+(559/6250 : ℝ))=(2000197523671827/2000000000000000 : ℝ) by norm_num, show 1+(10651848322767369/25000000000000000000 : ℝ)+(472839329080239/25000000000000000000 : ℝ)=(3126390585956480951/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10651848322767369/25000000000000000000 : ℝ) ≤ ((3564583356341900971/3565200000000000000 : ℝ)+2*(45182519099/44565000000000 : ℝ)*(17857/100000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (3564583356341900971/3565200000000000000 : ℝ)+2*(45182519099/44565000000000 : ℝ)*(17857/100000 : ℝ)=(2000378253748223/2000000000000000 : ℝ) by norm_num, show 1+2*(10651848322767369/25000000000000000000 : ℝ)=(12510651848322767369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3564583356341900971/3565200000000000000 : ℝ)*(X 1 0+X 2 0)+(45182519099/44565000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (559/6250 : ℝ)) (hi := (17857/100000 : ℝ)) (c := (3564583356341900971/3565200000000000000 : ℝ)) (alpha := (45182519099/44565000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3564583356341900971/3565200000000000000 : ℝ)*(X 0 1+X 2 1)+(45182519099/44565000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (559/6250 : ℝ)) (hi := (17857/100000 : ℝ)) (c := (3564583356341900971/3565200000000000000 : ℝ)) (alpha := (45182519099/44565000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3564583356341900971/3565200000000000000 : ℝ)*(X 0 2+X 1 2)+(45182519099/44565000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (559/6250 : ℝ)) (hi := (17857/100000 : ℝ)) (c := (3564583356341900971/3565200000000000000 : ℝ)) (alpha := (45182519099/44565000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1798110297/10000000000 : ℝ)*X 0 0+(5444278547/10000000000 : ℝ)*X 0 1+(2602164287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353356569/10000000000 : ℝ)*X 1 0+(-960663743/5000000000 : ℝ)*X 1 1+(520432819/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353356407/10000000000 : ℝ)*X 2 0+(5204328181/10000000000 : ℝ)*X 2 1+(-384265543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4246654593/10000000000 : ℝ)*X 0 0+(3973160749/10000000000 : ℝ)*X 0 1+(4535338357/10000000000 : ℝ)*X 0 2+(4246654593/10000000000 : ℝ)*X 1 0+(3973160749/10000000000 : ℝ)*X 1 1+(4535338357/10000000000 : ℝ)*X 1 2+(4246654593/10000000000 : ℝ)*X 2 0+(3973160749/10000000000 : ℝ)*X 2 1+(4535338357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-14385213/80000000 : ℝ)*X 0 0+(325360551/625000000 : ℝ)*X 0 1+(1360706613/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289950079/10000000000 : ℝ)*X 1 0+(-420707469/2500000000 : ℝ)*X 1 1+(5442826767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330621881/625000000 : ℝ)*X 2 0+(340176751/625000000 : ℝ)*X 2 1+(-1682828107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4246752547/10000000000 : ℝ)*X 0 0+(4531963479/10000000000 : ℝ)*X 0 1+(2485353/6250000 : ℝ)*X 0 2+(4246752547/10000000000 : ℝ)*X 1 0+(4531963479/10000000000 : ℝ)*X 1 1+(2485353/6250000 : ℝ)*X 1 2+(4246752547/10000000000 : ℝ)*X 2 0+(4531963479/10000000000 : ℝ)*X 2 1+(2485353/6250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107405692824998235496514103/11884000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1550660139/100000000000000 : ℝ)*(base19) + (1311191853/100000000000000 : ℝ)*(base23) + (60681449/100000000000000 : ℝ)*(lower2) + (7494877/2000000000000 : ℝ)*(upper3) + (64782689/100000000000000 : ℝ)*(upper5) + (594637826602107/20000000000000 : ℝ)*(major0) + (594637826602107/20000000000000 : ℝ)*(major1) + (594637826602107/20000000000000 : ℝ)*(major2) + (4167551999493047/100000000000000 : ℝ)*(sp0) + (2083779603229587/50000000000000 : ℝ)*(sp1) + (208377972296373/5000000000000 : ℝ)*(sp2) + (889402837769073/50000000000000 : ℝ)*(sp3) + (8757626267/100000000000000 : ℝ)*(sp4) + (1441512783/12500000000000 : ℝ)*(sp7) + (177881720764041/10000000000000 : ℝ)*(f.failure) + (2083780378559657/50000000000000 : ℝ)*(f.sum) + (4357767903243/742750000000000000000000000 : ℝ)*base66 + (57423874979492701/23768000000000000000000000000000 : ℝ)*base68 + (182399699310083299/23768000000000000000000000000000 : ℝ)*base69 + (3964481423939299/23768000000000000000000000000000 : ℝ)*base71 + (9180287990623/1485500000000000000000000000 : ℝ)*base74 + (216666609650419299/23768000000000000000000000000000 : ℝ)*base75 + (36085126558412701/23768000000000000000000000000000 : ℝ)*base78 + (128658228986035299/23768000000000000000000000000000 : ℝ)*base79 + (1993601153929/1485500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3442683/1000000000000000000000 : ℝ)*base89 + (3442683/1000000000000000000000 : ℝ)*base91 + (3442683/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48534885521956711489110689/3713750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7503663/12500000000000 : ℝ)*(base19) + (994948979/100000000000000 : ℝ)*(base23) + (1213429/5000000000000 : ℝ)*(lower2) + (80117697/50000000000000 : ℝ)*(upper3) + (263552797/100000000000000 : ℝ)*(lower4) + (121973637/100000000000000 : ℝ)*(upper5) + (188090312003597/6250000000000 : ℝ)*(major0) + (188090312003597/6250000000000 : ℝ)*(major1) + (188090312003597/6250000000000 : ℝ)*(major2) + (4891318657/12500000000000 : ℝ)*(sp2) + (33747047765699/800000000000 : ℝ)*(sp4) + (4218380910683071/100000000000000 : ℝ)*(sp5) + (210917042260707/5000000000000 : ℝ)*(sp6) + (225063572221301/12500000000000 : ℝ)*(sp7) + (225063572221301/12500000000000 : ℝ)*(f.failure) + (33747047765699/800000000000 : ℝ)*(f.sum) + (21335859706279/8913000000000000000000000000 : ℝ)*base65 + (137550473944492687/22282500000000000000000000000000 : ℝ)*base67 + (123185960761282687/22282500000000000000000000000000 : ℝ)*base69 + (29119052623770187/22282500000000000000000000000000 : ℝ)*base71 + (11634895115219/2228250000000000000000000000 : ℝ)*base74 + (52799599634430187/22282500000000000000000000000000 : ℝ)*base75 + (102877959701272687/22282500000000000000000000000000 : ℝ)*base77 + (123280057352272687/22282500000000000000000000000000 : ℝ)*base79 + (3003713354837/2228250000000000000000000000 : ℝ)*base82 + (6416063/1250000000000000000000 : ℝ)*base89 + (6416063/1250000000000000000000 : ℝ)*base91 + (6416063/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1559_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1559_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1559_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1559_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1559_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1559_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1559_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
