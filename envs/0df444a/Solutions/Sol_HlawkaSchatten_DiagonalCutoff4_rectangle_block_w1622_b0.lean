-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1622_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:21.026511+00:00
-- url     : https://prove2.me/submissions/3e978b54-41c4-4e4d-8c40-9527d66b3ab0

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
theorem support_rectangle_w1622_s0_0 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1543086897/10000000000 : ℝ)*x 0 + (29105437/50000000 : ℝ)*x 1 + (980373989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1543086897/10000000000 : ℝ)^4807 ≤ (9304651791857/100000000000000 : ℝ)^3783 := by
    have hnat : (1543086897 : ℕ)^4807*100000000000000^3783 ≤ 9304651791857^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543086897 10000000000 9304651791857 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29105437/50000000 : ℝ)^4807 ≤ (25139946476177/50000000000000 : ℝ)^3783 := by
    have hnat : (29105437 : ℕ)^4807*50000000000000^3783 ≤ 25139946476177^3783*50000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29105437 50000000 25139946476177 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980373989/2000000000 : ℝ)^4807 ≤ (5051931904727/12500000000000 : ℝ)^3783 := by
    have hnat : (980373989 : ℕ)^4807*12500000000000^3783 ≤ 5051931904727^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980373989 2000000000 5051931904727 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1543086897/10000000000 : ℝ), (29105437/50000000 : ℝ), (980373989/2000000000 : ℝ)] ![(9304651791857/100000000000000 : ℝ), (25139946476177/50000000000000 : ℝ), (5051931904727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1543086897/10000000000 : ℝ)|^4807 ≤ (9304651791857/100000000000000 : ℝ)^3783
        have hw : |(-1543086897/10000000000 : ℝ)|=(1543086897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29105437/50000000 : ℝ)|^4807 ≤ (25139946476177/50000000000000 : ℝ)^3783
        have hw : |(29105437/50000000 : ℝ)|=(29105437/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(980373989/2000000000 : ℝ)|^4807 ≤ (5051931904727/12500000000000 : ℝ)^3783
        have hw : |(980373989/2000000000 : ℝ)|=(980373989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_1 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5448797853/10000000000 : ℝ)*x 0 + (-2050674551/10000000000 : ℝ)*x 1 + (980374079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5448797853/10000000000 : ℝ)^4807 ≤ (23114864337087/50000000000000 : ℝ)^3783 := by
    have hnat : (5448797853 : ℕ)^4807*50000000000000^3783 ≤ 23114864337087^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448797853 10000000000 23114864337087 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050674551/10000000000 : ℝ)^4807 ≤ (13354811359239/100000000000000 : ℝ)^3783 := by
    have hnat : (2050674551 : ℕ)^4807*100000000000000^3783 ≤ 13354811359239^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050674551 10000000000 13354811359239 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980374079/2000000000 : ℝ)^4807 ≤ (126298312351/312500000000 : ℝ)^3783 := by
    have hnat : (980374079 : ℕ)^4807*312500000000^3783 ≤ 126298312351^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980374079 2000000000 126298312351 312500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5448797853/10000000000 : ℝ), (-2050674551/10000000000 : ℝ), (980374079/2000000000 : ℝ)] ![(23114864337087/50000000000000 : ℝ), (13354811359239/100000000000000 : ℝ), (126298312351/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5448797853/10000000000 : ℝ)|^4807 ≤ (23114864337087/50000000000000 : ℝ)^3783
        have hw : |(5448797853/10000000000 : ℝ)|=(5448797853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050674551/10000000000 : ℝ)|^4807 ≤ (13354811359239/100000000000000 : ℝ)^3783
        have hw : |(-2050674551/10000000000 : ℝ)|=(2050674551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(980374079/2000000000 : ℝ)|^4807 ≤ (126298312351/312500000000 : ℝ)^3783
        have hw : |(980374079/2000000000 : ℝ)|=(980374079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_2 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089759517/2000000000 : ℝ)*x 0 + (2450935107/5000000000 : ℝ)*x 1 + (-256334391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089759517/2000000000 : ℝ)^4807 ≤ (4622972578487/10000000000000 : ℝ)^3783 := by
    have hnat : (1089759517 : ℕ)^4807*10000000000000^3783 ≤ 4622972578487^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089759517 2000000000 4622972578487 10000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2450935107/5000000000 : ℝ)^4807 ≤ (40415458056041/100000000000000 : ℝ)^3783 := by
    have hnat : (2450935107 : ℕ)^4807*100000000000000^3783 ≤ 40415458056041^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450935107 5000000000 40415458056041 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256334391/1250000000 : ℝ)^4807 ≤ (13354816134033/100000000000000 : ℝ)^3783 := by
    have hnat : (256334391 : ℕ)^4807*100000000000000^3783 ≤ 13354816134033^3783*1250000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256334391 1250000000 13354816134033 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089759517/2000000000 : ℝ), (2450935107/5000000000 : ℝ), (-256334391/1250000000 : ℝ)] ![(4622972578487/10000000000000 : ℝ), (40415458056041/100000000000000 : ℝ), (13354816134033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089759517/2000000000 : ℝ)|^4807 ≤ (4622972578487/10000000000000 : ℝ)^3783
        have hw : |(1089759517/2000000000 : ℝ)|=(1089759517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2450935107/5000000000 : ℝ)|^4807 ≤ (40415458056041/100000000000000 : ℝ)^3783
        have hw : |(2450935107/5000000000 : ℝ)|=(2450935107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256334391/1250000000 : ℝ)|^4807 ≤ (13354816134033/100000000000000 : ℝ)^3783
        have hw : |(-256334391/1250000000 : ℝ)|=(256334391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_3 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2051967041/5000000000 : ℝ)*x 0 + (615283933/2000000000 : ℝ)*x 1 + (5370985287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051967041/5000000000 : ℝ)^4807 ≤ (32247767865593/100000000000000 : ℝ)^3783 := by
    have hnat : (2051967041 : ℕ)^4807*100000000000000^3783 ≤ 32247767865593^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051967041 5000000000 32247767865593 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615283933/2000000000 : ℝ)^4807 ≤ (22359772455819/100000000000000 : ℝ)^3783 := by
    have hnat : (615283933 : ℕ)^4807*100000000000000^3783 ≤ 22359772455819^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615283933 2000000000 22359772455819 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5370985287/10000000000 : ℝ)^4807 ≤ (22696229829053/50000000000000 : ℝ)^3783 := by
    have hnat : (5370985287 : ℕ)^4807*50000000000000^3783 ≤ 22696229829053^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370985287 10000000000 22696229829053 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2051967041/5000000000 : ℝ), (615283933/2000000000 : ℝ), (5370985287/10000000000 : ℝ)] ![(32247767865593/100000000000000 : ℝ), (22359772455819/100000000000000 : ℝ), (22696229829053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2051967041/5000000000 : ℝ)|^4807 ≤ (32247767865593/100000000000000 : ℝ)^3783
        have hw : |(2051967041/5000000000 : ℝ)|=(2051967041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615283933/2000000000 : ℝ)|^4807 ≤ (22359772455819/100000000000000 : ℝ)^3783
        have hw : |(615283933/2000000000 : ℝ)|=(615283933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5370985287/10000000000 : ℝ)|^4807 ≤ (22696229829053/50000000000000 : ℝ)^3783
        have hw : |(5370985287/10000000000 : ℝ)|=(5370985287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_4 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1545721777/10000000000 : ℝ)*x 0 + (7695317/15625000 : ℝ)*x 1 + (5797138743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1545721777/10000000000 : ℝ)^4807 ≤ (9324845155989/100000000000000 : ℝ)^3783 := by
    have hnat : (1545721777 : ℕ)^4807*100000000000000^3783 ≤ 9324845155989^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545721777 10000000000 9324845155989 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7695317/15625000 : ℝ)^4807 ≤ (40657966097121/100000000000000 : ℝ)^3783 := by
    have hnat : (7695317 : ℕ)^4807*100000000000000^3783 ≤ 40657966097121^3783*15625000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7695317 15625000 40657966097121 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5797138743/10000000000 : ℝ)^4807 ≤ (12504297184807/25000000000000 : ℝ)^3783 := by
    have hnat : (5797138743 : ℕ)^4807*25000000000000^3783 ≤ 12504297184807^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5797138743 10000000000 12504297184807 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1545721777/10000000000 : ℝ), (7695317/15625000 : ℝ), (5797138743/10000000000 : ℝ)] ![(9324845155989/100000000000000 : ℝ), (40657966097121/100000000000000 : ℝ), (12504297184807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1545721777/10000000000 : ℝ)|^4807 ≤ (9324845155989/100000000000000 : ℝ)^3783
        have hw : |(-1545721777/10000000000 : ℝ)|=(1545721777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7695317/15625000 : ℝ)|^4807 ≤ (40657966097121/100000000000000 : ℝ)^3783
        have hw : |(7695317/15625000 : ℝ)|=(7695317/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5797138743/10000000000 : ℝ)|^4807 ≤ (12504297184807/25000000000000 : ℝ)^3783
        have hw : |(5797138743/10000000000 : ℝ)|=(5797138743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_5 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197787263/10000000000 : ℝ)*x 0 + (-115540631/1000000000 : ℝ)*x 1 + (2898569371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197787263/10000000000 : ℝ)^4807 ≤ (21770326254213/50000000000000 : ℝ)^3783 := by
    have hnat : (5197787263 : ℕ)^4807*50000000000000^3783 ≤ 21770326254213^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197787263 10000000000 21770326254213 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115540631/1000000000 : ℝ)^4807 ≤ (6442158747311/100000000000000 : ℝ)^3783 := by
    have hnat : (115540631 : ℕ)^4807*100000000000000^3783 ≤ 6442158747311^3783*1000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115540631 1000000000 6442158747311 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2898569371/5000000000 : ℝ)^4807 ≤ (10003437745653/20000000000000 : ℝ)^3783 := by
    have hnat : (2898569371 : ℕ)^4807*20000000000000^3783 ≤ 10003437745653^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2898569371 5000000000 10003437745653 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197787263/10000000000 : ℝ), (-115540631/1000000000 : ℝ), (2898569371/5000000000 : ℝ)] ![(21770326254213/50000000000000 : ℝ), (6442158747311/100000000000000 : ℝ), (10003437745653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197787263/10000000000 : ℝ)|^4807 ≤ (21770326254213/50000000000000 : ℝ)^3783
        have hw : |(5197787263/10000000000 : ℝ)|=(5197787263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115540631/1000000000 : ℝ)|^4807 ≤ (6442158747311/100000000000000 : ℝ)^3783
        have hw : |(-115540631/1000000000 : ℝ)|=(115540631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2898569371/5000000000 : ℝ)|^4807 ≤ (10003437745653/20000000000000 : ℝ)^3783
        have hw : |(2898569371/5000000000 : ℝ)|=(2898569371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_6 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598893609/5000000000 : ℝ)*x 0 + (5797139157/10000000000 : ℝ)*x 1 + (-144425717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598893609/5000000000 : ℝ)^4807 ≤ (10885163007359/25000000000000 : ℝ)^3783 := by
    have hnat : (2598893609 : ℕ)^4807*25000000000000^3783 ≤ 10885163007359^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598893609 5000000000 10885163007359 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5797139157/10000000000 : ℝ)^4807 ≤ (6252149159757/12500000000000 : ℝ)^3783 := by
    have hnat : (5797139157 : ℕ)^4807*12500000000000^3783 ≤ 6252149159757^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5797139157 10000000000 6252149159757 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144425717/1250000000 : ℝ)^4807 ≤ (1610538670143/25000000000000 : ℝ)^3783 := by
    have hnat : (144425717 : ℕ)^4807*25000000000000^3783 ≤ 1610538670143^3783*1250000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144425717 1250000000 1610538670143 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598893609/5000000000 : ℝ), (5797139157/10000000000 : ℝ), (-144425717/1250000000 : ℝ)] ![(10885163007359/25000000000000 : ℝ), (6252149159757/12500000000000 : ℝ), (1610538670143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598893609/5000000000 : ℝ)|^4807 ≤ (10885163007359/25000000000000 : ℝ)^3783
        have hw : |(2598893609/5000000000 : ℝ)|=(2598893609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5797139157/10000000000 : ℝ)|^4807 ≤ (6252149159757/12500000000000 : ℝ)^3783
        have hw : |(5797139157/10000000000 : ℝ)|=(5797139157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-144425717/1250000000 : ℝ)|^4807 ≤ (1610538670143/25000000000000 : ℝ)^3783
        have hw : |(-144425717/1250000000 : ℝ)|=(144425717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s0_7 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4110511293/10000000000 : ℝ)*x 0 + (664154803/1250000000 : ℝ)*x 1 + (1568100679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4110511293/10000000000 : ℝ)^4807 ≤ (32313453892319/100000000000000 : ℝ)^3783 := by
    have hnat : (4110511293 : ℕ)^4807*100000000000000^3783 ≤ 32313453892319^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110511293 10000000000 32313453892319 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664154803/1250000000 : ℝ)^4807 ≤ (5596651950531/12500000000000 : ℝ)^3783 := by
    have hnat : (664154803 : ℕ)^4807*12500000000000^3783 ≤ 5596651950531^3783*1250000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664154803 1250000000 5596651950531 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568100679/5000000000 : ℝ)^4807 ≤ (22913330480803/100000000000000 : ℝ)^3783 := by
    have hnat : (1568100679 : ℕ)^4807*100000000000000^3783 ≤ 22913330480803^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568100679 5000000000 22913330480803 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4110511293/10000000000 : ℝ), (664154803/1250000000 : ℝ), (1568100679/5000000000 : ℝ)] ![(32313453892319/100000000000000 : ℝ), (5596651950531/12500000000000 : ℝ), (22913330480803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4110511293/10000000000 : ℝ)|^4807 ≤ (32313453892319/100000000000000 : ℝ)^3783
        have hw : |(4110511293/10000000000 : ℝ)|=(4110511293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(664154803/1250000000 : ℝ)|^4807 ≤ (5596651950531/12500000000000 : ℝ)^3783
        have hw : |(664154803/1250000000 : ℝ)|=(664154803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1568100679/5000000000 : ℝ)|^4807 ≤ (22913330480803/100000000000000 : ℝ)^3783
        have hw : |(1568100679/5000000000 : ℝ)|=(1568100679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1622_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23969/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4803/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4803 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4803*1^1024 ≤ 0^1024*1^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4803/1024 : ℝ) ≤ (1359848008197862449/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4803 ≤ (1359848008197862449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4803*100000000000000000000^1024 ≤ 1359848008197862449^1024*5^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1359848008197862449 100000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1359848008197862449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4803 := by
      have hnat : (1 : ℕ)^1024*1^4803 ≤ 1^4803*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101359848008197862449/100000000000000000000 : ℝ) ≤ (5014419059298409/5000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (101359848008197862449/100000000000000000000 : ℝ)^1024 ≤ (5014419059298409/5000000000000000 : ℝ)^4803 := by
      have hnat : (101359848008197862449 : ℕ)^1024*5000000000000000^4803 ≤ 5014419059298409^4803*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101359848008197862449 100000000000000000000 5014419059298409 5000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014419059298409/5000000000000000 : ℝ)) (X := (101359848008197862449/100000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51359848008197862449/50000000000000000000 : ℝ) ≤ (2514419059298409/2500000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (51359848008197862449/50000000000000000000 : ℝ)^1024 ≤ (2514419059298409/2500000000000000 : ℝ)^4803 := by
      have hnat : (51359848008197862449 : ℕ)^1024*2500000000000000^4803 ≤ 2514419059298409^4803*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51359848008197862449 50000000000000000000 2514419059298409 2500000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514419059298409/2500000000000000 : ℝ)) (X := (51359848008197862449/50000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14419059298409/2000000000000000 : ℝ)*(0 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14419059298409/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1359848008197862449/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14419059298409/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4803/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14419059298409/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014419059298409/5000000000000000 : ℝ) by norm_num, show 1+(1359848008197862449/100000000000000000000 : ℝ)+(0 : ℝ)=(101359848008197862449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1359848008197862449/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14419059298409/2000000000000000 : ℝ)*(2/5 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14419059298409/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514419059298409/2500000000000000 : ℝ) by norm_num, show 1+2*(1359848008197862449/100000000000000000000 : ℝ)=(51359848008197862449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14419059298409/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14419059298409/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14419059298409/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14419059298409/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14419059298409/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14419059298409/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1543086897/10000000000 : ℝ)*X 0 0+(29105437/50000000 : ℝ)*X 0 1+(980373989/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5448797853/10000000000 : ℝ)*X 1 0+(-2050674551/10000000000 : ℝ)*X 1 1+(980374079/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1089759517/2000000000 : ℝ)*X 2 0+(2450935107/5000000000 : ℝ)*X 2 1+(-256334391/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2051967041/5000000000 : ℝ)*X 0 0+(615283933/2000000000 : ℝ)*X 0 1+(5370985287/10000000000 : ℝ)*X 0 2+(2051967041/5000000000 : ℝ)*X 1 0+(615283933/2000000000 : ℝ)*X 1 1+(5370985287/10000000000 : ℝ)*X 1 2+(2051967041/5000000000 : ℝ)*X 2 0+(615283933/2000000000 : ℝ)*X 2 1+(5370985287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1545721777/10000000000 : ℝ)*X 0 0+(7695317/15625000 : ℝ)*X 0 1+(5797138743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197787263/10000000000 : ℝ)*X 1 0+(-115540631/1000000000 : ℝ)*X 1 1+(2898569371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2598893609/5000000000 : ℝ)*X 2 0+(5797139157/10000000000 : ℝ)*X 2 1+(-144425717/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4110511293/10000000000 : ℝ)*X 0 0+(664154803/1250000000 : ℝ)*X 0 1+(1568100679/5000000000 : ℝ)*X 0 2+(4110511293/10000000000 : ℝ)*X 1 0+(664154803/1250000000 : ℝ)*X 1 1+(1568100679/5000000000 : ℝ)*X 1 2+(4110511293/10000000000 : ℝ)*X 2 0+(664154803/1250000000 : ℝ)*X 2 1+(1568100679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5654158051810826031/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228833727/20000000000000 : ℝ)*(base19) + (1020994329/100000000000000 : ℝ)*(base23) + (57803683/20000000000000 : ℝ)*(upper3) + (37959731/100000000000000 : ℝ)*(upper4) + (15064969/50000000000000 : ℝ)*(upper5) + (761854015287563/100000000000000 : ℝ)*(major0) + (761854015287563/100000000000000 : ℝ)*(major1) + (761854015287563/100000000000000 : ℝ)*(major2) + (13598592780919/1250000000000 : ℝ)*(sp0) + (10878901123343/1000000000000 : ℝ)*(sp1) + (543945117754303/50000000000000 : ℝ)*(sp2) + (217907011000483/50000000000000 : ℝ)*(sp3) + (479253677/12500000000000 : ℝ)*(sp4) + (2563599283/100000000000000 : ℝ)*(sp7) + (435816585600249/100000000000000 : ℝ)*(f.failure) + (135986407062867/12500000000000 : ℝ)*(f.sum) + (198584517487267/100000000000000000000000000000 : ℝ)*base65 + (1339531329012733/200000000000000000000000000000 : ℝ)*base68 + (420255645412733/200000000000000000000000000000 : ℝ)*base70 + (695554357187267/200000000000000000000000000000 : ℝ)*base71 + (473433544812733/100000000000000000000000000000 : ℝ)*base74 + (585458752187267/200000000000000000000000000000 : ℝ)*base75 + (503302635187267/200000000000000000000000000000 : ℝ)*base77 + (464129550187267/200000000000000000000000000000 : ℝ)*base79 + (96695035412733/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11668099/5000000000000000000000 : ℝ)*base90 + (11668099/5000000000000000000000 : ℝ)*base92 + (11668099/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540443338279758483302733/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1050916721/100000000000000 : ℝ)*(base19) + (1307538457/100000000000000 : ℝ)*(base23) + (136405477/50000000000000 : ℝ)*(base39) + (7066367/6250000000000 : ℝ)*(upper3) + (59927791/20000000000000 : ℝ)*(upper5) + (401487165625869/50000000000000 : ℝ)*(major0) + (401487165625869/50000000000000 : ℝ)*(major1) + (802974058440783/100000000000000 : ℝ)*(major2) + (1834696739/50000000000000 : ℝ)*(sp1) + (904518663/25000000000000 : ℝ)*(sp2) + (1146608855352733/100000000000000 : ℝ)*(sp4) + (573302067521267/50000000000000 : ℝ)*(sp5) + (573302101275289/50000000000000 : ℝ)*(sp6) + (229669677096003/50000000000000 : ℝ)*(sp7) + (229669677096003/50000000000000 : ℝ)*(f.failure) + (1146609128163687/100000000000000 : ℝ)*(f.sum) + (122573948900911/200000000000000000000000000000 : ℝ)*base66 + (345146535814247/200000000000000000000000000000 : ℝ)*base67 + (199126644242421/100000000000000000000000000000 : ℝ)*base69 + (287814265814247/200000000000000000000000000000 : ℝ)*base71 + (323003369299089/200000000000000000000000000000 : ℝ)*base73 + (768703497657579/100000000000000000000000000000 : ℝ)*base76 + (455889402742421/100000000000000000000000000000 : ℝ)*base77 + (181039160857579/100000000000000000000000000000 : ℝ)*base80 + (137895856742421/50000000000000000000000000000 : ℝ)*base81 + (1279953/2500000000000000000000 : ℝ)*base90 + (1279953/2500000000000000000000 : ℝ)*base92 + (23720047/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1622_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23969/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1622_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1622_s1_0 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-332204749/2000000000 : ℝ)*x 0 + (2759506397/5000000000 : ℝ)*x 1 + (5127558663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332204749/2000000000 : ℝ)^4807 ≤ (10217474315249/100000000000000 : ℝ)^3783 := by
    have hnat : (332204749 : ℕ)^4807*100000000000000^3783 ≤ 10217474315249^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332204749 2000000000 10217474315249 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2759506397/5000000000 : ℝ)^4807 ≤ (46988030997431/100000000000000 : ℝ)^3783 := by
    have hnat : (2759506397 : ℕ)^4807*100000000000000^3783 ≤ 46988030997431^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759506397 5000000000 46988030997431 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127558663/10000000000 : ℝ)^4807 ≤ (21397247340999/50000000000000 : ℝ)^3783 := by
    have hnat : (5127558663 : ℕ)^4807*50000000000000^3783 ≤ 21397247340999^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127558663 10000000000 21397247340999 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332204749/2000000000 : ℝ), (2759506397/5000000000 : ℝ), (5127558663/10000000000 : ℝ)] ![(10217474315249/100000000000000 : ℝ), (46988030997431/100000000000000 : ℝ), (21397247340999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332204749/2000000000 : ℝ)|^4807 ≤ (10217474315249/100000000000000 : ℝ)^3783
        have hw : |(-332204749/2000000000 : ℝ)|=(332204749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2759506397/5000000000 : ℝ)|^4807 ≤ (46988030997431/100000000000000 : ℝ)^3783
        have hw : |(2759506397/5000000000 : ℝ)|=(2759506397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127558663/10000000000 : ℝ)|^4807 ≤ (21397247340999/50000000000000 : ℝ)^3783
        have hw : |(5127558663/10000000000 : ℝ)|=(5127558663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_1 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368438193/10000000000 : ℝ)*x 0 + (-466337503/2500000000 : ℝ)*x 1 + (256377923/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368438193/10000000000 : ℝ)^4807 ≤ (5670638492369/12500000000000 : ℝ)^3783 := by
    have hnat : (5368438193 : ℕ)^4807*12500000000000^3783 ≤ 5670638492369^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368438193 10000000000 5670638492369 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466337503/2500000000 : ℝ)^4807 ≤ (2960099879439/25000000000000 : ℝ)^3783 := by
    have hnat : (466337503 : ℕ)^4807*25000000000000^3783 ≤ 2960099879439^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466337503 2500000000 2960099879439 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256377923/500000000 : ℝ)^4807 ≤ (21397246264581/50000000000000 : ℝ)^3783 := by
    have hnat : (256377923 : ℕ)^4807*50000000000000^3783 ≤ 21397246264581^3783*500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256377923 500000000 21397246264581 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368438193/10000000000 : ℝ), (-466337503/2500000000 : ℝ), (256377923/500000000 : ℝ)] ![(5670638492369/12500000000000 : ℝ), (2960099879439/25000000000000 : ℝ), (21397246264581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368438193/10000000000 : ℝ)|^4807 ≤ (5670638492369/12500000000000 : ℝ)^3783
        have hw : |(5368438193/10000000000 : ℝ)|=(5368438193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466337503/2500000000 : ℝ)|^4807 ≤ (2960099879439/25000000000000 : ℝ)^3783
        have hw : |(-466337503/2500000000 : ℝ)|=(466337503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256377923/500000000 : ℝ)|^4807 ≤ (21397246264581/50000000000000 : ℝ)^3783
        have hw : |(256377923/500000000 : ℝ)|=(256377923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_2 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684219237/5000000000 : ℝ)*x 0 + (640944757/1250000000 : ℝ)*x 1 + (-1865350169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684219237/5000000000 : ℝ)^4807 ≤ (45365110956249/100000000000000 : ℝ)^3783 := by
    have hnat : (2684219237 : ℕ)^4807*100000000000000^3783 ≤ 45365110956249^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684219237 5000000000 45365110956249 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640944757/1250000000 : ℝ)^4807 ≤ (42794488244699/100000000000000 : ℝ)^3783 := by
    have hnat : (640944757 : ℕ)^4807*100000000000000^3783 ≤ 42794488244699^3783*1250000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640944757 1250000000 42794488244699 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865350169/10000000000 : ℝ)^4807 ≤ (2960100196019/25000000000000 : ℝ)^3783 := by
    have hnat : (1865350169 : ℕ)^4807*25000000000000^3783 ≤ 2960100196019^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865350169 10000000000 2960100196019 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684219237/5000000000 : ℝ), (640944757/1250000000 : ℝ), (-1865350169/10000000000 : ℝ)] ![(45365110956249/100000000000000 : ℝ), (42794488244699/100000000000000 : ℝ), (2960100196019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684219237/5000000000 : ℝ)|^4807 ≤ (45365110956249/100000000000000 : ℝ)^3783
        have hw : |(2684219237/5000000000 : ℝ)|=(2684219237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640944757/1250000000 : ℝ)|^4807 ≤ (42794488244699/100000000000000 : ℝ)^3783
        have hw : |(640944757/1250000000 : ℝ)|=(640944757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865350169/10000000000 : ℝ)|^4807 ≤ (2960100196019/25000000000000 : ℝ)^3783
        have hw : |(-1865350169/10000000000 : ℝ)|=(1865350169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_3 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192839929/10000000000 : ℝ)*x 0 + (3725726301/10000000000 : ℝ)*x 1 + (4702880937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192839929/10000000000 : ℝ)^4807 ≤ (8284514852967/25000000000000 : ℝ)^3783 := by
    have hnat : (4192839929 : ℕ)^4807*25000000000000^3783 ≤ 8284514852967^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192839929 10000000000 8284514852967 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3725726301/10000000000 : ℝ)^4807 ≤ (570393190601/2000000000000 : ℝ)^3783 := by
    have hnat : (3725726301 : ℕ)^4807*2000000000000^3783 ≤ 570393190601^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725726301 10000000000 570393190601 2000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4702880937/10000000000 : ℝ)^4807 ≤ (19171140520523/50000000000000 : ℝ)^3783 := by
    have hnat : (4702880937 : ℕ)^4807*50000000000000^3783 ≤ 19171140520523^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702880937 10000000000 19171140520523 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192839929/10000000000 : ℝ), (3725726301/10000000000 : ℝ), (4702880937/10000000000 : ℝ)] ![(8284514852967/25000000000000 : ℝ), (570393190601/2000000000000 : ℝ), (19171140520523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192839929/10000000000 : ℝ)|^4807 ≤ (8284514852967/25000000000000 : ℝ)^3783
        have hw : |(4192839929/10000000000 : ℝ)|=(4192839929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3725726301/10000000000 : ℝ)|^4807 ≤ (570393190601/2000000000000 : ℝ)^3783
        have hw : |(3725726301/10000000000 : ℝ)|=(3725726301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4702880937/10000000000 : ℝ)|^4807 ≤ (19171140520523/50000000000000 : ℝ)^3783
        have hw : |(4702880937/10000000000 : ℝ)|=(4702880937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_4 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1661223271/10000000000 : ℝ)*x 0 + (320732769/625000000 : ℝ)*x 1 + (2757392119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1661223271/10000000000 : ℝ)^4807 ≤ (2554758477757/25000000000000 : ℝ)^3783 := by
    have hnat : (1661223271 : ℕ)^4807*25000000000000^3783 ≤ 2554758477757^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661223271 10000000000 2554758477757 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320732769/625000000 : ℝ)^4807 ≤ (42838676606031/100000000000000 : ℝ)^3783 := by
    have hnat : (320732769 : ℕ)^4807*100000000000000^3783 ≤ 42838676606031^3783*625000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320732769 625000000 42838676606031 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757392119/5000000000 : ℝ)^4807 ≤ (733473272961/1562500000000 : ℝ)^3783 := by
    have hnat : (2757392119 : ℕ)^4807*1562500000000^3783 ≤ 733473272961^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757392119 5000000000 733473272961 1562500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1661223271/10000000000 : ℝ), (320732769/625000000 : ℝ), (2757392119/5000000000 : ℝ)] ![(2554758477757/25000000000000 : ℝ), (42838676606031/100000000000000 : ℝ), (733473272961/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1661223271/10000000000 : ℝ)|^4807 ≤ (2554758477757/25000000000000 : ℝ)^3783
        have hw : |(-1661223271/10000000000 : ℝ)|=(1661223271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320732769/625000000 : ℝ)|^4807 ≤ (42838676606031/100000000000000 : ℝ)^3783
        have hw : |(320732769/625000000 : ℝ)|=(320732769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757392119/5000000000 : ℝ)|^4807 ≤ (733473272961/1562500000000 : ℝ)^3783
        have hw : |(2757392119/5000000000 : ℝ)|=(2757392119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_5 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632060713/5000000000 : ℝ)*x 0 + (-295624719/2000000000 : ℝ)*x 1 + (5514784577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632060713/5000000000 : ℝ)^4807 ≤ (22123972167711/50000000000000 : ℝ)^3783 := by
    have hnat : (2632060713 : ℕ)^4807*50000000000000^3783 ≤ 22123972167711^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632060713 5000000000 22123972167711 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295624719/2000000000 : ℝ)^4807 ≤ (8809762514559/100000000000000 : ℝ)^3783 := by
    have hnat : (295624719 : ℕ)^4807*100000000000000^3783 ≤ 8809762514559^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295624719 2000000000 8809762514559 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514784577/10000000000 : ℝ)^4807 ≤ (23471146568093/50000000000000 : ℝ)^3783 := by
    have hnat : (5514784577 : ℕ)^4807*50000000000000^3783 ≤ 23471146568093^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514784577 10000000000 23471146568093 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632060713/5000000000 : ℝ), (-295624719/2000000000 : ℝ), (5514784577/10000000000 : ℝ)] ![(22123972167711/50000000000000 : ℝ), (8809762514559/100000000000000 : ℝ), (23471146568093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632060713/5000000000 : ℝ)|^4807 ≤ (22123972167711/50000000000000 : ℝ)^3783
        have hw : |(2632060713/5000000000 : ℝ)|=(2632060713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295624719/2000000000 : ℝ)|^4807 ≤ (8809762514559/100000000000000 : ℝ)^3783
        have hw : |(-295624719/2000000000 : ℝ)|=(295624719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514784577/10000000000 : ℝ)|^4807 ≤ (23471146568093/50000000000000 : ℝ)^3783
        have hw : |(5514784577/10000000000 : ℝ)|=(5514784577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_6 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632060389/5000000000 : ℝ)*x 0 + (5514784819/10000000000 : ℝ)*x 1 + (-1478124163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632060389/5000000000 : ℝ)^4807 ≤ (11061984353561/25000000000000 : ℝ)^3783 := by
    have hnat : (2632060389 : ℕ)^4807*25000000000000^3783 ≤ 11061984353561^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632060389 5000000000 11061984353561 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514784819/10000000000 : ℝ)^4807 ≤ (46942295753699/100000000000000 : ℝ)^3783 := by
    have hnat : (5514784819 : ℕ)^4807*100000000000000^3783 ≤ 46942295753699^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514784819 10000000000 46942295753699 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1478124163/10000000000 : ℝ)^4807 ≤ (8809766816253/100000000000000 : ℝ)^3783 := by
    have hnat : (1478124163 : ℕ)^4807*100000000000000^3783 ≤ 8809766816253^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478124163 10000000000 8809766816253 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632060389/5000000000 : ℝ), (5514784819/10000000000 : ℝ), (-1478124163/10000000000 : ℝ)] ![(11061984353561/25000000000000 : ℝ), (46942295753699/100000000000000 : ℝ), (8809766816253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632060389/5000000000 : ℝ)|^4807 ≤ (11061984353561/25000000000000 : ℝ)^3783
        have hw : |(2632060389/5000000000 : ℝ)|=(2632060389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514784819/10000000000 : ℝ)|^4807 ≤ (46942295753699/100000000000000 : ℝ)^3783
        have hw : |(5514784819/10000000000 : ℝ)|=(5514784819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1478124163/10000000000 : ℝ)|^4807 ≤ (8809766816253/100000000000000 : ℝ)^3783
        have hw : |(-1478124163/10000000000 : ℝ)|=(1478124163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s1_7 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193335827/10000000000 : ℝ)*x 0 + (1173120907/2500000000 : ℝ)*x 1 + (233517553/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193335827/10000000000 : ℝ)^4807 ≤ (8285759929041/25000000000000 : ℝ)^3783 := by
    have hnat : (4193335827 : ℕ)^4807*25000000000000^3783 ≤ 8285759929041^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193335827 10000000000 8285759929041 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173120907/2500000000 : ℝ)^4807 ≤ (38234599154591/100000000000000 : ℝ)^3783 := by
    have hnat : (1173120907 : ℕ)^4807*100000000000000^3783 ≤ 38234599154591^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173120907 2500000000 38234599154591 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233517553/625000000 : ℝ)^4807 ≤ (14311180556083/50000000000000 : ℝ)^3783 := by
    have hnat : (233517553 : ℕ)^4807*50000000000000^3783 ≤ 14311180556083^3783*625000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233517553 625000000 14311180556083 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193335827/10000000000 : ℝ), (1173120907/2500000000 : ℝ), (233517553/625000000 : ℝ)] ![(8285759929041/25000000000000 : ℝ), (38234599154591/100000000000000 : ℝ), (14311180556083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193335827/10000000000 : ℝ)|^4807 ≤ (8285759929041/25000000000000 : ℝ)^3783
        have hw : |(4193335827/10000000000 : ℝ)|=(4193335827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1173120907/2500000000 : ℝ)|^4807 ≤ (38234599154591/100000000000000 : ℝ)^3783
        have hw : |(1173120907/2500000000 : ℝ)|=(1173120907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233517553/625000000 : ℝ)|^4807 ≤ (14311180556083/50000000000000 : ℝ)^3783
        have hw : |(233517553/625000000 : ℝ)|=(233517553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1622_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17639/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4279/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (4756825735589/12500000000000000000 : ℝ) := by
    have hpowers : (4279/100000 : ℝ)^4803 ≤ (4756825735589/12500000000000000000 : ℝ)^1024 := by
      have hnat : (4279 : ℕ)^4803*12500000000000000000^1024 ≤ 4756825735589^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4279 100000 4756825735589 12500000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4279/100000 : ℝ)) (X := (4756825735589/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23969/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (123109494078539407/100000000000000000000 : ℝ) := by
    have hpowers : (23969/100000 : ℝ)^4803 ≤ (123109494078539407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23969 : ℕ)^4803*100000000000000000000^1024 ≤ 123109494078539407^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23969 100000 123109494078539407 100000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23969/100000 : ℝ)) (X := (123109494078539407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250004756825735589/6250000000000000000 : ℝ) ≤ (10000001622648543/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (6250004756825735589/6250000000000000000 : ℝ)^1024 ≤ (10000001622648543/10000000000000000 : ℝ)^4803 := by
      have hnat : (6250004756825735589 : ℕ)^1024*10000000000000000^4803 ≤ 10000001622648543^4803*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250004756825735589 6250000000000000000 10000001622648543 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001622648543/10000000000000000 : ℝ)) (X := (6250004756825735589/6250000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100123147548684424119/100000000000000000000 : ℝ) ≤ (250065605893409/250000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (100123147548684424119/100000000000000000000 : ℝ)^1024 ≤ (250065605893409/250000000000000 : ℝ)^4803 := by
      have hnat : (100123147548684424119 : ℕ)^1024*250000000000000^4803 ≤ 250065605893409^4803*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100123147548684424119 100000000000000000000 250065605893409 250000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250065605893409/250000000000000 : ℝ)) (X := (100123147548684424119/100000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50123109494078539407/50000000000000000000 : ℝ) ≤ (10005246848824177/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (50123109494078539407/50000000000000000000 : ℝ)^1024 ≤ (10005246848824177/10000000000000000 : ℝ)^4803 := by
      have hnat : (50123109494078539407 : ℕ)^1024*10000000000000000^4803 ≤ 10005246848824177^4803*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50123109494078539407 50000000000000000000 10005246848824177 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005246848824177/10000000000000000 : ℝ)) (X := (50123109494078539407/50000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4756825735589/12500000000000000000 : ℝ) ≤ ((2237245313944821293/2237500000000000000 : ℝ)+2*(2622613087817/1969000000000000 : ℝ)*(4279/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (2237245313944821293/2237500000000000000 : ℝ)+2*(2622613087817/1969000000000000 : ℝ)*(4279/100000 : ℝ)=(10000001622648543/10000000000000000 : ℝ) by norm_num, show 1+2*(4756825735589/12500000000000000000 : ℝ)=(6250004756825735589/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(123109494078539407/100000000000000000000 : ℝ)+(4756825735589/12500000000000000000 : ℝ) ≤ ((2237245313944821293/2237500000000000000 : ℝ)+(2622613087817/1969000000000000 : ℝ)*((23969/100000 : ℝ)+(4279/100000 : ℝ)))^(4803/1024 : ℝ) := by
    rw [show (2237245313944821293/2237500000000000000 : ℝ)+(2622613087817/1969000000000000 : ℝ)*((23969/100000 : ℝ)+(4279/100000 : ℝ))=(250065605893409/250000000000000 : ℝ) by norm_num, show 1+(123109494078539407/100000000000000000000 : ℝ)+(4756825735589/12500000000000000000 : ℝ)=(100123147548684424119/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(123109494078539407/100000000000000000000 : ℝ) ≤ ((2237245313944821293/2237500000000000000 : ℝ)+2*(2622613087817/1969000000000000 : ℝ)*(23969/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (2237245313944821293/2237500000000000000 : ℝ)+2*(2622613087817/1969000000000000 : ℝ)*(23969/100000 : ℝ)=(10005246848824177/10000000000000000 : ℝ) by norm_num, show 1+2*(123109494078539407/100000000000000000000 : ℝ)=(50123109494078539407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2237245313944821293/2237500000000000000 : ℝ)*(X 1 0+X 2 0)+(2622613087817/1969000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (4279/100000 : ℝ)) (hi := (23969/100000 : ℝ)) (c := (2237245313944821293/2237500000000000000 : ℝ)) (alpha := (2622613087817/1969000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2237245313944821293/2237500000000000000 : ℝ)*(X 0 1+X 2 1)+(2622613087817/1969000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (4279/100000 : ℝ)) (hi := (23969/100000 : ℝ)) (c := (2237245313944821293/2237500000000000000 : ℝ)) (alpha := (2622613087817/1969000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2237245313944821293/2237500000000000000 : ℝ)*(X 0 2+X 1 2)+(2622613087817/1969000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (4279/100000 : ℝ)) (hi := (23969/100000 : ℝ)) (c := (2237245313944821293/2237500000000000000 : ℝ)) (alpha := (2622613087817/1969000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-332204749/2000000000 : ℝ)*X 0 0+(2759506397/5000000000 : ℝ)*X 0 1+(5127558663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368438193/10000000000 : ℝ)*X 1 0+(-466337503/2500000000 : ℝ)*X 1 1+(256377923/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684219237/5000000000 : ℝ)*X 2 0+(640944757/1250000000 : ℝ)*X 2 1+(-1865350169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192839929/10000000000 : ℝ)*X 0 0+(3725726301/10000000000 : ℝ)*X 0 1+(4702880937/10000000000 : ℝ)*X 0 2+(4192839929/10000000000 : ℝ)*X 1 0+(3725726301/10000000000 : ℝ)*X 1 1+(4702880937/10000000000 : ℝ)*X 1 2+(4192839929/10000000000 : ℝ)*X 2 0+(3725726301/10000000000 : ℝ)*X 2 1+(4702880937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1661223271/10000000000 : ℝ)*X 0 0+(320732769/625000000 : ℝ)*X 0 1+(2757392119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632060713/5000000000 : ℝ)*X 1 0+(-295624719/2000000000 : ℝ)*X 1 1+(5514784577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632060389/5000000000 : ℝ)*X 2 0+(5514784819/10000000000 : ℝ)*X 2 1+(-1478124163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4193335827/10000000000 : ℝ)*X 0 0+(1173120907/2500000000 : ℝ)*X 0 1+(233517553/625000000 : ℝ)*X 0 2+(4193335827/10000000000 : ℝ)*X 1 0+(1173120907/2500000000 : ℝ)*X 1 1+(233517553/625000000 : ℝ)*X 1 2+(4193335827/10000000000 : ℝ)*X 2 0+(1173120907/2500000000 : ℝ)*X 2 1+(233517553/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (440101974194572344404605989/55937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63297019/20000000000000 : ℝ)*(base1) + (1413778069/100000000000000 : ℝ)*(base19) + (309498589/20000000000000 : ℝ)*(base23) + (24442017/12500000000000 : ℝ)*(upper3) + (31385167/25000000000000 : ℝ)*(upper5) + (894494918432909/50000000000000 : ℝ)*(major0) + (894494918432909/50000000000000 : ℝ)*(major1) + (894494918432909/50000000000000 : ℝ)*(major2) + (1277292793719393/50000000000000 : ℝ)*(sp0) + (2554591066956291/100000000000000 : ℝ)*(sp1) + (319323866655177/12500000000000 : ℝ)*(sp2) + (255845680793603/25000000000000 : ℝ)*(sp3) + (7209780669/100000000000000 : ℝ)*(sp4) + (972769901/25000000000000 : ℝ)*(sp7) + (127923366342389/12500000000000 : ℝ)*(f.failure) + (63864812018359/2500000000000 : ℝ)*(f.sum) + (9767782677711/24612500000000000000000000000 : ℝ)*base66 + (280176563922892793/1230625000000000000000000000000000 : ℝ)*base68 + (3709797908297107207/1230625000000000000000000000000000 : ℝ)*base69 + (2900434498380232207/1230625000000000000000000000000000 : ℝ)*base71 + (107887570760547/49225000000000000000000000000 : ℝ)*base74 + (765560182747107207/1230625000000000000000000000000000 : ℝ)*base75 + (9797913573087892793/1230625000000000000000000000000000 : ℝ)*base78 + (259895725399607207/1230625000000000000000000000000000 : ℝ)*base79 + (190258355091953/49225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1538761/625000000000000000000 : ℝ)*base89 + (1538761/625000000000000000000 : ℝ)*base91 + (1538761/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5900160734098530803332464603/615312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473619169/25000000000000 : ℝ)*(base19) + (1614228809/100000000000000 : ℝ)*(base23) + (28203847/100000000000000 : ℝ)*(upper2) + (377104101/100000000000000 : ℝ)*(upper3) + (100599657/100000000000000 : ℝ)*(upper5) + (914089019666771/50000000000000 : ℝ)*(major0) + (914089019666771/50000000000000 : ℝ)*(major1) + (914089019666771/50000000000000 : ℝ)*(major2) + (7245213647/50000000000000 : ℝ)*(sp1) + (13860864683/100000000000000 : ℝ)*(sp2) + (326318915018809/12500000000000 : ℝ)*(sp4) + (1305267467623251/50000000000000 : ℝ)*(sp5) + (130526792252849/5000000000000 : ℝ)*(sp6) + (1045804438887111/100000000000000 : ℝ)*(sp7) + (1045804438887111/100000000000000 : ℝ)*(f.failure) + (326318915018809/12500000000000 : ℝ)*(f.sum) + (84466440355109/24612500000000000000000000000 : ℝ)*base66 + (7185864886967741433/1230625000000000000000000000000000 : ℝ)*base67 + (7520693007160241433/1230625000000000000000000000000000 : ℝ)*base69 + (7323907545120866433/1230625000000000000000000000000000 : ℝ)*base71 + (28911610391343/49225000000000000000000000000 : ℝ)*base74 + (9349959774221491433/1230625000000000000000000000000000 : ℝ)*base75 + (4409845891513366433/1230625000000000000000000000000000 : ℝ)*base77 + (12308893532455241433/1230625000000000000000000000000000 : ℝ)*base79 + (42618503261841/24612500000000000000000000000 : ℝ)*base81 + (8556739/5000000000000000000000 : ℝ)*base89 + (8556739/5000000000000000000000 : ℝ)*base91 + (8556739/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1622_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17639/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1622_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1622_s2_0 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1673363319/10000000000 : ℝ)*x 0 + (1365428559/2500000000 : ℝ)*x 1 + (1035351949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1673363319/10000000000 : ℝ)^4807 ≤ (10314021878137/100000000000000 : ℝ)^3783 := by
    have hnat : (1673363319 : ℕ)^4807*100000000000000^3783 ≤ 10314021878137^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673363319 10000000000 10314021878137 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365428559/2500000000 : ℝ)^4807 ≤ (4636902465169/10000000000000 : ℝ)^3783 := by
    have hnat : (1365428559 : ℕ)^4807*10000000000000^3783 ≤ 4636902465169^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365428559 2500000000 4636902465169 10000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035351949/2000000000 : ℝ)^4807 ≤ (10829238364483/25000000000000 : ℝ)^3783 := by
    have hnat : (1035351949 : ℕ)^4807*25000000000000^3783 ≤ 10829238364483^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035351949 2000000000 10829238364483 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1673363319/10000000000 : ℝ), (1365428559/2500000000 : ℝ), (1035351949/2000000000 : ℝ)] ![(10314021878137/100000000000000 : ℝ), (4636902465169/10000000000000 : ℝ), (10829238364483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1673363319/10000000000 : ℝ)|^4807 ≤ (10314021878137/100000000000000 : ℝ)^3783
        have hw : |(-1673363319/10000000000 : ℝ)|=(1673363319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365428559/2500000000 : ℝ)|^4807 ≤ (4636902465169/10000000000000 : ℝ)^3783
        have hw : |(1365428559/2500000000 : ℝ)|=(1365428559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035351949/2000000000 : ℝ)|^4807 ≤ (10829238364483/25000000000000 : ℝ)^3783
        have hw : |(1035351949/2000000000 : ℝ)|=(1035351949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_1 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353430847/10000000000 : ℝ)*x 0 + (-910199237/5000000000 : ℝ)*x 1 + (5176759763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353430847/10000000000 : ℝ)^4807 ≤ (45204024382043/100000000000000 : ℝ)^3783 := by
    have hnat : (5353430847 : ℕ)^4807*100000000000000^3783 ≤ 45204024382043^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353430847 10000000000 45204024382043 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910199237/5000000000 : ℝ)^4807 ≤ (1147902196083/10000000000000 : ℝ)^3783 := by
    have hnat : (910199237 : ℕ)^4807*10000000000000^3783 ≤ 1147902196083^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910199237 5000000000 1147902196083 10000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176759763/10000000000 : ℝ)^4807 ≤ (21658476824659/50000000000000 : ℝ)^3783 := by
    have hnat : (5176759763 : ℕ)^4807*50000000000000^3783 ≤ 21658476824659^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176759763 10000000000 21658476824659 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353430847/10000000000 : ℝ), (-910199237/5000000000 : ℝ), (5176759763/10000000000 : ℝ)] ![(45204024382043/100000000000000 : ℝ), (1147902196083/10000000000000 : ℝ), (21658476824659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353430847/10000000000 : ℝ)|^4807 ≤ (45204024382043/100000000000000 : ℝ)^3783
        have hw : |(5353430847/10000000000 : ℝ)|=(5353430847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910199237/5000000000 : ℝ)|^4807 ≤ (1147902196083/10000000000000 : ℝ)^3783
        have hw : |(-910199237/5000000000 : ℝ)|=(910199237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176759763/10000000000 : ℝ)|^4807 ≤ (21658476824659/50000000000000 : ℝ)^3783
        have hw : |(5176759763/10000000000 : ℝ)|=(5176759763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_2 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42827447/80000000 : ℝ)*x 0 + (517675971/1000000000 : ℝ)*x 1 + (-910199253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42827447/80000000 : ℝ)^4807 ≤ (45204024682471/100000000000000 : ℝ)^3783 := by
    have hnat : (42827447 : ℕ)^4807*100000000000000^3783 ≤ 45204024682471^3783*80000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42827447 80000000 45204024682471 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517675971/1000000000 : ℝ)^4807 ≤ (1353654783931/3125000000000 : ℝ)^3783 := by
    have hnat : (517675971 : ℕ)^4807*3125000000000^3783 ≤ 1353654783931^3783*1000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517675971 1000000000 1353654783931 3125000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910199253/5000000000 : ℝ)^4807 ≤ (2295804443447/20000000000000 : ℝ)^3783 := by
    have hnat : (910199253 : ℕ)^4807*20000000000000^3783 ≤ 2295804443447^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910199253 5000000000 2295804443447 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42827447/80000000 : ℝ), (517675971/1000000000 : ℝ), (-910199253/5000000000 : ℝ)] ![(45204024682471/100000000000000 : ℝ), (1353654783931/3125000000000 : ℝ), (2295804443447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42827447/80000000 : ℝ)|^4807 ≤ (45204024682471/100000000000000 : ℝ)^3783
        have hw : |(42827447/80000000 : ℝ)|=(42827447/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517675971/1000000000 : ℝ)|^4807 ≤ (1353654783931/3125000000000 : ℝ)^3783
        have hw : |(517675971/1000000000 : ℝ)|=(517675971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-910199253/5000000000 : ℝ)|^4807 ≤ (2295804443447/20000000000000 : ℝ)^3783
        have hw : |(-910199253/5000000000 : ℝ)|=(910199253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_3 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050493681/2500000000 : ℝ)*x 0 + (964424617/2500000000 : ℝ)*x 1 + (4569005939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050493681/2500000000 : ℝ)^4807 ≤ (33229825738603/100000000000000 : ℝ)^3783 := by
    have hnat : (1050493681 : ℕ)^4807*100000000000000^3783 ≤ 33229825738603^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050493681 2500000000 33229825738603 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964424617/2500000000 : ℝ)^4807 ≤ (14904715859989/50000000000000 : ℝ)^3783 := by
    have hnat : (964424617 : ℕ)^4807*50000000000000^3783 ≤ 14904715859989^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964424617 2500000000 14904715859989 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4569005939/10000000000 : ℝ)^4807 ≤ (115502320383/312500000000 : ℝ)^3783 := by
    have hnat : (4569005939 : ℕ)^4807*312500000000^3783 ≤ 115502320383^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569005939 10000000000 115502320383 312500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050493681/2500000000 : ℝ), (964424617/2500000000 : ℝ), (4569005939/10000000000 : ℝ)] ![(33229825738603/100000000000000 : ℝ), (14904715859989/50000000000000 : ℝ), (115502320383/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050493681/2500000000 : ℝ)|^4807 ≤ (33229825738603/100000000000000 : ℝ)^3783
        have hw : |(1050493681/2500000000 : ℝ)|=(1050493681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(964424617/2500000000 : ℝ)|^4807 ≤ (14904715859989/50000000000000 : ℝ)^3783
        have hw : |(964424617/2500000000 : ℝ)|=(964424617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4569005939/10000000000 : ℝ)|^4807 ≤ (115502320383/312500000000 : ℝ)^3783
        have hw : |(4569005939/10000000000 : ℝ)|=(4569005939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_4 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836720113/5000000000 : ℝ)*x 0 + (5178973749/10000000000 : ℝ)*x 1 + (2729738013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836720113/5000000000 : ℝ)^4807 ≤ (5157312110769/50000000000000 : ℝ)^3783 := by
    have hnat : (836720113 : ℕ)^4807*50000000000000^3783 ≤ 5157312110769^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836720113 5000000000 5157312110769 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178973749/10000000000 : ℝ)^4807 ≤ (43340495341739/100000000000000 : ℝ)^3783 := by
    have hnat : (5178973749 : ℕ)^4807*100000000000000^3783 ≤ 43340495341739^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178973749 10000000000 43340495341739 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729738013/5000000000 : ℝ)^4807 ≤ (23172440206679/50000000000000 : ℝ)^3783 := by
    have hnat : (2729738013 : ℕ)^4807*50000000000000^3783 ≤ 23172440206679^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729738013 5000000000 23172440206679 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836720113/5000000000 : ℝ), (5178973749/10000000000 : ℝ), (2729738013/5000000000 : ℝ)] ![(5157312110769/50000000000000 : ℝ), (43340495341739/100000000000000 : ℝ), (23172440206679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836720113/5000000000 : ℝ)|^4807 ≤ (5157312110769/50000000000000 : ℝ)^3783
        have hw : |(-836720113/5000000000 : ℝ)|=(836720113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178973749/10000000000 : ℝ)|^4807 ≤ (43340495341739/100000000000000 : ℝ)^3783
        have hw : |(5178973749/10000000000 : ℝ)|=(5178973749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729738013/5000000000 : ℝ)|^4807 ≤ (23172440206679/50000000000000 : ℝ)^3783
        have hw : |(2729738013/5000000000 : ℝ)|=(2729738013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_5 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277590999/10000000000 : ℝ)*x 0 + (-384420611/2500000000 : ℝ)*x 1 + (5459475769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277590999/10000000000 : ℝ)^4807 ≤ (44391860338719/100000000000000 : ℝ)^3783 := by
    have hnat : (5277590999 : ℕ)^4807*100000000000000^3783 ≤ 44391860338719^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277590999 10000000000 44391860338719 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384420611/2500000000 : ℝ)^4807 ≤ (9263262006049/100000000000000 : ℝ)^3783 := by
    have hnat : (384420611 : ℕ)^4807*100000000000000^3783 ≤ 9263262006049^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384420611 2500000000 9263262006049 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459475769/10000000000 : ℝ)^4807 ≤ (5793109705147/12500000000000 : ℝ)^3783 := by
    have hnat : (5459475769 : ℕ)^4807*12500000000000^3783 ≤ 5793109705147^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459475769 10000000000 5793109705147 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277590999/10000000000 : ℝ), (-384420611/2500000000 : ℝ), (5459475769/10000000000 : ℝ)] ![(44391860338719/100000000000000 : ℝ), (9263262006049/100000000000000 : ℝ), (5793109705147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277590999/10000000000 : ℝ)|^4807 ≤ (44391860338719/100000000000000 : ℝ)^3783
        have hw : |(5277590999/10000000000 : ℝ)|=(5277590999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384420611/2500000000 : ℝ)|^4807 ≤ (9263262006049/100000000000000 : ℝ)^3783
        have hw : |(-384420611/2500000000 : ℝ)|=(384420611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459475769/10000000000 : ℝ)|^4807 ≤ (5793109705147/12500000000000 : ℝ)^3783
        have hw : |(5459475769/10000000000 : ℝ)|=(5459475769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_6 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20615589/39062500 : ℝ)*x 0 + (1364869027/2500000000 : ℝ)*x 1 + (-1537682267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20615589/39062500 : ℝ)^4807 ≤ (44391858040751/100000000000000 : ℝ)^3783 := by
    have hnat : (20615589 : ℕ)^4807*100000000000000^3783 ≤ 44391858040751^3783*39062500^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20615589 39062500 44391858040751 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364869027/2500000000 : ℝ)^4807 ≤ (11586220324467/25000000000000 : ℝ)^3783 := by
    have hnat : (1364869027 : ℕ)^4807*25000000000000^3783 ≤ 11586220324467^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364869027 2500000000 11586220324467 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1537682267/10000000000 : ℝ)^4807 ≤ (4631630325573/50000000000000 : ℝ)^3783 := by
    have hnat : (1537682267 : ℕ)^4807*50000000000000^3783 ≤ 4631630325573^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537682267 10000000000 4631630325573 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20615589/39062500 : ℝ), (1364869027/2500000000 : ℝ), (-1537682267/10000000000 : ℝ)] ![(44391858040751/100000000000000 : ℝ), (11586220324467/25000000000000 : ℝ), (4631630325573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20615589/39062500 : ℝ)|^4807 ≤ (44391858040751/100000000000000 : ℝ)^3783
        have hw : |(20615589/39062500 : ℝ)|=(20615589/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364869027/2500000000 : ℝ)|^4807 ≤ (11586220324467/25000000000000 : ℝ)^3783
        have hw : |(1364869027/2500000000 : ℝ)|=(1364869027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1537682267/10000000000 : ℝ)|^4807 ≤ (4631630325573/50000000000000 : ℝ)^3783
        have hw : |(-1537682267/10000000000 : ℝ)|=(1537682267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s2_7 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420216683/1000000000 : ℝ)*x 0 + (228173937/500000000 : ℝ)*x 1 + (3863286091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420216683/1000000000 : ℝ)^4807 ≤ (8307939044337/25000000000000 : ℝ)^3783 := by
    have hnat : (420216683 : ℕ)^4807*25000000000000^3783 ≤ 8307939044337^3783*1000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420216683 1000000000 8307939044337 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228173937/500000000 : ℝ)^4807 ≤ (1845196848983/5000000000000 : ℝ)^3783 := by
    have hnat : (228173937 : ℕ)^4807*5000000000000^3783 ≤ 1845196848983^3783*500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228173937 500000000 1845196848983 5000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3863286091/10000000000 : ℝ)^4807 ≤ (5972861365743/20000000000000 : ℝ)^3783 := by
    have hnat : (3863286091 : ℕ)^4807*20000000000000^3783 ≤ 5972861365743^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863286091 10000000000 5972861365743 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420216683/1000000000 : ℝ), (228173937/500000000 : ℝ), (3863286091/10000000000 : ℝ)] ![(8307939044337/25000000000000 : ℝ), (1845196848983/5000000000000 : ℝ), (5972861365743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420216683/1000000000 : ℝ)|^4807 ≤ (8307939044337/25000000000000 : ℝ)^3783
        have hw : |(420216683/1000000000 : ℝ)|=(420216683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228173937/500000000 : ℝ)|^4807 ≤ (1845196848983/5000000000000 : ℝ)^3783
        have hw : |(228173937/500000000 : ℝ)|=(228173937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3863286091/10000000000 : ℝ)|^4807 ≤ (5972861365743/20000000000000 : ℝ)^3783
        have hw : |(3863286091/10000000000 : ℝ)|=(3863286091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1622_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17639/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (13/125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3289/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17639/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17639/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17639/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17639/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17639/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17639/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9337/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (1478529601027111/100000000000000000000 : ℝ) := by
    have hpowers : (9337/100000 : ℝ)^4803 ≤ (1478529601027111/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9337 : ℕ)^4803*100000000000000000000^1024 ≤ 1478529601027111^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9337 100000 1478529601027111 100000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9337/100000 : ℝ)) (X := (1478529601027111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17639/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (2921723359203937/10000000000000000000 : ℝ) := by
    have hpowers : (17639/100000 : ℝ)^4803 ≤ (2921723359203937/10000000000000000000 : ℝ)^1024 := by
      have hnat : (17639 : ℕ)^4803*10000000000000000000^1024 ≤ 2921723359203937^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17639 100000 2921723359203937 10000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17639/100000 : ℝ)) (X := (2921723359203937/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001478529601027111/50000000000000000000 : ℝ) ≤ (10000063043793427/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (50001478529601027111/50000000000000000000 : ℝ)^1024 ≤ (10000063043793427/10000000000000000 : ℝ)^4803 := by
      have hnat : (50001478529601027111 : ℕ)^1024*10000000000000000^4803 ≤ 10000063043793427^4803*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001478529601027111 50000000000000000000 10000063043793427 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063043793427/10000000000000000 : ℝ)) (X := (50001478529601027111/50000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030695763193066481/100000000000000000000 : ℝ) ≤ (2500163588728451/2500000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (100030695763193066481/100000000000000000000 : ℝ)^1024 ≤ (2500163588728451/2500000000000000 : ℝ)^4803 := by
      have hnat : (100030695763193066481 : ℕ)^1024*2500000000000000^4803 ≤ 2500163588728451^4803*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030695763193066481 100000000000000000000 2500163588728451 2500000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500163588728451/2500000000000000 : ℝ)) (X := (100030695763193066481/100000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002921723359203937/5000000000000000000 : ℝ) ≤ (10001245666034181/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (5002921723359203937/5000000000000000000 : ℝ)^1024 ≤ (10001245666034181/10000000000000000 : ℝ)^4803 := by
      have hnat : (5002921723359203937 : ℕ)^1024*10000000000000000^4803 ≤ 10001245666034181^4803*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002921723359203937 5000000000000000000 10001245666034181 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001245666034181/10000000000000000 : ℝ)) (X := (5002921723359203937/5000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1478529601027111/100000000000000000000 : ℝ) ≤ ((10376185155713888857/10377500000000000000 : ℝ)+2*(591311120377/830200000000000 : ℝ)*(9337/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (10376185155713888857/10377500000000000000 : ℝ)+2*(591311120377/830200000000000 : ℝ)*(9337/100000 : ℝ)=(10000063043793427/10000000000000000 : ℝ) by norm_num, show 1+2*(1478529601027111/100000000000000000000 : ℝ)=(50001478529601027111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2921723359203937/10000000000000000000 : ℝ)+(1478529601027111/100000000000000000000 : ℝ) ≤ ((10376185155713888857/10377500000000000000 : ℝ)+(591311120377/830200000000000 : ℝ)*((17639/100000 : ℝ)+(9337/100000 : ℝ)))^(4803/1024 : ℝ) := by
    rw [show (10376185155713888857/10377500000000000000 : ℝ)+(591311120377/830200000000000 : ℝ)*((17639/100000 : ℝ)+(9337/100000 : ℝ))=(2500163588728451/2500000000000000 : ℝ) by norm_num, show 1+(2921723359203937/10000000000000000000 : ℝ)+(1478529601027111/100000000000000000000 : ℝ)=(100030695763193066481/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2921723359203937/10000000000000000000 : ℝ) ≤ ((10376185155713888857/10377500000000000000 : ℝ)+2*(591311120377/830200000000000 : ℝ)*(17639/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (10376185155713888857/10377500000000000000 : ℝ)+2*(591311120377/830200000000000 : ℝ)*(17639/100000 : ℝ)=(10001245666034181/10000000000000000 : ℝ) by norm_num, show 1+2*(2921723359203937/10000000000000000000 : ℝ)=(5002921723359203937/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10376185155713888857/10377500000000000000 : ℝ)*(X 1 0+X 2 0)+(591311120377/830200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (9337/100000 : ℝ)) (hi := (17639/100000 : ℝ)) (c := (10376185155713888857/10377500000000000000 : ℝ)) (alpha := (591311120377/830200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10376185155713888857/10377500000000000000 : ℝ)*(X 0 1+X 2 1)+(591311120377/830200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (9337/100000 : ℝ)) (hi := (17639/100000 : ℝ)) (c := (10376185155713888857/10377500000000000000 : ℝ)) (alpha := (591311120377/830200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10376185155713888857/10377500000000000000 : ℝ)*(X 0 2+X 1 2)+(591311120377/830200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (9337/100000 : ℝ)) (hi := (17639/100000 : ℝ)) (c := (10376185155713888857/10377500000000000000 : ℝ)) (alpha := (591311120377/830200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1673363319/10000000000 : ℝ)*X 0 0+(1365428559/2500000000 : ℝ)*X 0 1+(1035351949/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353430847/10000000000 : ℝ)*X 1 0+(-910199237/5000000000 : ℝ)*X 1 1+(5176759763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42827447/80000000 : ℝ)*X 2 0+(517675971/1000000000 : ℝ)*X 2 1+(-910199253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050493681/2500000000 : ℝ)*X 0 0+(964424617/2500000000 : ℝ)*X 0 1+(4569005939/10000000000 : ℝ)*X 0 2+(1050493681/2500000000 : ℝ)*X 1 0+(964424617/2500000000 : ℝ)*X 1 1+(4569005939/10000000000 : ℝ)*X 1 2+(1050493681/2500000000 : ℝ)*X 2 0+(964424617/2500000000 : ℝ)*X 2 1+(4569005939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-836720113/5000000000 : ℝ)*X 0 0+(5178973749/10000000000 : ℝ)*X 0 1+(2729738013/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277590999/10000000000 : ℝ)*X 1 0+(-384420611/2500000000 : ℝ)*X 1 1+(5459475769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20615589/39062500 : ℝ)*X 2 0+(1364869027/2500000000 : ℝ)*X 2 1+(-1537682267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420216683/1000000000 : ℝ)*X 0 0+(228173937/500000000 : ℝ)*X 0 1+(3863286091/10000000000 : ℝ)*X 0 2+(420216683/1000000000 : ℝ)*X 1 0+(228173937/500000000 : ℝ)*X 1 1+(3863286091/10000000000 : ℝ)*X 1 2+(420216683/1000000000 : ℝ)*X 2 0+(228173937/500000000 : ℝ)*X 2 1+(3863286091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (348183807410687436069032859/129718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (419599233/100000000000000 : ℝ)*(base19) + (406361431/100000000000000 : ℝ)*(base23) + (4228231/25000000000000 : ℝ)*(lower2) + (2499899/3125000000000 : ℝ)*(upper3) + (35018001/100000000000000 : ℝ)*(upper5) + (614401005492579/25000000000000 : ℝ)*(major0) + (614401005492579/25000000000000 : ℝ)*(major1) + (614401005492579/25000000000000 : ℝ)*(major2) + (1754668742688597/50000000000000 : ℝ)*(sp0) + (1754670809072679/50000000000000 : ℝ)*(sp1) + (3509341631383161/100000000000000 : ℝ)*(sp2) + (70293180952033/5000000000000 : ℝ)*(sp3) + (2276183699/50000000000000 : ℝ)*(sp4) + (574420977/25000000000000 : ℝ)*(sp7) + (175733239590571/12500000000000 : ℝ)*(f.failure) + (219333877359037/6250000000000 : ℝ)*(f.sum) + (19282158426709/5188750000000000000000000000 : ℝ)*base65 + (124185307741256471/37062500000000000000000000000000 : ℝ)*base68 + (116638106308756471/37062500000000000000000000000000 : ℝ)*base70 + (176047383607506471/37062500000000000000000000000000 : ℝ)*base72 + (12168068415987/10377500000000000000000000000 : ℝ)*base74 + (68141647086993529/37062500000000000000000000000000 : ℝ)*base75 + (246263583526431029/37062500000000000000000000000000 : ℝ)*base77 + (387042728580756471/37062500000000000000000000000000 : ℝ)*base80 + (1081604667139/5188750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (364279/625000000000000000000 : ℝ)*base89 + (364279/625000000000000000000 : ℝ)*base91 + (364279/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20624842641005159326665327/3242968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (925184231/100000000000000 : ℝ)*(base19) + (56319777/6250000000000 : ℝ)*(base23) + (8863987/12500000000000 : ℝ)*(upper3) + (55958403/100000000000000 : ℝ)*(lower4) + (24731497/12500000000000 : ℝ)*(upper5) + (487618390103/19531250000 : ℝ)*(major0) + (487618390103/19531250000 : ℝ)*(major1) + (487618390103/19531250000 : ℝ)*(major2) + (2277451927/25000000000000 : ℝ)*(sp1) + (10163025209/100000000000000 : ℝ)*(sp2) + (3565035116987921/100000000000000 : ℝ)*(sp4) + (1782512540997991/50000000000000 : ℝ)*(sp5) + (89125601321157/2500000000000 : ℝ)*(sp6) + (14281769856713/1000000000000 : ℝ)*(sp7) + (14281769856713/1000000000000 : ℝ)*(f.failure) + (3565035116987921/100000000000000 : ℝ)*(f.sum) + (6294037174259/2075500000000000000000000000 : ℝ)*base65 + (10892867860436567/1853125000000000000000000000000 : ℝ)*base67 + (1368796909466721/926562500000000000000000000000 : ℝ)*base69 + (3303233839679221/926562500000000000000000000000 : ℝ)*base71 + (549079919817/259437500000000000000000000 : ℝ)*base73 + (16847087019329221/926562500000000000000000000000 : ℝ)*base75 + (10761773042817817/1853125000000000000000000000000 : ℝ)*base77 + (3673807011479221/926562500000000000000000000000 : ℝ)*base79 + (10030942842107/2075500000000000000000000000 : ℝ)*base82 + (242163/50000000000000000000 : ℝ)*base90 + (242163/50000000000000000000 : ℝ)*base92 + (242163/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1622_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17639/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1622_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1622_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1622_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1622_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1622_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1622_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
