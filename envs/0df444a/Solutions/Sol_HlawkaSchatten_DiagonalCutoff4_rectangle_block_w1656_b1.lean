-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1656_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:10.909682+00:00
-- url     : https://prove2.me/submissions/875d4118-7a4d-4cbf-8470-1d5d094d630e

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
theorem support_rectangle_w1656_s3_0 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-797485807/5000000000 : ℝ)*x 0 + (5445821393/10000000000 : ℝ)*x 1 + (5184235847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (797485807/5000000000 : ℝ)^4943 ≤ (1974555571587/20000000000000 : ℝ)^3919 := by
    have hnat : (797485807 : ℕ)^4943*20000000000000^3919 ≤ 1974555571587^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797485807 5000000000 1974555571587 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445821393/10000000000 : ℝ)^4943 ≤ (23231063917327/50000000000000 : ℝ)^3919 := by
    have hnat : (5445821393 : ℕ)^4943*50000000000000^3919 ≤ 23231063917327^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445821393 10000000000 23231063917327 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184235847/10000000000 : ℝ)^4943 ≤ (21832547147003/50000000000000 : ℝ)^3919 := by
    have hnat : (5184235847 : ℕ)^4943*50000000000000^3919 ≤ 21832547147003^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184235847 10000000000 21832547147003 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-797485807/5000000000 : ℝ), (5445821393/10000000000 : ℝ), (5184235847/10000000000 : ℝ)] ![(1974555571587/20000000000000 : ℝ), (23231063917327/50000000000000 : ℝ), (21832547147003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-797485807/5000000000 : ℝ)|^4943 ≤ (1974555571587/20000000000000 : ℝ)^3919
        have hw : |(-797485807/5000000000 : ℝ)|=(797485807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445821393/10000000000 : ℝ)|^4943 ≤ (23231063917327/50000000000000 : ℝ)^3919
        have hw : |(5445821393/10000000000 : ℝ)|=(5445821393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184235847/10000000000 : ℝ)|^4943 ≤ (21832547147003/50000000000000 : ℝ)^3919
        have hw : |(5184235847/10000000000 : ℝ)|=(5184235847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_1 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334178231/625000000 : ℝ)*x 0 + (-1729603101/10000000000 : ℝ)*x 1 + (2592117899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334178231/625000000 : ℝ)^4943 ≤ (4539965885131/10000000000000 : ℝ)^3919 := by
    have hnat : (334178231 : ℕ)^4943*10000000000000^3919 ≤ 4539965885131^3919*625000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334178231 625000000 4539965885131 10000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729603101/10000000000 : ℝ)^4943 ≤ (5467623680641/50000000000000 : ℝ)^3919 := by
    have hnat : (1729603101 : ℕ)^4943*50000000000000^3919 ≤ 5467623680641^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729603101 10000000000 5467623680641 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592117899/5000000000 : ℝ)^4943 ≤ (21832546886729/50000000000000 : ℝ)^3919 := by
    have hnat : (2592117899 : ℕ)^4943*50000000000000^3919 ≤ 21832546886729^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592117899 5000000000 21832546886729 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334178231/625000000 : ℝ), (-1729603101/10000000000 : ℝ), (2592117899/5000000000 : ℝ)] ![(4539965885131/10000000000000 : ℝ), (5467623680641/50000000000000 : ℝ), (21832546886729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334178231/625000000 : ℝ)|^4943 ≤ (4539965885131/10000000000000 : ℝ)^3919
        have hw : |(334178231/625000000 : ℝ)|=(334178231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729603101/10000000000 : ℝ)|^4943 ≤ (5467623680641/50000000000000 : ℝ)^3919
        have hw : |(-1729603101/10000000000 : ℝ)|=(1729603101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592117899/5000000000 : ℝ)|^4943 ≤ (21832546886729/50000000000000 : ℝ)^3919
        have hw : |(2592117899/5000000000 : ℝ)|=(2592117899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_2 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069370447/2000000000 : ℝ)*x 0 + (5184235401/10000000000 : ℝ)*x 1 + (-1729602907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069370447/2000000000 : ℝ)^4943 ≤ (22699832311869/50000000000000 : ℝ)^3919 := by
    have hnat : (1069370447 : ℕ)^4943*50000000000000^3919 ≤ 22699832311869^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069370447 2000000000 22699832311869 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184235401/10000000000 : ℝ)^4943 ≤ (21832544777977/50000000000000 : ℝ)^3919 := by
    have hnat : (5184235401 : ℕ)^4943*50000000000000^3919 ≤ 21832544777977^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184235401 10000000000 21832544777977 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1729602907/10000000000 : ℝ)^4943 ≤ (43740983257/400000000000 : ℝ)^3919 := by
    have hnat : (1729602907 : ℕ)^4943*400000000000^3919 ≤ 43740983257^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729602907 10000000000 43740983257 400000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069370447/2000000000 : ℝ), (5184235401/10000000000 : ℝ), (-1729602907/10000000000 : ℝ)] ![(22699832311869/50000000000000 : ℝ), (21832544777977/50000000000000 : ℝ), (43740983257/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069370447/2000000000 : ℝ)|^4943 ≤ (22699832311869/50000000000000 : ℝ)^3919
        have hw : |(1069370447/2000000000 : ℝ)|=(1069370447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184235401/10000000000 : ℝ)|^4943 ≤ (21832544777977/50000000000000 : ℝ)^3919
        have hw : |(5184235401/10000000000 : ℝ)|=(5184235401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1729602907/10000000000 : ℝ)|^4943 ≤ (43740983257/400000000000 : ℝ)^3919
        have hw : |(-1729602907/10000000000 : ℝ)|=(1729602907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_3 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835228757/2000000000 : ℝ)*x 0 + (769039517/2000000000 : ℝ)*x 1 + (282943929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835228757/2000000000 : ℝ)^4943 ≤ (16621010674793/50000000000000 : ℝ)^3919 := by
    have hnat : (835228757 : ℕ)^4943*50000000000000^3919 ≤ 16621010674793^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835228757 2000000000 16621010674793 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769039517/2000000000 : ℝ)^4943 ≤ (29954466028861/100000000000000 : ℝ)^3919 := by
    have hnat : (769039517 : ℕ)^4943*100000000000000^3919 ≤ 29954466028861^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769039517 2000000000 29954466028861 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282943929/625000000 : ℝ)^4943 ≤ (36803512616913/100000000000000 : ℝ)^3919 := by
    have hnat : (282943929 : ℕ)^4943*100000000000000^3919 ≤ 36803512616913^3919*625000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282943929 625000000 36803512616913 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835228757/2000000000 : ℝ), (769039517/2000000000 : ℝ), (282943929/625000000 : ℝ)] ![(16621010674793/50000000000000 : ℝ), (29954466028861/100000000000000 : ℝ), (36803512616913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835228757/2000000000 : ℝ)|^4943 ≤ (16621010674793/50000000000000 : ℝ)^3919
        have hw : |(835228757/2000000000 : ℝ)|=(835228757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769039517/2000000000 : ℝ)|^4943 ≤ (29954466028861/100000000000000 : ℝ)^3919
        have hw : |(769039517/2000000000 : ℝ)|=(769039517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282943929/625000000 : ℝ)|^4943 ≤ (36803512616913/100000000000000 : ℝ)^3919
        have hw : |(282943929/625000000 : ℝ)|=(282943929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_4 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398758913/2500000000 : ℝ)*x 0 + (324138829/625000000 : ℝ)*x 1 + (2721907347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398758913/2500000000 : ℝ)^4943 ≤ (1974655565091/20000000000000 : ℝ)^3919 := by
    have hnat : (398758913 : ℕ)^4943*20000000000000^3919 ≤ 1974655565091^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398758913 2500000000 1974655565091 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324138829/625000000 : ℝ)^4943 ≤ (43686187299293/100000000000000 : ℝ)^3919 := by
    have hnat : (324138829 : ℕ)^4943*100000000000000^3919 ≤ 43686187299293^3919*625000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324138829 625000000 43686187299293 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721907347/5000000000 : ℝ)^4943 ≤ (46440534865057/100000000000000 : ℝ)^3919 := by
    have hnat : (2721907347 : ℕ)^4943*100000000000000^3919 ≤ 46440534865057^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721907347 5000000000 46440534865057 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398758913/2500000000 : ℝ), (324138829/625000000 : ℝ), (2721907347/5000000000 : ℝ)] ![(1974655565091/20000000000000 : ℝ), (43686187299293/100000000000000 : ℝ), (46440534865057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398758913/2500000000 : ℝ)|^4943 ≤ (1974655565091/20000000000000 : ℝ)^3919
        have hw : |(-398758913/2500000000 : ℝ)|=(398758913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324138829/625000000 : ℝ)|^4943 ≤ (43686187299293/100000000000000 : ℝ)^3919
        have hw : |(324138829/625000000 : ℝ)|=(324138829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721907347/5000000000 : ℝ)|^4943 ≤ (46440534865057/100000000000000 : ℝ)^3919
        have hw : |(2721907347/5000000000 : ℝ)|=(2721907347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_5 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638459957/5000000000 : ℝ)*x 0 + (-36750607/250000000 : ℝ)*x 1 + (2721907349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638459957/5000000000 : ℝ)^4943 ≤ (1786080290363/4000000000000 : ℝ)^3919 := by
    have hnat : (2638459957 : ℕ)^4943*4000000000000^3919 ≤ 1786080290363^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638459957 5000000000 1786080290363 4000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36750607/250000000 : ℝ)^4943 ≤ (4453728911303/50000000000000 : ℝ)^3919 := by
    have hnat : (36750607 : ℕ)^4943*50000000000000^3919 ≤ 4453728911303^3919*250000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36750607 250000000 4453728911303 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721907349/5000000000 : ℝ)^4943 ≤ (46440534908097/100000000000000 : ℝ)^3919 := by
    have hnat : (2721907349 : ℕ)^4943*100000000000000^3919 ≤ 46440534908097^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721907349 5000000000 46440534908097 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638459957/5000000000 : ℝ), (-36750607/250000000 : ℝ), (2721907349/5000000000 : ℝ)] ![(1786080290363/4000000000000 : ℝ), (4453728911303/50000000000000 : ℝ), (46440534908097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638459957/5000000000 : ℝ)|^4943 ≤ (1786080290363/4000000000000 : ℝ)^3919
        have hw : |(2638459957/5000000000 : ℝ)|=(2638459957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36750607/250000000 : ℝ)|^4943 ≤ (4453728911303/50000000000000 : ℝ)^3919
        have hw : |(-36750607/250000000 : ℝ)|=(36750607/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721907349/5000000000 : ℝ)|^4943 ≤ (46440534908097/100000000000000 : ℝ)^3919
        have hw : |(2721907349/5000000000 : ℝ)|=(2721907349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_6 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276919771/10000000000 : ℝ)*x 0 + (5443814819/10000000000 : ℝ)*x 1 + (-367506077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276919771/10000000000 : ℝ)^4943 ≤ (22326002866437/50000000000000 : ℝ)^3919 := by
    have hnat : (5276919771 : ℕ)^4943*50000000000000^3919 ≤ 22326002866437^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276919771 10000000000 22326002866437 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443814819/10000000000 : ℝ)^4943 ≤ (362816689141/781250000000 : ℝ)^3919 := by
    have hnat : (5443814819 : ℕ)^4943*781250000000^3919 ≤ 362816689141^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443814819 10000000000 362816689141 781250000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367506077/2500000000 : ℝ)^4943 ≤ (8907458036601/100000000000000 : ℝ)^3919 := by
    have hnat : (367506077 : ℕ)^4943*100000000000000^3919 ≤ 8907458036601^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367506077 2500000000 8907458036601 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276919771/10000000000 : ℝ), (5443814819/10000000000 : ℝ), (-367506077/2500000000 : ℝ)] ![(22326002866437/50000000000000 : ℝ), (362816689141/781250000000 : ℝ), (8907458036601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276919771/10000000000 : ℝ)|^4943 ≤ (22326002866437/50000000000000 : ℝ)^3919
        have hw : |(5276919771/10000000000 : ℝ)|=(5276919771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443814819/10000000000 : ℝ)|^4943 ≤ (362816689141/781250000000 : ℝ)^3919
        have hw : |(5443814819/10000000000 : ℝ)|=(5443814819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367506077/2500000000 : ℝ)|^4943 ≤ (8907458036601/100000000000000 : ℝ)^3919
        have hw : |(-367506077/2500000000 : ℝ)|=(367506077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s3_7 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044077413/2500000000 : ℝ)*x 0 + (4521927023/10000000000 : ℝ)*x 1 + (385042777/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044077413/2500000000 : ℝ)^4943 ≤ (1329747465537/4000000000000 : ℝ)^3919 := by
    have hnat : (1044077413 : ℕ)^4943*4000000000000^3919 ≤ 1329747465537^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044077413 2500000000 1329747465537 4000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521927023/10000000000 : ℝ)^4943 ≤ (4593806072457/12500000000000 : ℝ)^3919 := by
    have hnat : (4521927023 : ℕ)^4943*12500000000000^3919 ≤ 4593806072457^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521927023 10000000000 4593806072457 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385042777/1000000000 : ℝ)^4943 ≤ (3750733095943/12500000000000 : ℝ)^3919 := by
    have hnat : (385042777 : ℕ)^4943*12500000000000^3919 ≤ 3750733095943^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385042777 1000000000 3750733095943 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044077413/2500000000 : ℝ), (4521927023/10000000000 : ℝ), (385042777/1000000000 : ℝ)] ![(1329747465537/4000000000000 : ℝ), (4593806072457/12500000000000 : ℝ), (3750733095943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044077413/2500000000 : ℝ)|^4943 ≤ (1329747465537/4000000000000 : ℝ)^3919
        have hw : |(1044077413/2500000000 : ℝ)|=(1044077413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521927023/10000000000 : ℝ)|^4943 ≤ (4593806072457/12500000000000 : ℝ)^3919
        have hw : |(4521927023/10000000000 : ℝ)|=(4521927023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385042777/1000000000 : ℝ)|^4943 ≤ (3750733095943/12500000000000 : ℝ)^3919
        have hw : |(385042777/1000000000 : ℝ)|=(385042777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1656_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10697/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (813/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5319/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5319/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5319/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5319/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5319/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5319/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5319/50000 : ℝ) ^ (4939/1024 : ℝ) ≤ (404892773632927/20000000000000000000 : ℝ) := by
    have hpowers : (5319/50000 : ℝ)^4939 ≤ (404892773632927/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5319 : ℕ)^4939*20000000000000000000^1024 ≤ 404892773632927^1024*50000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5319 50000 404892773632927 20000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5319/50000 : ℝ)) (X := (404892773632927/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8163/50000 : ℝ) ^ (4939/1024 : ℝ) ≤ (3195645547998089/20000000000000000000 : ℝ) := by
    have hpowers : (8163/50000 : ℝ)^4939 ≤ (3195645547998089/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8163 : ℕ)^4939*20000000000000000000^1024 ≤ 3195645547998089^1024*50000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8163 50000 3195645547998089 20000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8163/50000 : ℝ)) (X := (3195645547998089/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000404892773632927/10000000000000000000 : ℝ) ≤ (10000083944836399/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (10000404892773632927/10000000000000000000 : ℝ)^1024 ≤ (10000083944836399/10000000000000000 : ℝ)^4939 := by
      have hnat : (10000404892773632927 : ℕ)^1024*10000000000000000^4939 ≤ 10000083944836399^4939*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000404892773632927 10000000000000000000 10000083944836399 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083944836399/10000000000000000 : ℝ)) (X := (10000404892773632927/10000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500450067290203877/2500000000000000000 : ℝ) ≤ (500018661106509/500000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (2500450067290203877/2500000000000000000 : ℝ)^1024 ≤ (500018661106509/500000000000000 : ℝ)^4939 := by
      have hnat : (2500450067290203877 : ℕ)^1024*500000000000000^4939 ≤ 500018661106509^4939*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500450067290203877 2500000000000000000 500018661106509 500000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500018661106509/500000000000000 : ℝ)) (X := (2500450067290203877/2500000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003195645547998089/10000000000000000000 : ℝ) ≤ (10000662499423961/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (10003195645547998089/10000000000000000000 : ℝ)^1024 ≤ (10000662499423961/10000000000000000 : ℝ)^4939 := by
      have hnat : (10003195645547998089 : ℕ)^1024*10000000000000000^4939 ≤ 10000662499423961^4939*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003195645547998089 10000000000000000000 10000662499423961 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000662499423961/10000000000000000 : ℝ)) (X := (10003195645547998089/10000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(404892773632927/20000000000000000000 : ℝ) ≤ ((1579842300403526471/1580000000000000000 : ℝ)+2*(289277293781/568800000000000 : ℝ)*(5319/50000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (1579842300403526471/1580000000000000000 : ℝ)+2*(289277293781/568800000000000 : ℝ)*(5319/50000 : ℝ)=(10000083944836399/10000000000000000 : ℝ) by norm_num, show 1+2*(404892773632927/20000000000000000000 : ℝ)=(10000404892773632927/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3195645547998089/20000000000000000000 : ℝ)+(404892773632927/20000000000000000000 : ℝ) ≤ ((1579842300403526471/1580000000000000000 : ℝ)+(289277293781/568800000000000 : ℝ)*((8163/50000 : ℝ)+(5319/50000 : ℝ)))^(4939/1024 : ℝ) := by
    rw [show (1579842300403526471/1580000000000000000 : ℝ)+(289277293781/568800000000000 : ℝ)*((8163/50000 : ℝ)+(5319/50000 : ℝ))=(500018661106509/500000000000000 : ℝ) by norm_num, show 1+(3195645547998089/20000000000000000000 : ℝ)+(404892773632927/20000000000000000000 : ℝ)=(2500450067290203877/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3195645547998089/20000000000000000000 : ℝ) ≤ ((1579842300403526471/1580000000000000000 : ℝ)+2*(289277293781/568800000000000 : ℝ)*(8163/50000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (1579842300403526471/1580000000000000000 : ℝ)+2*(289277293781/568800000000000 : ℝ)*(8163/50000 : ℝ)=(10000662499423961/10000000000000000 : ℝ) by norm_num, show 1+2*(3195645547998089/20000000000000000000 : ℝ)=(10003195645547998089/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1579842300403526471/1580000000000000000 : ℝ)*(X 1 0+X 2 0)+(289277293781/568800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (5319/50000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (1579842300403526471/1580000000000000000 : ℝ)) (alpha := (289277293781/568800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1579842300403526471/1580000000000000000 : ℝ)*(X 0 1+X 2 1)+(289277293781/568800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (5319/50000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (1579842300403526471/1580000000000000000 : ℝ)) (alpha := (289277293781/568800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1579842300403526471/1580000000000000000 : ℝ)*(X 0 2+X 1 2)+(289277293781/568800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (5319/50000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (1579842300403526471/1580000000000000000 : ℝ)) (alpha := (289277293781/568800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-797485807/5000000000 : ℝ)*X 0 0+(5445821393/10000000000 : ℝ)*X 0 1+(5184235847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334178231/625000000 : ℝ)*X 1 0+(-1729603101/10000000000 : ℝ)*X 1 1+(2592117899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069370447/2000000000 : ℝ)*X 2 0+(5184235401/10000000000 : ℝ)*X 2 1+(-1729602907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835228757/2000000000 : ℝ)*X 0 0+(769039517/2000000000 : ℝ)*X 0 1+(282943929/625000000 : ℝ)*X 0 2+(835228757/2000000000 : ℝ)*X 1 0+(769039517/2000000000 : ℝ)*X 1 1+(282943929/625000000 : ℝ)*X 1 2+(835228757/2000000000 : ℝ)*X 2 0+(769039517/2000000000 : ℝ)*X 2 1+(282943929/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398758913/2500000000 : ℝ)*X 0 0+(324138829/625000000 : ℝ)*X 0 1+(2721907347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638459957/5000000000 : ℝ)*X 1 0+(-36750607/250000000 : ℝ)*X 1 1+(2721907349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276919771/10000000000 : ℝ)*X 2 0+(5443814819/10000000000 : ℝ)*X 2 1+(-367506077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044077413/2500000000 : ℝ)*X 0 0+(4521927023/10000000000 : ℝ)*X 0 1+(385042777/1000000000 : ℝ)*X 0 2+(1044077413/2500000000 : ℝ)*X 1 0+(4521927023/10000000000 : ℝ)*X 1 1+(385042777/1000000000 : ℝ)*X 1 2+(1044077413/2500000000 : ℝ)*X 2 0+(4521927023/10000000000 : ℝ)*X 2 1+(385042777/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118775127025760799425123/9480000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1942267777/100000000000000 : ℝ)*(base19) + (1932057047/100000000000000 : ℝ)*(base23) + (1692107/800000000000 : ℝ)*(lower2) + (192472067/100000000000000 : ℝ)*(upper3) + (23725859/20000000000000 : ℝ)*(upper5) + (2644696211172463/100000000000000 : ℝ)*(major0) + (2644696211172463/100000000000000 : ℝ)*(major1) + (2644696211172463/100000000000000 : ℝ)*(major2) + (3822865494416231/100000000000000 : ℝ)*(sp0) + (1911445724555137/50000000000000 : ℝ)*(sp1) + (3822891459321003/100000000000000 : ℝ)*(sp2) + (1466487819452907/100000000000000 : ℝ)*(sp3) + (27896961819/100000000000000 : ℝ)*(sp4) + (5396939951/50000000000000 : ℝ)*(sp7) + (1466498613332809/100000000000000 : ℝ)*(f.failure) + (76457867827561/2000000000000 : ℝ)*(f.sum) + (70143604514723/28440000000000000000000000000 : ℝ)*base65 + (3847075561764012343/1422000000000000000000000000000000 : ℝ)*base68 + (1074936176766012343/1422000000000000000000000000000000 : ℝ)*base70 + (1842913157849987657/1422000000000000000000000000000000 : ℝ)*base71 + (18038949456877/28440000000000000000000000000 : ℝ)*base74 + (10179131356764012343/1422000000000000000000000000000000 : ℝ)*base76 + (1494427882427987657/1422000000000000000000000000000000 : ℝ)*base77 + (2331118832147987657/1422000000000000000000000000000000 : ℝ)*base79 + (6005610048877/28440000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2936213/500000000000000000000 : ℝ)*base90 + (2936213/500000000000000000000 : ℝ)*base92 + (2936213/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14358283277406688821451873/2468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41378879/5000000000000 : ℝ)*(base19) + (382676893/50000000000000 : ℝ)*(base23) + (71800629/50000000000000 : ℝ)*(upper3) + (18966921/100000000000000 : ℝ)*(lower4) + (21319313/20000000000000 : ℝ)*(upper5) + (83926408419057/3125000000000 : ℝ)*(major0) + (83926408419057/3125000000000 : ℝ)*(major1) + (83926408419057/3125000000000 : ℝ)*(major2) + (452677889/5000000000000 : ℝ)*(sp1) + (4792125437/50000000000000 : ℝ)*(sp2) + (1941042482111677/50000000000000 : ℝ)*(sp4) + (1941037541543997/50000000000000 : ℝ)*(sp5) + (1941037307309347/50000000000000 : ℝ)*(sp6) + (1489204980729173/100000000000000 : ℝ)*(sp7) + (1489204980729173/100000000000000 : ℝ)*(f.failure) + (1941042482111677/50000000000000 : ℝ)*(f.sum) + (9124490893/37031250000000000000000000 : ℝ)*base65 + (45331054853888959/14812500000000000000000000000000 : ℝ)*base68 + (109465572284326459/14812500000000000000000000000000 : ℝ)*base70 + (113398103004451459/14812500000000000000000000000000 : ℝ)*base72 + (4286487302741/1185000000000000000000000000 : ℝ)*base73 + (57603759566326459/14812500000000000000000000000000 : ℝ)*base76 + (75811311199201459/14812500000000000000000000000000 : ℝ)*base78 + (130168425150638959/14812500000000000000000000000000 : ℝ)*base80 + (135250641409/74062500000000000000000000 : ℝ)*base82 + (4295439/500000000000000000000 : ℝ)*base89 + (4295439/500000000000000000000 : ℝ)*base91 + (4295439/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1656_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (813/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1656_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1656_s4_0 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-319002307/2000000000 : ℝ)*x 0 + (5445622389/10000000000 : ℝ)*x 1 + (5184408087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319002307/2000000000 : ℝ)^4943 ≤ (4936544767407/50000000000000 : ℝ)^3919 := by
    have hnat : (319002307 : ℕ)^4943*50000000000000^3919 ≤ 4936544767407^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319002307 2000000000 4936544767407 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445622389/10000000000 : ℝ)^4943 ≤ (23229993185319/50000000000000 : ℝ)^3919 := by
    have hnat : (5445622389 : ℕ)^4943*50000000000000^3919 ≤ 23229993185319^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445622389 10000000000 23229993185319 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184408087/10000000000 : ℝ)^4943 ≤ (8733384816507/20000000000000 : ℝ)^3919 := by
    have hnat : (5184408087 : ℕ)^4943*20000000000000^3919 ≤ 8733384816507^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184408087 10000000000 8733384816507 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-319002307/2000000000 : ℝ), (5445622389/10000000000 : ℝ), (5184408087/10000000000 : ℝ)] ![(4936544767407/50000000000000 : ℝ), (23229993185319/50000000000000 : ℝ), (8733384816507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-319002307/2000000000 : ℝ)|^4943 ≤ (4936544767407/50000000000000 : ℝ)^3919
        have hw : |(-319002307/2000000000 : ℝ)|=(319002307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445622389/10000000000 : ℝ)|^4943 ≤ (23229993185319/50000000000000 : ℝ)^3919
        have hw : |(5445622389/10000000000 : ℝ)|=(5445622389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184408087/10000000000 : ℝ)|^4943 ≤ (8733384816507/20000000000000 : ℝ)^3919
        have hw : |(5184408087/10000000000 : ℝ)|=(5184408087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_1 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673398723/5000000000 : ℝ)*x 0 + (-1729446207/10000000000 : ℝ)*x 1 + (81006379/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673398723/5000000000 : ℝ)^4943 ≤ (22699538930449/50000000000000 : ℝ)^3919 := by
    have hnat : (2673398723 : ℕ)^4943*50000000000000^3919 ≤ 22699538930449^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673398723 5000000000 22699538930449 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729446207/10000000000 : ℝ)^4943 ≤ (5466998121037/50000000000000 : ℝ)^3919 := by
    have hnat : (1729446207 : ℕ)^4943*50000000000000^3919 ≤ 5466998121037^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729446207 10000000000 5466998121037 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81006379/156250000 : ℝ)^4943 ≤ (43666925877911/100000000000000 : ℝ)^3919 := by
    have hnat : (81006379 : ℕ)^4943*100000000000000^3919 ≤ 43666925877911^3919*156250000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81006379 156250000 43666925877911 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673398723/5000000000 : ℝ), (-1729446207/10000000000 : ℝ), (81006379/156250000 : ℝ)] ![(22699538930449/50000000000000 : ℝ), (5466998121037/50000000000000 : ℝ), (43666925877911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673398723/5000000000 : ℝ)|^4943 ≤ (22699538930449/50000000000000 : ℝ)^3919
        have hw : |(2673398723/5000000000 : ℝ)|=(2673398723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729446207/10000000000 : ℝ)|^4943 ≤ (5466998121037/50000000000000 : ℝ)^3919
        have hw : |(-1729446207/10000000000 : ℝ)|=(1729446207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81006379/156250000 : ℝ)|^4943 ≤ (43666925877911/100000000000000 : ℝ)^3919
        have hw : |(81006379/156250000 : ℝ)|=(81006379/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_2 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167087421/312500000 : ℝ)*x 0 + (5184408267/10000000000 : ℝ)*x 1 + (-864723079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167087421/312500000 : ℝ)^4943 ≤ (9079815627869/20000000000000 : ℝ)^3919 := by
    have hnat : (167087421 : ℕ)^4943*20000000000000^3919 ≤ 9079815627869^3919*312500000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167087421 312500000 9079815627869 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184408267/10000000000 : ℝ)^4943 ≤ (4366692599477/10000000000000 : ℝ)^3919 := by
    have hnat : (5184408267 : ℕ)^4943*10000000000000^3919 ≤ 4366692599477^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184408267 10000000000 4366692599477 10000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864723079/5000000000 : ℝ)^4943 ≤ (5466997925669/50000000000000 : ℝ)^3919 := by
    have hnat : (864723079 : ℕ)^4943*50000000000000^3919 ≤ 5466997925669^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864723079 5000000000 5466997925669 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167087421/312500000 : ℝ), (5184408267/10000000000 : ℝ), (-864723079/5000000000 : ℝ)] ![(9079815627869/20000000000000 : ℝ), (4366692599477/10000000000000 : ℝ), (5466997925669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167087421/312500000 : ℝ)|^4943 ≤ (9079815627869/20000000000000 : ℝ)^3919
        have hw : |(167087421/312500000 : ℝ)|=(167087421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184408267/10000000000 : ℝ)|^4943 ≤ (4366692599477/10000000000000 : ℝ)^3919
        have hw : |(5184408267/10000000000 : ℝ)|=(5184408267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864723079/5000000000 : ℝ)|^4943 ≤ (5466997925669/50000000000000 : ℝ)^3919
        have hw : |(-864723079/5000000000 : ℝ)|=(864723079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_3 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088084893/5000000000 : ℝ)*x 0 + (3845678777/10000000000 : ℝ)*x 1 + (1131654073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088084893/5000000000 : ℝ)^4943 ≤ (33242282396001/100000000000000 : ℝ)^3919 := by
    have hnat : (2088084893 : ℕ)^4943*100000000000000^3919 ≤ 33242282396001^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088084893 5000000000 33242282396001 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3845678777/10000000000 : ℝ)^4943 ≤ (7489798524359/25000000000000 : ℝ)^3919 := by
    have hnat : (3845678777 : ℕ)^4943*25000000000000^3919 ≤ 7489798524359^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845678777 10000000000 7489798524359 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131654073/2500000000 : ℝ)^4943 ≤ (36798523481743/100000000000000 : ℝ)^3919 := by
    have hnat : (1131654073 : ℕ)^4943*100000000000000^3919 ≤ 36798523481743^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131654073 2500000000 36798523481743 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088084893/5000000000 : ℝ), (3845678777/10000000000 : ℝ), (1131654073/2500000000 : ℝ)] ![(33242282396001/100000000000000 : ℝ), (7489798524359/25000000000000 : ℝ), (36798523481743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088084893/5000000000 : ℝ)|^4943 ≤ (33242282396001/100000000000000 : ℝ)^3919
        have hw : |(2088084893/5000000000 : ℝ)|=(2088084893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3845678777/10000000000 : ℝ)|^4943 ≤ (7489798524359/25000000000000 : ℝ)^3919
        have hw : |(3845678777/10000000000 : ℝ)|=(3845678777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131654073/2500000000 : ℝ)|^4943 ≤ (36798523481743/100000000000000 : ℝ)^3919
        have hw : |(1131654073/2500000000 : ℝ)|=(1131654073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_4 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1595074577/10000000000 : ℝ)*x 0 + (1037277601/2000000000 : ℝ)*x 1 + (2721810903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1595074577/10000000000 : ℝ)^4943 ≤ (1974716345877/20000000000000 : ℝ)^3919 := by
    have hnat : (1595074577 : ℕ)^4943*20000000000000^3919 ≤ 1974716345877^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595074577 10000000000 1974716345877 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037277601/2000000000 : ℝ)^4943 ≤ (43687958846277/100000000000000 : ℝ)^3919 := by
    have hnat : (1037277601 : ℕ)^4943*100000000000000^3919 ≤ 43687958846277^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037277601 2000000000 43687958846277 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721810903/5000000000 : ℝ)^4943 ≤ (725600928349/1562500000000 : ℝ)^3919 := by
    have hnat : (2721810903 : ℕ)^4943*1562500000000^3919 ≤ 725600928349^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721810903 5000000000 725600928349 1562500000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1595074577/10000000000 : ℝ), (1037277601/2000000000 : ℝ), (2721810903/5000000000 : ℝ)] ![(1974716345877/20000000000000 : ℝ), (43687958846277/100000000000000 : ℝ), (725600928349/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1595074577/10000000000 : ℝ)|^4943 ≤ (1974716345877/20000000000000 : ℝ)^3919
        have hw : |(-1595074577/10000000000 : ℝ)|=(1595074577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037277601/2000000000 : ℝ)|^4943 ≤ (43687958846277/100000000000000 : ℝ)^3919
        have hw : |(1037277601/2000000000 : ℝ)|=(1037277601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721810903/5000000000 : ℝ)|^4943 ≤ (725600928349/1562500000000 : ℝ)^3919
        have hw : |(2721810903/5000000000 : ℝ)|=(2721810903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_5 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10553931/20000000 : ℝ)*x 0 + (-1470232279/10000000000 : ℝ)*x 1 + (5443621737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10553931/20000000 : ℝ)^4943 ≤ (44652493787039/100000000000000 : ℝ)^3919 := by
    have hnat : (10553931 : ℕ)^4943*100000000000000^3919 ≤ 44652493787039^3919*20000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10553931 20000000 44652493787039 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1470232279/10000000000 : ℝ)^4943 ≤ (89090475179/1000000000000 : ℝ)^3919 := by
    have hnat : (1470232279 : ℕ)^4943*1000000000000^3919 ≤ 89090475179^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470232279 10000000000 89090475179 1000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443621737/10000000000 : ℝ)^4943 ≤ (11609614667977/25000000000000 : ℝ)^3919 := by
    have hnat : (5443621737 : ℕ)^4943*25000000000000^3919 ≤ 11609614667977^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443621737 10000000000 11609614667977 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10553931/20000000 : ℝ), (-1470232279/10000000000 : ℝ), (5443621737/10000000000 : ℝ)] ![(44652493787039/100000000000000 : ℝ), (89090475179/1000000000000 : ℝ), (11609614667977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10553931/20000000 : ℝ)|^4943 ≤ (44652493787039/100000000000000 : ℝ)^3919
        have hw : |(10553931/20000000 : ℝ)|=(10553931/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1470232279/10000000000 : ℝ)|^4943 ≤ (89090475179/1000000000000 : ℝ)^3919
        have hw : |(-1470232279/10000000000 : ℝ)|=(1470232279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443621737/10000000000 : ℝ)|^4943 ≤ (11609614667977/25000000000000 : ℝ)^3919
        have hw : |(5443621737/10000000000 : ℝ)|=(5443621737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_6 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527696551/1000000000 : ℝ)*x 0 + (5443621427/10000000000 : ℝ)*x 1 + (-1470232703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527696551/1000000000 : ℝ)^4943 ≤ (44652493893767/100000000000000 : ℝ)^3919 := by
    have hnat : (527696551 : ℕ)^4943*100000000000000^3919 ≤ 44652493893767^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527696551 1000000000 44652493893767 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443621427/10000000000 : ℝ)^4943 ≤ (46438455336363/100000000000000 : ℝ)^3919 := by
    have hnat : (5443621427 : ℕ)^4943*100000000000000^3919 ≤ 46438455336363^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443621427 10000000000 46438455336363 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1470232703/10000000000 : ℝ)^4943 ≤ (2227262689627/25000000000000 : ℝ)^3919 := by
    have hnat : (1470232703 : ℕ)^4943*25000000000000^3919 ≤ 2227262689627^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470232703 10000000000 2227262689627 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527696551/1000000000 : ℝ), (5443621427/10000000000 : ℝ), (-1470232703/10000000000 : ℝ)] ![(44652493893767/100000000000000 : ℝ), (46438455336363/100000000000000 : ℝ), (2227262689627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527696551/1000000000 : ℝ)|^4943 ≤ (44652493893767/100000000000000 : ℝ)^3919
        have hw : |(527696551/1000000000 : ℝ)|=(527696551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443621427/10000000000 : ℝ)|^4943 ≤ (46438455336363/100000000000000 : ℝ)^3919
        have hw : |(5443621427/10000000000 : ℝ)|=(5443621427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1470232703/10000000000 : ℝ)|^4943 ≤ (2227262689627/25000000000000 : ℝ)^3919
        have hw : |(-1470232703/10000000000 : ℝ)|=(1470232703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_s4_7 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26102091/62500000 : ℝ)*x 0 + (282590941/625000000 : ℝ)*x 1 + (3850894527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26102091/62500000 : ℝ)^4943 ≤ (16621968356929/50000000000000 : ℝ)^3919 := by
    have hnat : (26102091 : ℕ)^4943*50000000000000^3919 ≤ 16621968356929^3919*62500000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26102091 62500000 16621968356929 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282590941/625000000 : ℝ)^4943 ≤ (36745610643267/100000000000000 : ℝ)^3919 := by
    have hnat : (282590941 : ℕ)^4943*100000000000000^3919 ≤ 36745610643267^3919*625000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282590941 625000000 36745610643267 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3850894527/10000000000 : ℝ)^4943 ≤ (30010452628331/100000000000000 : ℝ)^3919 := by
    have hnat : (3850894527 : ℕ)^4943*100000000000000^3919 ≤ 30010452628331^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3850894527 10000000000 30010452628331 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26102091/62500000 : ℝ), (282590941/625000000 : ℝ), (3850894527/10000000000 : ℝ)] ![(16621968356929/50000000000000 : ℝ), (36745610643267/100000000000000 : ℝ), (30010452628331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26102091/62500000 : ℝ)|^4943 ≤ (16621968356929/50000000000000 : ℝ)^3919
        have hw : |(26102091/62500000 : ℝ)|=(26102091/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282590941/625000000 : ℝ)|^4943 ≤ (36745610643267/100000000000000 : ℝ)^3919
        have hw : |(282590941/625000000 : ℝ)|=(282590941/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3850894527/10000000000 : ℝ)|^4943 ≤ (30010452628331/100000000000000 : ℝ)^3919
        have hw : |(3850894527/10000000000 : ℝ)|=(3850894527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1656_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10701/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (508/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (813/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (813/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (813/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (813/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (813/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (813/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10697/100000 : ℝ) ^ (4939/1024 : ℝ) ≤ (2079196355062263/100000000000000000000 : ℝ) := by
    have hpowers : (10697/100000 : ℝ)^4939 ≤ (2079196355062263/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10697 : ℕ)^4939*100000000000000000000^1024 ≤ 2079196355062263^1024*100000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10697 100000 2079196355062263 100000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10697/100000 : ℝ)) (X := (2079196355062263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (813/5000 : ℝ) ^ (4939/1024 : ℝ) ≤ (15669073355944029/100000000000000000000 : ℝ) := by
    have hpowers : (813/5000 : ℝ)^4939 ≤ (15669073355944029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (813 : ℕ)^4939*100000000000000000000^1024 ≤ 15669073355944029^1024*5000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813 5000 15669073355944029 100000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (813/5000 : ℝ)) (X := (15669073355944029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002079196355062263/50000000000000000000 : ℝ) ≤ (10000086214293519/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (50002079196355062263/50000000000000000000 : ℝ)^1024 ≤ (10000086214293519/10000000000000000 : ℝ)^4939 := by
      have hnat : (50002079196355062263 : ℕ)^1024*10000000000000000^4939 ≤ 10000086214293519^4939*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002079196355062263 50000000000000000000 10000086214293519 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000086214293519/10000000000000000 : ℝ)) (X := (50002079196355062263/50000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004437067427751573/25000000000000000000 : ℝ) ≤ (10000367947963073/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (25004437067427751573/25000000000000000000 : ℝ)^1024 ≤ (10000367947963073/10000000000000000 : ℝ)^4939 := by
      have hnat : (25004437067427751573 : ℕ)^1024*10000000000000000^4939 ≤ 10000367947963073^4939*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004437067427751573 25000000000000000000 10000367947963073 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000367947963073/10000000000000000 : ℝ)) (X := (25004437067427751573/25000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015669073355944029/50000000000000000000 : ℝ) ≤ (10000649681632627/10000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (50015669073355944029/50000000000000000000 : ℝ)^1024 ≤ (10000649681632627/10000000000000000 : ℝ)^4939 := by
      have hnat : (50015669073355944029 : ℕ)^1024*10000000000000000^4939 ≤ 10000649681632627^4939*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015669073355944029 50000000000000000000 10000649681632627 10000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000649681632627/10000000000000000 : ℝ)) (X := (50015669073355944029/50000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2079196355062263/100000000000000000000 : ℝ) ≤ ((55624452199988407921/55630000000000000000 : ℝ)+2*(140866834777/278150000000000 : ℝ)*(10697/100000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (55624452199988407921/55630000000000000000 : ℝ)+2*(140866834777/278150000000000 : ℝ)*(10697/100000 : ℝ)=(10000086214293519/10000000000000000 : ℝ) by norm_num, show 1+2*(2079196355062263/100000000000000000000 : ℝ)=(50002079196355062263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15669073355944029/100000000000000000000 : ℝ)+(2079196355062263/100000000000000000000 : ℝ) ≤ ((55624452199988407921/55630000000000000000 : ℝ)+(140866834777/278150000000000 : ℝ)*((813/5000 : ℝ)+(10697/100000 : ℝ)))^(4939/1024 : ℝ) := by
    rw [show (55624452199988407921/55630000000000000000 : ℝ)+(140866834777/278150000000000 : ℝ)*((813/5000 : ℝ)+(10697/100000 : ℝ))=(10000367947963073/10000000000000000 : ℝ) by norm_num, show 1+(15669073355944029/100000000000000000000 : ℝ)+(2079196355062263/100000000000000000000 : ℝ)=(25004437067427751573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15669073355944029/100000000000000000000 : ℝ) ≤ ((55624452199988407921/55630000000000000000 : ℝ)+2*(140866834777/278150000000000 : ℝ)*(813/5000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (55624452199988407921/55630000000000000000 : ℝ)+2*(140866834777/278150000000000 : ℝ)*(813/5000 : ℝ)=(10000649681632627/10000000000000000 : ℝ) by norm_num, show 1+2*(15669073355944029/100000000000000000000 : ℝ)=(50015669073355944029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55624452199988407921/55630000000000000000 : ℝ)*(X 1 0+X 2 0)+(140866834777/278150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (813/5000 : ℝ)) (c := (55624452199988407921/55630000000000000000 : ℝ)) (alpha := (140866834777/278150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55624452199988407921/55630000000000000000 : ℝ)*(X 0 1+X 2 1)+(140866834777/278150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (813/5000 : ℝ)) (c := (55624452199988407921/55630000000000000000 : ℝ)) (alpha := (140866834777/278150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55624452199988407921/55630000000000000000 : ℝ)*(X 0 2+X 1 2)+(140866834777/278150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (813/5000 : ℝ)) (c := (55624452199988407921/55630000000000000000 : ℝ)) (alpha := (140866834777/278150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-319002307/2000000000 : ℝ)*X 0 0+(5445622389/10000000000 : ℝ)*X 0 1+(5184408087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673398723/5000000000 : ℝ)*X 1 0+(-1729446207/10000000000 : ℝ)*X 1 1+(81006379/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167087421/312500000 : ℝ)*X 2 0+(5184408267/10000000000 : ℝ)*X 2 1+(-864723079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088084893/5000000000 : ℝ)*X 0 0+(3845678777/10000000000 : ℝ)*X 0 1+(1131654073/2500000000 : ℝ)*X 0 2+(2088084893/5000000000 : ℝ)*X 1 0+(3845678777/10000000000 : ℝ)*X 1 1+(1131654073/2500000000 : ℝ)*X 1 2+(2088084893/5000000000 : ℝ)*X 2 0+(3845678777/10000000000 : ℝ)*X 2 1+(1131654073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1595074577/10000000000 : ℝ)*X 0 0+(1037277601/2000000000 : ℝ)*X 0 1+(2721810903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10553931/20000000 : ℝ)*X 1 0+(-1470232279/10000000000 : ℝ)*X 1 1+(5443621737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527696551/1000000000 : ℝ)*X 2 0+(5443621427/10000000000 : ℝ)*X 2 1+(-1470232703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26102091/62500000 : ℝ)*X 0 0+(282590941/625000000 : ℝ)*X 0 1+(3850894527/10000000000 : ℝ)*X 0 2+(26102091/62500000 : ℝ)*X 1 0+(282590941/625000000 : ℝ)*X 1 1+(3850894527/10000000000 : ℝ)*X 1 2+(26102091/62500000 : ℝ)*X 2 0+(282590941/625000000 : ℝ)*X 2 1+(3850894527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27099576476416552108228549941/2781500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1369012033/100000000000000 : ℝ)*(base19) + (666505903/50000000000000 : ℝ)*(base23) + (14601101/50000000000000 : ℝ)*(lower2) + (213594907/100000000000000 : ℝ)*(upper3) + (216617767/100000000000000 : ℝ)*(upper5) + (2648445294062793/100000000000000 : ℝ)*(major0) + (2648445294062793/100000000000000 : ℝ)*(major1) + (2648445294062793/100000000000000 : ℝ)*(major2) + (1914146537000887/50000000000000 : ℝ)*(sp0) + (191415569695613/5000000000000 : ℝ)*(sp1) + (1914155714956243/50000000000000 : ℝ)*(sp2) + (1468570390676331/100000000000000 : ℝ)*(sp3) + (19688922517/100000000000000 : ℝ)*(sp4) + (3554882609/50000000000000 : ℝ)*(sp7) + (1468577500441549/100000000000000 : ℝ)*(f.failure) + (957078190731073/25000000000000 : ℝ)*(f.sum) + (30630157079983/27815000000000000000000000000 : ℝ)*base66 + (20133659261146783353/5563000000000000000000000000000000 : ℝ)*base67 + (34522901086890783353/5563000000000000000000000000000000 : ℝ)*base69 + (661706539326783353/5563000000000000000000000000000000 : ℝ)*base71 + (74028905945697/27815000000000000000000000000 : ℝ)*base73 + (32901028963869216647/5563000000000000000000000000000000 : ℝ)*base76 + (36209568975110783353/5563000000000000000000000000000000 : ℝ)*base77 + (11250534230086216647/5563000000000000000000000000000000 : ℝ)*base80 + (8866128823509/3476875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1319607/500000000000000000000 : ℝ)*base89 + (1319607/500000000000000000000 : ℝ)*base91 + (1319607/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20261154822847233730880019/2781500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582427501/50000000000000 : ℝ)*(base19) + (61682713/5000000000000 : ℝ)*(base23) + (285317491/100000000000000 : ℝ)*(lower1) + (39516713/100000000000000 : ℝ)*(upper3) + (40332721/50000000000000 : ℝ)*(lower4) + (165716223/100000000000000 : ℝ)*(upper5) + (5378788462287/200000000000 : ℝ)*(major0) + (5378788462287/200000000000 : ℝ)*(major1) + (5378788462287/200000000000 : ℝ)*(major2) + (6909132071/100000000000000 : ℝ)*(sp1) + (1943752153960757/50000000000000 : ℝ)*(sp4) + (1943748116967221/50000000000000 : ℝ)*(sp5) + (1943751537133627/50000000000000 : ℝ)*(sp6) + (1491283911556981/100000000000000 : ℝ)*(sp7) + (1491283911556981/100000000000000 : ℝ)*(f.failure) + (1943752153960757/50000000000000 : ℝ)*(f.sum) + (5400012965267/2781500000000000000000000000 : ℝ)*base65 + (89451215540619327/11126000000000000000000000000000 : ℝ)*base67 + (10342109363229327/11126000000000000000000000000000 : ℝ)*base69 + (41054010961099327/11126000000000000000000000000000 : ℝ)*base71 + (30512660295277/5563000000000000000000000000 : ℝ)*base73 + (34651541958166673/11126000000000000000000000000000 : ℝ)*base76 + (75709633194975327/11126000000000000000000000000000 : ℝ)*base77 + (94927300474731327/11126000000000000000000000000000 : ℝ)*base79 + (627391033221/222520000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5372817/500000000000000000000 : ℝ)*base90 + (5372817/500000000000000000000 : ℝ)*base92 + (5372817/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1656_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (508/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1656_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1656_box_0 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-669580999/5000000000 : ℝ)*x 0 + (2703296417/5000000000 : ℝ)*x 1 + (1351648291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669580999/5000000000 : ℝ)^4943 ≤ (7919218783039/100000000000000 : ℝ)^3919 := by
    have hnat : (669580999 : ℕ)^4943*100000000000000^3919 ≤ 7919218783039^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669580999 5000000000 7919218783039 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703296417/5000000000 : ℝ)^4943 ≤ (46040388827687/100000000000000 : ℝ)^3919 := by
    have hnat : (2703296417 : ℕ)^4943*100000000000000^3919 ≤ 46040388827687^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703296417 5000000000 46040388827687 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351648291/2500000000 : ℝ)^4943 ≤ (23020196186051/50000000000000 : ℝ)^3919 := by
    have hnat : (1351648291 : ℕ)^4943*50000000000000^3919 ≤ 23020196186051^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351648291 2500000000 23020196186051 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-669580999/5000000000 : ℝ), (2703296417/5000000000 : ℝ), (1351648291/2500000000 : ℝ)] ![(7919218783039/100000000000000 : ℝ), (46040388827687/100000000000000 : ℝ), (23020196186051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-669580999/5000000000 : ℝ)|^4943 ≤ (7919218783039/100000000000000 : ℝ)^3919
        have hw : |(-669580999/5000000000 : ℝ)|=(669580999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703296417/5000000000 : ℝ)|^4943 ≤ (46040388827687/100000000000000 : ℝ)^3919
        have hw : |(2703296417/5000000000 : ℝ)|=(2703296417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351648291/2500000000 : ℝ)|^4943 ≤ (23020196186051/50000000000000 : ℝ)^3919
        have hw : |(1351648291/2500000000 : ℝ)|=(1351648291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_1 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250985793/10000000000 : ℝ)*x 0 + (-1557897643/10000000000 : ℝ)*x 1 + (168956027/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250985793/10000000000 : ℝ)^4943 ≤ (44375397125877/100000000000000 : ℝ)^3919 := by
    have hnat : (5250985793 : ℕ)^4943*100000000000000^3919 ≤ 44375397125877^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250985793 10000000000 44375397125877 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557897643/10000000000 : ℝ)^4943 ≤ (9584213721349/100000000000000 : ℝ)^3919 := by
    have hnat : (1557897643 : ℕ)^4943*100000000000000^3919 ≤ 9584213721349^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557897643 10000000000 9584213721349 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168956027/312500000 : ℝ)^4943 ≤ (23020194574953/50000000000000 : ℝ)^3919 := by
    have hnat : (168956027 : ℕ)^4943*50000000000000^3919 ≤ 23020194574953^3919*312500000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168956027 312500000 23020194574953 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250985793/10000000000 : ℝ), (-1557897643/10000000000 : ℝ), (168956027/312500000 : ℝ)] ![(44375397125877/100000000000000 : ℝ), (9584213721349/100000000000000 : ℝ), (23020194574953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250985793/10000000000 : ℝ)|^4943 ≤ (44375397125877/100000000000000 : ℝ)^3919
        have hw : |(5250985793/10000000000 : ℝ)|=(5250985793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1557897643/10000000000 : ℝ)|^4943 ≤ (9584213721349/100000000000000 : ℝ)^3919
        have hw : |(-1557897643/10000000000 : ℝ)|=(1557897643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168956027/312500000 : ℝ)|^4943 ≤ (23020194574953/50000000000000 : ℝ)^3919
        have hw : |(168956027/312500000 : ℝ)|=(168956027/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_2 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250985849/10000000000 : ℝ)*x 0 + (540659329/1000000000 : ℝ)*x 1 + (-62315879/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250985849/10000000000 : ℝ)^4943 ≤ (22187698861391/50000000000000 : ℝ)^3919 := by
    have hnat : (5250985849 : ℕ)^4943*50000000000000^3919 ≤ 22187698861391^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250985849 10000000000 22187698861391 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540659329/1000000000 : ℝ)^4943 ≤ (2877524607839/6250000000000 : ℝ)^3919 := by
    have hnat : (540659329 : ℕ)^4943*6250000000000^3919 ≤ 2877524607839^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540659329 1000000000 2877524607839 6250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62315879/400000000 : ℝ)^4943 ≤ (9584208538013/100000000000000 : ℝ)^3919 := by
    have hnat : (62315879 : ℕ)^4943*100000000000000^3919 ≤ 9584208538013^3919*400000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62315879 400000000 9584208538013 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250985849/10000000000 : ℝ), (540659329/1000000000 : ℝ), (-62315879/400000000 : ℝ)] ![(22187698861391/50000000000000 : ℝ), (2877524607839/6250000000000 : ℝ), (9584208538013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250985849/10000000000 : ℝ)|^4943 ≤ (22187698861391/50000000000000 : ℝ)^3919
        have hw : |(5250985849/10000000000 : ℝ)|=(5250985849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540659329/1000000000 : ℝ)|^4943 ≤ (2877524607839/6250000000000 : ℝ)^3919
        have hw : |(540659329/1000000000 : ℝ)|=(540659329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62315879/400000000 : ℝ)|^4943 ≤ (9584208538013/100000000000000 : ℝ)^3919
        have hw : |(-62315879/400000000 : ℝ)|=(62315879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_3 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4452579773/10000000000 : ℝ)*x 0 + (809977967/2000000000 : ℝ)*x 1 + (2024944509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452579773/10000000000 : ℝ)^4943 ≤ (36041018877629/100000000000000 : ℝ)^3919 := by
    have hnat : (4452579773 : ℕ)^4943*100000000000000^3919 ≤ 36041018877629^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452579773 10000000000 36041018877629 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809977967/2000000000 : ℝ)^4943 ≤ (15989747310757/50000000000000 : ℝ)^3919 := by
    have hnat : (809977967 : ℕ)^4943*50000000000000^3919 ≤ 15989747310757^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809977967 2000000000 15989747310757 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024944509/5000000000 : ℝ)^4943 ≤ (15989743242243/50000000000000 : ℝ)^3919 := by
    have hnat : (2024944509 : ℕ)^4943*50000000000000^3919 ≤ 15989743242243^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024944509 5000000000 15989743242243 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452579773/10000000000 : ℝ), (809977967/2000000000 : ℝ), (2024944509/5000000000 : ℝ)] ![(36041018877629/100000000000000 : ℝ), (15989747310757/50000000000000 : ℝ), (15989743242243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452579773/10000000000 : ℝ)|^4943 ≤ (36041018877629/100000000000000 : ℝ)^3919
        have hw : |(4452579773/10000000000 : ℝ)|=(4452579773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(809977967/2000000000 : ℝ)|^4943 ≤ (15989747310757/50000000000000 : ℝ)^3919
        have hw : |(809977967/2000000000 : ℝ)|=(809977967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2024944509/5000000000 : ℝ)|^4943 ≤ (15989743242243/50000000000000 : ℝ)^3919
        have hw : |(2024944509/5000000000 : ℝ)|=(2024944509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_4 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372287951/2000000000 : ℝ)*x 0 + (5215884131/10000000000 : ℝ)*x 1 + (2607942323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372287951/2000000000 : ℝ)^4943 ≤ (1499605424469/12500000000000 : ℝ)^3919 := by
    have hnat : (372287951 : ℕ)^4943*12500000000000^3919 ≤ 1499605424469^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372287951 2000000000 1499605424469 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215884131/10000000000 : ℝ)^4943 ≤ (55001969443/125000000000 : ℝ)^3919 := by
    have hnat : (5215884131 : ℕ)^4943*125000000000^3919 ≤ 55001969443^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215884131 10000000000 55001969443 125000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607942323/5000000000 : ℝ)^4943 ≤ (44001581034177/100000000000000 : ℝ)^3919 := by
    have hnat : (2607942323 : ℕ)^4943*100000000000000^3919 ≤ 44001581034177^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607942323 5000000000 44001581034177 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372287951/2000000000 : ℝ), (5215884131/10000000000 : ℝ), (2607942323/5000000000 : ℝ)] ![(1499605424469/12500000000000 : ℝ), (55001969443/125000000000 : ℝ), (44001581034177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372287951/2000000000 : ℝ)|^4943 ≤ (1499605424469/12500000000000 : ℝ)^3919
        have hw : |(-372287951/2000000000 : ℝ)|=(372287951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215884131/10000000000 : ℝ)|^4943 ≤ (55001969443/125000000000 : ℝ)^3919
        have hw : |(5215884131/10000000000 : ℝ)|=(5215884131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607942323/5000000000 : ℝ)|^4943 ≤ (44001581034177/100000000000000 : ℝ)^3919
        have hw : |(2607942323/5000000000 : ℝ)|=(2607942323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_5 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345444917/2500000000 : ℝ)*x 0 + (-409960903/2500000000 : ℝ)*x 1 + (2607942003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345444917/2500000000 : ℝ)^4943 ≤ (45774039211561/100000000000000 : ℝ)^3919 := by
    have hnat : (1345444917 : ℕ)^4943*100000000000000^3919 ≤ 45774039211561^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345444917 2500000000 45774039211561 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409960903/2500000000 : ℝ)^4943 ≤ (5112193274899/50000000000000 : ℝ)^3919 := by
    have hnat : (409960903 : ℕ)^4943*50000000000000^3919 ≤ 5112193274899^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409960903 2500000000 5112193274899 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607942003/5000000000 : ℝ)^4943 ≤ (44001574224357/100000000000000 : ℝ)^3919 := by
    have hnat : (2607942003 : ℕ)^4943*100000000000000^3919 ≤ 44001574224357^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607942003 5000000000 44001574224357 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345444917/2500000000 : ℝ), (-409960903/2500000000 : ℝ), (2607942003/5000000000 : ℝ)] ![(45774039211561/100000000000000 : ℝ), (5112193274899/50000000000000 : ℝ), (44001574224357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345444917/2500000000 : ℝ)|^4943 ≤ (45774039211561/100000000000000 : ℝ)^3919
        have hw : |(1345444917/2500000000 : ℝ)|=(1345444917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409960903/2500000000 : ℝ)|^4943 ≤ (5112193274899/50000000000000 : ℝ)^3919
        have hw : |(-409960903/2500000000 : ℝ)|=(409960903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607942003/5000000000 : ℝ)|^4943 ≤ (44001574224357/100000000000000 : ℝ)^3919
        have hw : |(2607942003/5000000000 : ℝ)|=(2607942003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_6 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538177913/1000000000 : ℝ)*x 0 + (5215884727/10000000000 : ℝ)*x 1 + (-1639843371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538177913/1000000000 : ℝ)^4943 ≤ (45774033440031/100000000000000 : ℝ)^3919 := by
    have hnat : (538177913 : ℕ)^4943*100000000000000^3919 ≤ 45774033440031^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538177913 1000000000 45774033440031 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215884727/10000000000 : ℝ)^4943 ≤ (11000395474011/25000000000000 : ℝ)^3919 := by
    have hnat : (5215884727 : ℕ)^4943*25000000000000^3919 ≤ 11000395474011^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215884727 10000000000 11000395474011 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639843371/10000000000 : ℝ)^4943 ≤ (639024040909/6250000000000 : ℝ)^3919 := by
    have hnat : (1639843371 : ℕ)^4943*6250000000000^3919 ≤ 639024040909^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639843371 10000000000 639024040909 6250000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538177913/1000000000 : ℝ), (5215884727/10000000000 : ℝ), (-1639843371/10000000000 : ℝ)] ![(45774033440031/100000000000000 : ℝ), (11000395474011/25000000000000 : ℝ), (639024040909/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538177913/1000000000 : ℝ)|^4943 ≤ (45774033440031/100000000000000 : ℝ)^3919
        have hw : |(538177913/1000000000 : ℝ)|=(538177913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215884727/10000000000 : ℝ)|^4943 ≤ (11000395474011/25000000000000 : ℝ)^3919
        have hw : |(5215884727/10000000000 : ℝ)|=(5215884727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1639843371/10000000000 : ℝ)|^4943 ≤ (639024040909/6250000000000 : ℝ)^3919
        have hw : |(-1639843371/10000000000 : ℝ)|=(1639843371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_7 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3893155287/10000000000 : ℝ)*x 0 + (2164639533/5000000000 : ℝ)*x 1 + (2164639649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3893155287/10000000000 : ℝ)^4943 ≤ (15213221902397/50000000000000 : ℝ)^3919 := by
    have hnat : (3893155287 : ℕ)^4943*50000000000000^3919 ≤ 15213221902397^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893155287 10000000000 15213221902397 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164639533/5000000000 : ℝ)^4943 ≤ (34786776915713/100000000000000 : ℝ)^3919 := by
    have hnat : (2164639533 : ℕ)^4943*100000000000000^3919 ≤ 34786776915713^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164639533 5000000000 34786776915713 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164639649/5000000000 : ℝ)^4943 ≤ (1739338963349/5000000000000 : ℝ)^3919 := by
    have hnat : (2164639649 : ℕ)^4943*5000000000000^3919 ≤ 1739338963349^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164639649 5000000000 1739338963349 5000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3893155287/10000000000 : ℝ), (2164639533/5000000000 : ℝ), (2164639649/5000000000 : ℝ)] ![(15213221902397/50000000000000 : ℝ), (34786776915713/100000000000000 : ℝ), (1739338963349/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3893155287/10000000000 : ℝ)|^4943 ≤ (15213221902397/50000000000000 : ℝ)^3919
        have hw : |(3893155287/10000000000 : ℝ)|=(3893155287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2164639533/5000000000 : ℝ)|^4943 ≤ (34786776915713/100000000000000 : ℝ)^3919
        have hw : |(2164639533/5000000000 : ℝ)|=(2164639533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2164639649/5000000000 : ℝ)|^4943 ≤ (1739338963349/5000000000000 : ℝ)^3919
        have hw : |(2164639649/5000000000 : ℝ)|=(2164639649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_8 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-874993057/5000000000 : ℝ)*x 0 + (2539294691/5000000000 : ℝ)*x 1 + (1358993651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874993057/5000000000 : ℝ)^4943 ≤ (1387254875057/12500000000000 : ℝ)^3919 := by
    have hnat : (874993057 : ℕ)^4943*12500000000000^3919 ≤ 1387254875057^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874993057 5000000000 1387254875057 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539294691/5000000000 : ℝ)^4943 ≤ (8509153802139/20000000000000 : ℝ)^3919 := by
    have hnat : (2539294691 : ℕ)^4943*20000000000000^3919 ≤ 8509153802139^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539294691 5000000000 8509153802139 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358993651/2500000000 : ℝ)^4943 ≤ (11589047991537/25000000000000 : ℝ)^3919 := by
    have hnat : (1358993651 : ℕ)^4943*25000000000000^3919 ≤ 11589047991537^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358993651 2500000000 11589047991537 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-874993057/5000000000 : ℝ), (2539294691/5000000000 : ℝ), (1358993651/2500000000 : ℝ)] ![(1387254875057/12500000000000 : ℝ), (8509153802139/20000000000000 : ℝ), (11589047991537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-874993057/5000000000 : ℝ)|^4943 ≤ (1387254875057/12500000000000 : ℝ)^3919
        have hw : |(-874993057/5000000000 : ℝ)|=(874993057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539294691/5000000000 : ℝ)|^4943 ≤ (8509153802139/20000000000000 : ℝ)^3919
        have hw : |(2539294691/5000000000 : ℝ)|=(2539294691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358993651/2500000000 : ℝ)|^4943 ≤ (11589047991537/25000000000000 : ℝ)^3919
        have hw : |(1358993651/2500000000 : ℝ)|=(1358993651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_9 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615418499/5000000000 : ℝ)*x 0 + (-772424063/5000000000 : ℝ)*x 1 + (1087194959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615418499/5000000000 : ℝ)^4943 ≤ (44160738739953/100000000000000 : ℝ)^3919 := by
    have hnat : (2615418499 : ℕ)^4943*100000000000000^3919 ≤ 44160738739953^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615418499 5000000000 44160738739953 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772424063/5000000000 : ℝ)^4943 ≤ (9483067224669/100000000000000 : ℝ)^3919 := by
    have hnat : (772424063 : ℕ)^4943*100000000000000^3919 ≤ 9483067224669^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772424063 5000000000 9483067224669 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087194959/2000000000 : ℝ)^4943 ≤ (1158904850513/2500000000000 : ℝ)^3919 := by
    have hnat : (1087194959 : ℕ)^4943*2500000000000^3919 ≤ 1158904850513^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087194959 2000000000 1158904850513 2500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615418499/5000000000 : ℝ), (-772424063/5000000000 : ℝ), (1087194959/2000000000 : ℝ)] ![(44160738739953/100000000000000 : ℝ), (9483067224669/100000000000000 : ℝ), (1158904850513/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615418499/5000000000 : ℝ)|^4943 ≤ (44160738739953/100000000000000 : ℝ)^3919
        have hw : |(2615418499/5000000000 : ℝ)|=(2615418499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-772424063/5000000000 : ℝ)|^4943 ≤ (9483067224669/100000000000000 : ℝ)^3919
        have hw : |(-772424063/5000000000 : ℝ)|=(772424063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087194959/2000000000 : ℝ)|^4943 ≤ (1158904850513/2500000000000 : ℝ)^3919
        have hw : |(1087194959/2000000000 : ℝ)|=(1087194959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_10 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615418487/5000000000 : ℝ)*x 0 + (5435974903/10000000000 : ℝ)*x 1 + (-154484801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615418487/5000000000 : ℝ)^4943 ≤ (22080369242197/50000000000000 : ℝ)^3919 := by
    have hnat : (2615418487 : ℕ)^4943*50000000000000^3919 ≤ 22080369242197^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615418487 5000000000 22080369242197 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435974903/10000000000 : ℝ)^4943 ≤ (23178097591077/50000000000000 : ℝ)^3919 := by
    have hnat : (5435974903 : ℕ)^4943*50000000000000^3919 ≤ 23178097591077^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435974903 10000000000 23178097591077 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154484801/1000000000 : ℝ)^4943 ≤ (1896613265309/20000000000000 : ℝ)^3919 := by
    have hnat : (154484801 : ℕ)^4943*20000000000000^3919 ≤ 1896613265309^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154484801 1000000000 1896613265309 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615418487/5000000000 : ℝ), (5435974903/10000000000 : ℝ), (-154484801/1000000000 : ℝ)] ![(22080369242197/50000000000000 : ℝ), (23178097591077/50000000000000 : ℝ), (1896613265309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615418487/5000000000 : ℝ)|^4943 ≤ (22080369242197/50000000000000 : ℝ)^3919
        have hw : |(2615418487/5000000000 : ℝ)|=(2615418487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435974903/10000000000 : ℝ)|^4943 ≤ (23178097591077/50000000000000 : ℝ)^3919
        have hw : |(5435974903/10000000000 : ℝ)|=(5435974903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-154484801/1000000000 : ℝ)|^4943 ≤ (1896613265309/20000000000000 : ℝ)^3919
        have hw : |(-154484801/1000000000 : ℝ)|=(154484801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_11 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4536393257/10000000000 : ℝ)*x 0 + (801353311/2000000000 : ℝ)*x 1 + (50084579/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4536393257/10000000000 : ℝ)^4943 ≤ (1153087495229/3125000000000 : ℝ)^3919 := by
    have hnat : (4536393257 : ℕ)^4943*3125000000000^3919 ≤ 1153087495229^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536393257 10000000000 1153087495229 3125000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801353311/2000000000 : ℝ)^4943 ≤ (31550601232901/100000000000000 : ℝ)^3919 := by
    have hnat : (801353311 : ℕ)^4943*100000000000000^3919 ≤ 31550601232901^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801353311 2000000000 31550601232901 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50084579/125000000 : ℝ)^4943 ≤ (31550598898923/100000000000000 : ℝ)^3919 := by
    have hnat : (50084579 : ℕ)^4943*100000000000000^3919 ≤ 31550598898923^3919*125000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50084579 125000000 31550598898923 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4536393257/10000000000 : ℝ), (801353311/2000000000 : ℝ), (50084579/125000000 : ℝ)] ![(1153087495229/3125000000000 : ℝ), (31550601232901/100000000000000 : ℝ), (31550598898923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4536393257/10000000000 : ℝ)|^4943 ≤ (1153087495229/3125000000000 : ℝ)^3919
        have hw : |(4536393257/10000000000 : ℝ)|=(4536393257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801353311/2000000000 : ℝ)|^4943 ≤ (31550601232901/100000000000000 : ℝ)^3919
        have hw : |(801353311/2000000000 : ℝ)|=(801353311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50084579/125000000 : ℝ)|^4943 ≤ (31550598898923/100000000000000 : ℝ)^3919
        have hw : |(50084579/125000000 : ℝ)|=(50084579/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_12 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-289755847/2000000000 : ℝ)*x 0 + (5538685483/10000000000 : ℝ)*x 1 + (1299019861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289755847/2000000000 : ℝ)^4943 ≤ (8745396807469/100000000000000 : ℝ)^3919 := by
    have hnat : (289755847 : ℕ)^4943*100000000000000^3919 ≤ 8745396807469^3919*2000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289755847 2000000000 8745396807469 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5538685483/10000000000 : ℝ)^4943 ≤ (9492730331367/20000000000000 : ℝ)^3919 := by
    have hnat : (5538685483 : ℕ)^4943*20000000000000^3919 ≤ 9492730331367^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538685483 10000000000 9492730331367 20000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299019861/2500000000 : ℝ)^4943 ≤ (5473868939791/12500000000000 : ℝ)^3919 := by
    have hnat : (1299019861 : ℕ)^4943*12500000000000^3919 ≤ 5473868939791^3919*2500000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299019861 2500000000 5473868939791 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-289755847/2000000000 : ℝ), (5538685483/10000000000 : ℝ), (1299019861/2500000000 : ℝ)] ![(8745396807469/100000000000000 : ℝ), (9492730331367/20000000000000 : ℝ), (5473868939791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-289755847/2000000000 : ℝ)|^4943 ≤ (8745396807469/100000000000000 : ℝ)^3919
        have hw : |(-289755847/2000000000 : ℝ)|=(289755847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5538685483/10000000000 : ℝ)|^4943 ≤ (9492730331367/20000000000000 : ℝ)^3919
        have hw : |(5538685483/10000000000 : ℝ)|=(5538685483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299019861/2500000000 : ℝ)|^4943 ≤ (5473868939791/12500000000000 : ℝ)^3919
        have hw : |(1299019861/2500000000 : ℝ)|=(1299019861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_13 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395372799/10000000000 : ℝ)*x 0 + (-16480729/100000000 : ℝ)*x 1 + (519607873/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395372799/10000000000 : ℝ)^4943 ≤ (22959955510323/50000000000000 : ℝ)^3919 := by
    have hnat : (5395372799 : ℕ)^4943*50000000000000^3919 ≤ 22959955510323^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395372799 10000000000 22959955510323 50000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16480729/100000000 : ℝ)^4943 ≤ (1286143130207/12500000000000 : ℝ)^3919 := by
    have hnat : (16480729 : ℕ)^4943*12500000000000^3919 ≤ 1286143130207^3919*100000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16480729 100000000 1286143130207 12500000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519607873/1000000000 : ℝ)^4943 ≤ (43790943928671/100000000000000 : ℝ)^3919 := by
    have hnat : (519607873 : ℕ)^4943*100000000000000^3919 ≤ 43790943928671^3919*1000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519607873 1000000000 43790943928671 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395372799/10000000000 : ℝ), (-16480729/100000000 : ℝ), (519607873/1000000000 : ℝ)] ![(22959955510323/50000000000000 : ℝ), (1286143130207/12500000000000 : ℝ), (43790943928671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395372799/10000000000 : ℝ)|^4943 ≤ (22959955510323/50000000000000 : ℝ)^3919
        have hw : |(5395372799/10000000000 : ℝ)|=(5395372799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16480729/100000000 : ℝ)|^4943 ≤ (1286143130207/12500000000000 : ℝ)^3919
        have hw : |(-16480729/100000000 : ℝ)|=(16480729/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519607873/1000000000 : ℝ)|^4943 ≤ (43790943928671/100000000000000 : ℝ)^3919
        have hw : |(519607873/1000000000 : ℝ)|=(519607873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_14 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697686079/5000000000 : ℝ)*x 0 + (5196079207/10000000000 : ℝ)*x 1 + (-1648073129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697686079/5000000000 : ℝ)^4943 ≤ (45919904139623/100000000000000 : ℝ)^3919 := by
    have hnat : (2697686079 : ℕ)^4943*100000000000000^3919 ≤ 45919904139623^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697686079 5000000000 45919904139623 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196079207/10000000000 : ℝ)^4943 ≤ (1368467156221/3125000000000 : ℝ)^3919 := by
    have hnat : (5196079207 : ℕ)^4943*3125000000000^3919 ≤ 1368467156221^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196079207 10000000000 1368467156221 3125000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1648073129/10000000000 : ℝ)^4943 ≤ (10289146844897/100000000000000 : ℝ)^3919 := by
    have hnat : (1648073129 : ℕ)^4943*100000000000000^3919 ≤ 10289146844897^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648073129 10000000000 10289146844897 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697686079/5000000000 : ℝ), (5196079207/10000000000 : ℝ), (-1648073129/10000000000 : ℝ)] ![(45919904139623/100000000000000 : ℝ), (1368467156221/3125000000000 : ℝ), (10289146844897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697686079/5000000000 : ℝ)|^4943 ≤ (45919904139623/100000000000000 : ℝ)^3919
        have hw : |(2697686079/5000000000 : ℝ)|=(2697686079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196079207/10000000000 : ℝ)|^4943 ≤ (1368467156221/3125000000000 : ℝ)^3919
        have hw : |(5196079207/10000000000 : ℝ)|=(5196079207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1648073129/10000000000 : ℝ)|^4943 ≤ (10289146844897/100000000000000 : ℝ)^3919
        have hw : |(-1648073129/10000000000 : ℝ)|=(1648073129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1656_box_15 (p : ℝ) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1916714349/5000000000 : ℝ)*x 0 + (4358241519/10000000000 : ℝ)*x 1 + (174329669/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916714349/5000000000 : ℝ)^4943 ≤ (29838876142421/100000000000000 : ℝ)^3919 := by
    have hnat : (1916714349 : ℕ)^4943*100000000000000^3919 ≤ 29838876142421^3919*5000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916714349 5000000000 29838876142421 100000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4358241519/10000000000 : ℝ)^4943 ≤ (68516720469/195312500000 : ℝ)^3919 := by
    have hnat : (4358241519 : ℕ)^4943*195312500000^3919 ≤ 68516720469^3919*10000000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358241519 10000000000 68516720469 195312500000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174329669/400000000 : ℝ)^4943 ≤ (8770140742883/25000000000000 : ℝ)^3919 := by
    have hnat : (174329669 : ℕ)^4943*25000000000000^3919 ≤ 8770140742883^3919*400000000^4943 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174329669 400000000 8770140742883 25000000000000 4943 3919 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4943/1024 : ℝ)) 4943 3919 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1916714349/5000000000 : ℝ), (4358241519/10000000000 : ℝ), (174329669/400000000 : ℝ)] ![(29838876142421/100000000000000 : ℝ), (68516720469/195312500000 : ℝ), (8770140742883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1916714349/5000000000 : ℝ)|^4943 ≤ (29838876142421/100000000000000 : ℝ)^3919
        have hw : |(1916714349/5000000000 : ℝ)|=(1916714349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4358241519/10000000000 : ℝ)|^4943 ≤ (68516720469/195312500000 : ℝ)^3919
        have hw : |(4358241519/10000000000 : ℝ)|=(4358241519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(174329669/400000000 : ℝ)|^4943 ≤ (8770140742883/25000000000000 : ℝ)^3919
        have hw : |(174329669/400000000 : ℝ)|=(174329669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1656_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (508/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65093/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5869/10000 : ℝ) ∧ (16261/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88281/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (508/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (508/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (508/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (508/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (508/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (508/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10701/100000 : ℝ) ^ (4939/1024 : ℝ) ≤ (2082949047854457/100000000000000000000 : ℝ) := by
    have hpowers : (10701/100000 : ℝ)^4939 ≤ (2082949047854457/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10701 : ℕ)^4939*100000000000000000000^1024 ≤ 2082949047854457^1024*100000^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10701 100000 2082949047854457 100000000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10701/100000 : ℝ)) (X := (2082949047854457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (508/3125 : ℝ) ^ (4939/1024 : ℝ) ≤ (1956311285010621/12500000000000000000 : ℝ) := by
    have hpowers : (508/3125 : ℝ)^4939 ≤ (1956311285010621/12500000000000000000 : ℝ)^1024 := by
      have hnat : (508 : ℕ)^4939*12500000000000000000^1024 ≤ 1956311285010621^1024*3125^4939 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        508 3125 1956311285010621 12500000000000000000 4939 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (508/3125 : ℝ)) (X := (1956311285010621/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002082949047854457/50000000000000000000 : ℝ) ≤ (2500021592474277/2500000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (50002082949047854457/50000000000000000000 : ℝ)^1024 ≤ (2500021592474277/2500000000000000 : ℝ)^4939 := by
      have hnat : (50002082949047854457 : ℕ)^1024*2500000000000000^4939 ≤ 2500021592474277^4939*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002082949047854457 50000000000000000000 2500021592474277 2500000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500021592474277/2500000000000000 : ℝ)) (X := (50002082949047854457/50000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000709337573117577/4000000000000000000 : ℝ) ≤ (2000073528105767/2000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (4000709337573117577/4000000000000000000 : ℝ)^1024 ≤ (2000073528105767/2000000000000000 : ℝ)^4939 := by
      have hnat : (4000709337573117577 : ℕ)^1024*2000000000000000^4939 ≤ 2000073528105767^4939*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000709337573117577 4000000000000000000 2000073528105767 2000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000073528105767/2000000000000000 : ℝ)) (X := (4000709337573117577/4000000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251956311285010621/6250000000000000000 : ℝ) ≤ (5000324455580281/5000000000000000 : ℝ) ^ (4939/1024 : ℝ) := by
    have hpowers : (6251956311285010621/6250000000000000000 : ℝ)^1024 ≤ (5000324455580281/5000000000000000 : ℝ)^4939 := by
      have hnat : (6251956311285010621 : ℕ)^1024*5000000000000000^4939 ≤ 5000324455580281^4939*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251956311285010621 6250000000000000000 5000324455580281 5000000000000000 1024 4939 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000324455580281/5000000000000000 : ℝ)) (X := (6251956311285010621/6250000000000000000 : ℝ)) (by norm_num) 4939 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2082949047854457/100000000000000000000 : ℝ) ≤ ((27772230015359106843/27775000000000000000 : ℝ)+2*(281270631727/555500000000000 : ℝ)*(10701/100000 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (27772230015359106843/27775000000000000000 : ℝ)+2*(281270631727/555500000000000 : ℝ)*(10701/100000 : ℝ)=(2500021592474277/2500000000000000 : ℝ) by norm_num, show 1+2*(2082949047854457/100000000000000000000 : ℝ)=(50002082949047854457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1956311285010621/12500000000000000000 : ℝ)+(2082949047854457/100000000000000000000 : ℝ) ≤ ((27772230015359106843/27775000000000000000 : ℝ)+(281270631727/555500000000000 : ℝ)*((508/3125 : ℝ)+(10701/100000 : ℝ)))^(4939/1024 : ℝ) := by
    rw [show (27772230015359106843/27775000000000000000 : ℝ)+(281270631727/555500000000000 : ℝ)*((508/3125 : ℝ)+(10701/100000 : ℝ))=(2000073528105767/2000000000000000 : ℝ) by norm_num, show 1+(1956311285010621/12500000000000000000 : ℝ)+(2082949047854457/100000000000000000000 : ℝ)=(4000709337573117577/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1956311285010621/12500000000000000000 : ℝ) ≤ ((27772230015359106843/27775000000000000000 : ℝ)+2*(281270631727/555500000000000 : ℝ)*(508/3125 : ℝ))^(4939/1024 : ℝ) := by
    rw [show (27772230015359106843/27775000000000000000 : ℝ)+2*(281270631727/555500000000000 : ℝ)*(508/3125 : ℝ)=(5000324455580281/5000000000000000 : ℝ) by norm_num, show 1+2*(1956311285010621/12500000000000000000 : ℝ)=(6251956311285010621/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27772230015359106843/27775000000000000000 : ℝ)*(X 1 0+X 2 0)+(281270631727/555500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (508/3125 : ℝ)) (c := (27772230015359106843/27775000000000000000 : ℝ)) (alpha := (281270631727/555500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27772230015359106843/27775000000000000000 : ℝ)*(X 0 1+X 2 1)+(281270631727/555500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (508/3125 : ℝ)) (c := (27772230015359106843/27775000000000000000 : ℝ)) (alpha := (281270631727/555500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27772230015359106843/27775000000000000000 : ℝ)*(X 0 2+X 1 2)+(281270631727/555500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4939/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (508/3125 : ℝ)) (c := (27772230015359106843/27775000000000000000 : ℝ)) (alpha := (281270631727/555500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-669580999/5000000000 : ℝ)*X 0 0+(2703296417/5000000000 : ℝ)*X 0 1+(1351648291/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250985793/10000000000 : ℝ)*X 1 0+(-1557897643/10000000000 : ℝ)*X 1 1+(168956027/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250985849/10000000000 : ℝ)*X 2 0+(540659329/1000000000 : ℝ)*X 2 1+(-62315879/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4452579773/10000000000 : ℝ)*X 0 0+(809977967/2000000000 : ℝ)*X 0 1+(2024944509/5000000000 : ℝ)*X 0 2+(4452579773/10000000000 : ℝ)*X 1 0+(809977967/2000000000 : ℝ)*X 1 1+(2024944509/5000000000 : ℝ)*X 1 2+(4452579773/10000000000 : ℝ)*X 2 0+(809977967/2000000000 : ℝ)*X 2 1+(2024944509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372287951/2000000000 : ℝ)*X 0 0+(5215884131/10000000000 : ℝ)*X 0 1+(2607942323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345444917/2500000000 : ℝ)*X 1 0+(-409960903/2500000000 : ℝ)*X 1 1+(2607942003/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538177913/1000000000 : ℝ)*X 2 0+(5215884727/10000000000 : ℝ)*X 2 1+(-1639843371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3893155287/10000000000 : ℝ)*X 0 0+(2164639533/5000000000 : ℝ)*X 0 1+(2164639649/5000000000 : ℝ)*X 0 2+(3893155287/10000000000 : ℝ)*X 1 0+(2164639533/5000000000 : ℝ)*X 1 1+(2164639649/5000000000 : ℝ)*X 1 2+(3893155287/10000000000 : ℝ)*X 2 0+(2164639533/5000000000 : ℝ)*X 2 1+(2164639649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-874993057/5000000000 : ℝ)*X 0 0+(2539294691/5000000000 : ℝ)*X 0 1+(1358993651/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615418499/5000000000 : ℝ)*X 1 0+(-772424063/5000000000 : ℝ)*X 1 1+(1087194959/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615418487/5000000000 : ℝ)*X 2 0+(5435974903/10000000000 : ℝ)*X 2 1+(-154484801/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4536393257/10000000000 : ℝ)*X 0 0+(801353311/2000000000 : ℝ)*X 0 1+(50084579/125000000 : ℝ)*X 0 2+(4536393257/10000000000 : ℝ)*X 1 0+(801353311/2000000000 : ℝ)*X 1 1+(50084579/125000000 : ℝ)*X 1 2+(4536393257/10000000000 : ℝ)*X 2 0+(801353311/2000000000 : ℝ)*X 2 1+(50084579/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-289755847/2000000000 : ℝ)*X 0 0+(5538685483/10000000000 : ℝ)*X 0 1+(1299019861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5395372799/10000000000 : ℝ)*X 1 0+(-16480729/100000000 : ℝ)*X 1 1+(519607873/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697686079/5000000000 : ℝ)*X 2 0+(5196079207/10000000000 : ℝ)*X 2 1+(-1648073129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1916714349/5000000000 : ℝ)*X 0 0+(4358241519/10000000000 : ℝ)*X 0 1+(174329669/400000000 : ℝ)*X 0 2+(1916714349/5000000000 : ℝ)*X 1 0+(4358241519/10000000000 : ℝ)*X 1 1+(174329669/400000000 : ℝ)*X 1 2+(1916714349/5000000000 : ℝ)*X 2 0+(4358241519/10000000000 : ℝ)*X 2 1+(174329669/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1656_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65093/100000 : ℝ) ≤ (-112992950113442635129119482593143/173593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (509799/2000000000000 : ℝ)*(lower0) + (6416707/12500000000000 : ℝ)*(lower3) + (21880271/50000000000000 : ℝ)*(lower4) + (442583999033867/25000000000000 : ℝ)*(major0) + (442583999033867/25000000000000 : ℝ)*(major1) + (442583999033867/25000000000000 : ℝ)*(major2) + (5655030291/100000000000000 : ℝ)*(sp1) + (7906213/50000000000000 : ℝ)*(sp3) + (1290352363655439/50000000000000 : ℝ)*(sp4) + (645175523579109/25000000000000 : ℝ)*(sp5) + (1290346107014059/50000000000000 : ℝ)*(sp6) + (490830521607583/50000000000000 : ℝ)*(sp7) + (3022035849/100000000000000 : ℝ)*(sp12) + (15535318609/100000000000000 : ℝ)*(sp14) + (122707632378449/12500000000000 : ℝ)*(f.failure) + (2580707749346727/100000000000000 : ℝ)*(f.sum) + (16509314091389/27775000000000000000000000000 : ℝ)*base66 + (4602685941093276881/694375000000000000000000000000000 : ℝ)*base67 + (2909121613768901881/694375000000000000000000000000000 : ℝ)*base69 + (1210523790906723119/694375000000000000000000000000000 : ℝ)*base72 + (173841032692461/27775000000000000000000000000 : ℝ)*base73 + (3179373130358901881/694375000000000000000000000000000 : ℝ)*base75 + (1084533797742651881/694375000000000000000000000000000 : ℝ)*base77 + (6446904442465776881/694375000000000000000000000000000 : ℝ)*base79 + (25428318268439/27775000000000000000000000000 : ℝ)*base82 + (593693/62500000000000000000 : ℝ)*base90 + (593693/62500000000000000000 : ℝ)*base92 + (593693/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5869/10000 : ℝ) ≤ (4631232924621651385776295939491/7890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20393581/50000000000000 : ℝ)*(lower2) + (63499041/50000000000000 : ℝ)*(upper4) + (2822213/100000000000000 : ℝ)*(lower5) + (116349234128919/6250000000000 : ℝ)*(major0) + (116349234128919/6250000000000 : ℝ)*(major1) + (116349234128919/6250000000000 : ℝ)*(major2) + (53427000908583/2000000000000 : ℝ)*(sp0) + (1335661384997603/50000000000000 : ℝ)*(sp1) + (133567157304719/5000000000000 : ℝ)*(sp2) + (1032259600833821/100000000000000 : ℝ)*(sp3) + (7404846961/100000000000000 : ℝ)*(sp6) + (105604821/10000000000000 : ℝ)*(sp7) + (50551219/10000000000000 : ℝ)*(sp8) + (13890473067/50000000000000 : ℝ)*(sp9) + (1032260656882031/100000000000000 : ℝ)*(f.failure) + (133567527547067/5000000000000 : ℝ)*(f.sum) + (7857584631547/2525000000000000000000000000 : ℝ)*base66 + (81639636266996497/15781250000000000000000000000000 : ℝ)*base67 + (49918050130347253/15781250000000000000000000000000 : ℝ)*base70 + (65459058811058997/15781250000000000000000000000000 : ℝ)*base71 + (3055588894297/2525000000000000000000000000 : ℝ)*base74 + (66673778966909753/15781250000000000000000000000000 : ℝ)*base76 + (155411820010816003/15781250000000000000000000000000 : ℝ)*base78 + (25936365899722253/15781250000000000000000000000000 : ℝ)*base80 + (3621391638853/2525000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (545667/500000000000000000000 : ℝ)*base90 + (545667/500000000000000000000 : ℝ)*base92 + (545667/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16261/20000 : ℝ) ≤ (1129158405212640665899562594948127/1388750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (941721/25000000000000 : ℝ)*(lower3) + (845807/2500000000000 : ℝ)*(upper4) + (11518417/50000000000000 : ℝ)*(lower5) + (1954491985018737/100000000000000 : ℝ)*(major0) + (1954491985018737/100000000000000 : ℝ)*(major1) + (1954491985018737/100000000000000 : ℝ)*(major2) + (1735639313/50000000000000 : ℝ)*(sp0) + (2867825643/12500000000000 : ℝ)*(sp1) + (43066581253/100000000000000 : ℝ)*(sp2) + (13368528171/100000000000000 : ℝ)*(sp3) + (2798101417779409/100000000000000 : ℝ)*(sp8) + (699520486613223/25000000000000 : ℝ)*(sp9) + (1399030911238391/50000000000000 : ℝ)*(sp10) + (541881600237479/50000000000000 : ℝ)*(sp11) + (1083776569003129/100000000000000 : ℝ)*(f.failure) + (699526222264509/25000000000000 : ℝ)*(f.sum) + (29603497898913/13887500000000000000000000000 : ℝ)*base66 + (3415392826712367291/2777500000000000000000000000000000 : ℝ)*base67 + (5408778076584867291/2777500000000000000000000000000000 : ℝ)*base69 + (12632413343287632709/2777500000000000000000000000000000 : ℝ)*base72 + (43947250546863/13887500000000000000000000000 : ℝ)*base74 + (1862460993455132709/2777500000000000000000000000000000 : ℝ)*base76 + (9689218000894867291/2777500000000000000000000000000000 : ℝ)*base77 + (11061313730377367291/2777500000000000000000000000000000 : ℝ)*base79 + (28494791114013/13887500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3672453/500000000000000000000 : ℝ)*base90 + (3672453/500000000000000000000 : ℝ)*base92 + (3672453/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88281/100000 : ℝ) ≤ (-612987087957483337727304646615383/694375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14146053/12500000000000 : ℝ)*(upper3) + (25098771/20000000000000 : ℝ)*(lower4) + (3187331/10000000000000 : ℝ)*(upper5) + (1998893354259073/100000000000000 : ℝ)*(major0) + (1998893354259073/100000000000000 : ℝ)*(major1) + (1998893354259073/100000000000000 : ℝ)*(major2) + (7482752883/100000000000000 : ℝ)*(sp4) + (10615593211/6250000000000 : ℝ)*(sp5) + (15566473639/12500000000000 : ℝ)*(sp6) + (32366874363/50000000000000 : ℝ)*(sp7) + (2918808175856021/100000000000000 : ℝ)*(sp12) + (364830726139691/12500000000000 : ℝ)*(sp13) + (182418195426237/6250000000000 : ℝ)*(sp14) + (554166319507379/50000000000000 : ℝ)*(sp15) + (277099343190871/25000000000000 : ℝ)*(f.failure) + (364851957326113/12500000000000 : ℝ)*(f.sum) + (62016978886421/27775000000000000000000000000 : ℝ)*base65 + (1220047175422313461/2777500000000000000000000000000000 : ℝ)*base68 + (1912390450837313461/2777500000000000000000000000000000 : ℝ)*base70 + (4205373139397686539/2777500000000000000000000000000000 : ℝ)*base71 + (11955460907579/27775000000000000000000000000 : ℝ)*base74 + (8996806810572313461/2777500000000000000000000000000000 : ℝ)*base76 + (4403542705142313461/2777500000000000000000000000000000 : ℝ)*base78 + (10296679843602313461/2777500000000000000000000000000000 : ℝ)*base80 + (82989472684879/27775000000000000000000000000 : ℝ)*base82 + (235547/125000000000000000000 : ℝ)*base90 + (235547/125000000000000000000 : ℝ)*base92 + (235547/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1656_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (508/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65093/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5869/10000 : ℝ) else (16261/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88281/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1656_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1656_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65093/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5869/10000 : ℝ) else (16261/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88281/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1656_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1656_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1656_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4939/1024 : ℝ) ≤ p) (hpb : p ≤ (4943/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9017043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65093/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5869/10000 : ℝ) else (16261/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88281/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1656_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
