-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1599_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:29.460571+00:00
-- url     : https://prove2.me/submissions/68fca273-4adf-4549-8c38-24c38491dfca

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
theorem support_rectangle_w1599_s0_0 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396632687/2500000000 : ℝ)*x 0 + (2926099209/5000000000 : ℝ)*x 1 + (4884664991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396632687/2500000000 : ℝ)^4715 ≤ (9519796118693/100000000000000 : ℝ)^3691 := by
    have hnat : (396632687 : ℕ)^4715*100000000000000^3691 ≤ 9519796118693^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396632687 2500000000 9519796118693 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2926099209/5000000000 : ℝ)^4715 ≤ (50438945018287/100000000000000 : ℝ)^3691 := by
    have hnat : (2926099209 : ℕ)^4715*100000000000000^3691 ≤ 50438945018287^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2926099209 5000000000 50438945018287 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4884664991/10000000000 : ℝ)^4715 ≤ (20020629420151/50000000000000 : ℝ)^3691 := by
    have hnat : (4884664991 : ℕ)^4715*50000000000000^3691 ≤ 20020629420151^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884664991 10000000000 20020629420151 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396632687/2500000000 : ℝ), (2926099209/5000000000 : ℝ), (4884664991/10000000000 : ℝ)] ![(9519796118693/100000000000000 : ℝ), (50438945018287/100000000000000 : ℝ), (20020629420151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396632687/2500000000 : ℝ)|^4715 ≤ (9519796118693/100000000000000 : ℝ)^3691
        have hw : |(-396632687/2500000000 : ℝ)|=(396632687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2926099209/5000000000 : ℝ)|^4715 ≤ (50438945018287/100000000000000 : ℝ)^3691
        have hw : |(2926099209/5000000000 : ℝ)|=(2926099209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4884664991/10000000000 : ℝ)|^4715 ≤ (20020629420151/50000000000000 : ℝ)^3691
        have hw : |(4884664991/10000000000 : ℝ)|=(4884664991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_1 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2729137029/5000000000 : ℝ)*x 0 + (-2123567981/10000000000 : ℝ)*x 1 + (4884664799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2729137029/5000000000 : ℝ)^4715 ≤ (46143037709923/100000000000000 : ℝ)^3691 := by
    have hnat : (2729137029 : ℕ)^4715*100000000000000^3691 ≤ 46143037709923^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729137029 5000000000 46143037709923 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123567981/10000000000 : ℝ)^4715 ≤ (13815705445047/100000000000000 : ℝ)^3691 := by
    have hnat : (2123567981 : ℕ)^4715*100000000000000^3691 ≤ 13815705445047^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123567981 10000000000 13815705445047 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4884664799/10000000000 : ℝ)^4715 ≤ (20020628414883/50000000000000 : ℝ)^3691 := by
    have hnat : (4884664799 : ℕ)^4715*50000000000000^3691 ≤ 20020628414883^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884664799 10000000000 20020628414883 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2729137029/5000000000 : ℝ), (-2123567981/10000000000 : ℝ), (4884664799/10000000000 : ℝ)] ![(46143037709923/100000000000000 : ℝ), (13815705445047/100000000000000 : ℝ), (20020628414883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2729137029/5000000000 : ℝ)|^4715 ≤ (46143037709923/100000000000000 : ℝ)^3691
        have hw : |(2729137029/5000000000 : ℝ)|=(2729137029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123567981/10000000000 : ℝ)|^4715 ≤ (13815705445047/100000000000000 : ℝ)^3691
        have hw : |(-2123567981/10000000000 : ℝ)|=(2123567981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4884664799/10000000000 : ℝ)|^4715 ≤ (20020628414883/50000000000000 : ℝ)^3691
        have hw : |(4884664799/10000000000 : ℝ)|=(4884664799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_2 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5458273983/10000000000 : ℝ)*x 0 + (305291551/625000000 : ℝ)*x 1 + (-1061784029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5458273983/10000000000 : ℝ)^4715 ≤ (46143036899989/100000000000000 : ℝ)^3691 := by
    have hnat : (5458273983 : ℕ)^4715*100000000000000^3691 ≤ 46143036899989^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458273983 10000000000 46143036899989 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305291551/625000000 : ℝ)^4715 ≤ (20020628503891/50000000000000 : ℝ)^3691 := by
    have hnat : (305291551 : ℕ)^4715*50000000000000^3691 ≤ 20020628503891^3691*625000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305291551 625000000 20020628503891 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061784029/5000000000 : ℝ)^4715 ≤ (13815706084981/100000000000000 : ℝ)^3691 := by
    have hnat : (1061784029 : ℕ)^4715*100000000000000^3691 ≤ 13815706084981^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061784029 5000000000 13815706084981 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5458273983/10000000000 : ℝ), (305291551/625000000 : ℝ), (-1061784029/5000000000 : ℝ)] ![(46143036899989/100000000000000 : ℝ), (20020628503891/50000000000000 : ℝ), (13815706084981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5458273983/10000000000 : ℝ)|^4715 ≤ (46143036899989/100000000000000 : ℝ)^3691
        have hw : |(5458273983/10000000000 : ℝ)|=(5458273983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(305291551/625000000 : ℝ)|^4715 ≤ (20020628503891/50000000000000 : ℝ)^3691
        have hw : |(305291551/625000000 : ℝ)|=(305291551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061784029/5000000000 : ℝ)|^4715 ≤ (13815706084981/100000000000000 : ℝ)^3691
        have hw : |(-1061784029/5000000000 : ℝ)|=(1061784029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_3 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823043351/2000000000 : ℝ)*x 0 + (192040403/625000000 : ℝ)*x 1 + (2707903283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823043351/2000000000 : ℝ)^4715 ≤ (32167186188959/100000000000000 : ℝ)^3691 := by
    have hnat : (823043351 : ℕ)^4715*100000000000000^3691 ≤ 32167186188959^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823043351 2000000000 32167186188959 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192040403/625000000 : ℝ)^4715 ≤ (4429578373617/20000000000000 : ℝ)^3691 := by
    have hnat : (192040403 : ℕ)^4715*20000000000000^3691 ≤ 4429578373617^3691*625000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192040403 625000000 4429578373617 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707903283/5000000000 : ℝ)^4715 ≤ (571061524059/1250000000000 : ℝ)^3691 := by
    have hnat : (2707903283 : ℕ)^4715*1250000000000^3691 ≤ 571061524059^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707903283 5000000000 571061524059 1250000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823043351/2000000000 : ℝ), (192040403/625000000 : ℝ), (2707903283/5000000000 : ℝ)] ![(32167186188959/100000000000000 : ℝ), (4429578373617/20000000000000 : ℝ), (571061524059/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823043351/2000000000 : ℝ)|^4715 ≤ (32167186188959/100000000000000 : ℝ)^3691
        have hw : |(823043351/2000000000 : ℝ)|=(823043351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192040403/625000000 : ℝ)|^4715 ≤ (4429578373617/20000000000000 : ℝ)^3691
        have hw : |(192040403/625000000 : ℝ)|=(192040403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707903283/5000000000 : ℝ)|^4715 ≤ (571061524059/1250000000000 : ℝ)^3691
        have hw : |(2707903283/5000000000 : ℝ)|=(2707903283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_4 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1589477529/10000000000 : ℝ)*x 0 + (4909279427/10000000000 : ℝ)*x 1 + (5826703803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1589477529/10000000000 : ℝ)^4715 ≤ (4771194626841/50000000000000 : ℝ)^3691 := by
    have hnat : (1589477529 : ℕ)^4715*50000000000000^3691 ≤ 4771194626841^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589477529 10000000000 4771194626841 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4909279427/10000000000 : ℝ)^4715 ≤ (40299189863611/100000000000000 : ℝ)^3691 := by
    have hnat : (4909279427 : ℕ)^4715*100000000000000^3691 ≤ 40299189863611^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909279427 10000000000 40299189863611 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5826703803/10000000000 : ℝ)^4715 ≤ (50158420864783/100000000000000 : ℝ)^3691 := by
    have hnat : (5826703803 : ℕ)^4715*100000000000000^3691 ≤ 50158420864783^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5826703803 10000000000 50158420864783 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1589477529/10000000000 : ℝ), (4909279427/10000000000 : ℝ), (5826703803/10000000000 : ℝ)] ![(4771194626841/50000000000000 : ℝ), (40299189863611/100000000000000 : ℝ), (50158420864783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1589477529/10000000000 : ℝ)|^4715 ≤ (4771194626841/50000000000000 : ℝ)^3691
        have hw : |(-1589477529/10000000000 : ℝ)|=(1589477529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4909279427/10000000000 : ℝ)|^4715 ≤ (40299189863611/100000000000000 : ℝ)^3691
        have hw : |(4909279427/10000000000 : ℝ)|=(4909279427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5826703803/10000000000 : ℝ)|^4715 ≤ (50158420864783/100000000000000 : ℝ)^3691
        have hw : |(5826703803/10000000000 : ℝ)|=(5826703803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_5 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597004559/5000000000 : ℝ)*x 0 + (-590764269/5000000000 : ℝ)*x 1 + (1165340803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597004559/5000000000 : ℝ)^4715 ≤ (43308602646897/100000000000000 : ℝ)^3691 := by
    have hnat : (2597004559 : ℕ)^4715*100000000000000^3691 ≤ 43308602646897^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597004559 5000000000 43308602646897 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590764269/5000000000 : ℝ)^4715 ≤ (261318965821/4000000000000 : ℝ)^3691 := by
    have hnat : (590764269 : ℕ)^4715*4000000000000^3691 ≤ 261318965821^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590764269 5000000000 261318965821 4000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1165340803/2000000000 : ℝ)^4715 ≤ (50158423196063/100000000000000 : ℝ)^3691 := by
    have hnat : (1165340803 : ℕ)^4715*100000000000000^3691 ≤ 50158423196063^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165340803 2000000000 50158423196063 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597004559/5000000000 : ℝ), (-590764269/5000000000 : ℝ), (1165340803/2000000000 : ℝ)] ![(43308602646897/100000000000000 : ℝ), (261318965821/4000000000000 : ℝ), (50158423196063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597004559/5000000000 : ℝ)|^4715 ≤ (43308602646897/100000000000000 : ℝ)^3691
        have hw : |(2597004559/5000000000 : ℝ)|=(2597004559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-590764269/5000000000 : ℝ)|^4715 ≤ (261318965821/4000000000000 : ℝ)^3691
        have hw : |(-590764269/5000000000 : ℝ)|=(590764269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1165340803/2000000000 : ℝ)|^4715 ≤ (50158423196063/100000000000000 : ℝ)^3691
        have hw : |(1165340803/2000000000 : ℝ)|=(1165340803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_6 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038801833/2000000000 : ℝ)*x 0 + (2913351909/5000000000 : ℝ)*x 1 + (-1181528773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038801833/2000000000 : ℝ)^4715 ≤ (8661720629503/20000000000000 : ℝ)^3691 := by
    have hnat : (1038801833 : ℕ)^4715*20000000000000^3691 ≤ 8661720629503^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038801833 2000000000 8661720629503 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2913351909/5000000000 : ℝ)^4715 ≤ (12539605257433/25000000000000 : ℝ)^3691 := by
    have hnat : (2913351909 : ℕ)^4715*25000000000000^3691 ≤ 12539605257433^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913351909 5000000000 12539605257433 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181528773/10000000000 : ℝ)^4715 ≤ (1633243951347/25000000000000 : ℝ)^3691 := by
    have hnat : (1181528773 : ℕ)^4715*25000000000000^3691 ≤ 1633243951347^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181528773 10000000000 1633243951347 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038801833/2000000000 : ℝ), (2913351909/5000000000 : ℝ), (-1181528773/10000000000 : ℝ)] ![(8661720629503/20000000000000 : ℝ), (12539605257433/25000000000000 : ℝ), (1633243951347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038801833/2000000000 : ℝ)|^4715 ≤ (8661720629503/20000000000000 : ℝ)^3691
        have hw : |(1038801833/2000000000 : ℝ)|=(1038801833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2913351909/5000000000 : ℝ)|^4715 ≤ (12539605257433/25000000000000 : ℝ)^3691
        have hw : |(2913351909/5000000000 : ℝ)|=(2913351909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1181528773/10000000000 : ℝ)|^4715 ≤ (1633243951347/25000000000000 : ℝ)^3691
        have hw : |(-1181528773/10000000000 : ℝ)|=(1181528773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s0_7 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2061176981/5000000000 : ℝ)*x 0 + (5356195457/10000000000 : ℝ)*x 1 + (3134388447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061176981/5000000000 : ℝ)^4715 ≤ (32238469970277/100000000000000 : ℝ)^3691 := by
    have hnat : (2061176981 : ℕ)^4715*100000000000000^3691 ≤ 32238469970277^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061176981 5000000000 32238469970277 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5356195457/10000000000 : ℝ)^4715 ≤ (45043551060087/100000000000000 : ℝ)^3691 := by
    have hnat : (5356195457 : ℕ)^4715*100000000000000^3691 ≤ 45043551060087^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356195457 10000000000 45043551060087 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134388447/10000000000 : ℝ)^4715 ≤ (22717978953429/100000000000000 : ℝ)^3691 := by
    have hnat : (3134388447 : ℕ)^4715*100000000000000^3691 ≤ 22717978953429^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134388447 10000000000 22717978953429 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2061176981/5000000000 : ℝ), (5356195457/10000000000 : ℝ), (3134388447/10000000000 : ℝ)] ![(32238469970277/100000000000000 : ℝ), (45043551060087/100000000000000 : ℝ), (22717978953429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2061176981/5000000000 : ℝ)|^4715 ≤ (32238469970277/100000000000000 : ℝ)^3691
        have hw : |(2061176981/5000000000 : ℝ)|=(2061176981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5356195457/10000000000 : ℝ)|^4715 ≤ (45043551060087/100000000000000 : ℝ)^3691
        have hw : |(5356195457/10000000000 : ℝ)|=(5356195457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134388447/10000000000 : ℝ)|^4715 ≤ (22717978953429/100000000000000 : ℝ)^3691
        have hw : |(3134388447/10000000000 : ℝ)|=(3134388447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1599_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3779/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12249/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4711/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4711 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4711*1^1024 ≤ 0^1024*1^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4711/1024 : ℝ) ≤ (23070808703103841/1562500000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4711 ≤ (23070808703103841/1562500000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4711*1562500000000000000^1024 ≤ 23070808703103841^1024*5^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 23070808703103841 1562500000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (23070808703103841/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4711 := by
      have hnat : (1 : ℕ)^1024*1^4711 ≤ 1^4711*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1585570808703103841/1562500000000000000 : ℝ) ≤ (10031910599214349/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (1585570808703103841/1562500000000000000 : ℝ)^1024 ≤ (10031910599214349/10000000000000000 : ℝ)^4711 := by
      have hnat : (1585570808703103841 : ℕ)^1024*10000000000000000^4711 ≤ 10031910599214349^4711*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1585570808703103841 1562500000000000000 10031910599214349 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10031910599214349/10000000000000000 : ℝ)) (X := (1585570808703103841/1562500000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (804320808703103841/781250000000000000 : ℝ) ≤ (5031910599214349/5000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (804320808703103841/781250000000000000 : ℝ)^1024 ≤ (5031910599214349/5000000000000000 : ℝ)^4711 := by
      have hnat : (804320808703103841 : ℕ)^1024*5000000000000000^4711 ≤ 5031910599214349^4711*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        804320808703103841 781250000000000000 5031910599214349 5000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5031910599214349/5000000000000000 : ℝ)) (X := (804320808703103841/781250000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(31910599214349/4000000000000000 : ℝ)*(0 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31910599214349/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23070808703103841/1562500000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(31910599214349/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4711/1024 : ℝ) := by
    rw [show (1 : ℝ)+(31910599214349/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10031910599214349/10000000000000000 : ℝ) by norm_num, show 1+(23070808703103841/1562500000000000000 : ℝ)+(0 : ℝ)=(1585570808703103841/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23070808703103841/1562500000000000000 : ℝ) ≤ ((1 : ℝ)+2*(31910599214349/4000000000000000 : ℝ)*(2/5 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31910599214349/4000000000000000 : ℝ)*(2/5 : ℝ)=(5031910599214349/5000000000000000 : ℝ) by norm_num, show 1+2*(23070808703103841/1562500000000000000 : ℝ)=(804320808703103841/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(31910599214349/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31910599214349/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(31910599214349/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31910599214349/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(31910599214349/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31910599214349/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-396632687/2500000000 : ℝ)*X 0 0+(2926099209/5000000000 : ℝ)*X 0 1+(4884664991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2729137029/5000000000 : ℝ)*X 1 0+(-2123567981/10000000000 : ℝ)*X 1 1+(4884664799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5458273983/10000000000 : ℝ)*X 2 0+(305291551/625000000 : ℝ)*X 2 1+(-1061784029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((823043351/2000000000 : ℝ)*X 0 0+(192040403/625000000 : ℝ)*X 0 1+(2707903283/5000000000 : ℝ)*X 0 2+(823043351/2000000000 : ℝ)*X 1 0+(192040403/625000000 : ℝ)*X 1 1+(2707903283/5000000000 : ℝ)*X 1 2+(823043351/2000000000 : ℝ)*X 2 0+(192040403/625000000 : ℝ)*X 2 1+(2707903283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1589477529/10000000000 : ℝ)*X 0 0+(4909279427/10000000000 : ℝ)*X 0 1+(5826703803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597004559/5000000000 : ℝ)*X 1 0+(-590764269/5000000000 : ℝ)*X 1 1+(1165340803/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038801833/2000000000 : ℝ)*X 2 0+(2913351909/5000000000 : ℝ)*X 2 1+(-1181528773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2061176981/5000000000 : ℝ)*X 0 0+(5356195457/10000000000 : ℝ)*X 0 1+(3134388447/10000000000 : ℝ)*X 0 2+(2061176981/5000000000 : ℝ)*X 1 0+(5356195457/10000000000 : ℝ)*X 1 1+(3134388447/10000000000 : ℝ)*X 1 2+(2061176981/5000000000 : ℝ)*X 2 0+(5356195457/10000000000 : ℝ)*X 2 1+(3134388447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18931575766807299019743/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8153003/12500000000000 : ℝ)*(base1) + (1461573241/100000000000000 : ℝ)*(base19) + (1447371431/100000000000000 : ℝ)*(base23) + (202441573/100000000000000 : ℝ)*(upper3) + (174971669/100000000000000 : ℝ)*(upper5) + (36508631128569/5000000000000 : ℝ)*(major0) + (36508631128569/5000000000000 : ℝ)*(major1) + (36508631128569/5000000000000 : ℝ)*(major2) + (1033561216336277/100000000000000 : ℝ)*(sp0) + (258391232038613/25000000000000 : ℝ)*(sp1) + (516782471178131/50000000000000 : ℝ)*(sp2) + (426776212698057/100000000000000 : ℝ)*(sp3) + (65482693/1250000000000 : ℝ)*(sp4) + (232507197/10000000000000 : ℝ)*(sp7) + (426778602994051/100000000000000 : ℝ)*(f.failure) + (1033566389727693/100000000000000 : ℝ)*(f.sum) + (714636446581/10000000000000000000000000000 : ℝ)*base65 + (125054481203419/20000000000000000000000000000 : ℝ)*base68 + (151328784943419/20000000000000000000000000000 : ℝ)*base70 + (19739319183419/20000000000000000000000000000 : ℝ)*base72 + (34221295503419/10000000000000000000000000000 : ℝ)*base74 + (140765551363419/20000000000000000000000000000 : ℝ)*base76 + (28197825783419/20000000000000000000000000000 : ℝ)*base78 + (116188783723419/20000000000000000000000000000 : ℝ)*base80 + (45104327923419/10000000000000000000000000000 : ℝ)*base82 + (41382527/10000000000000000000000 : ℝ)*base90 + (41382527/10000000000000000000000 : ℝ)*base92 + (41382527/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (427551108941742880457259/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (921034861/100000000000000 : ℝ)*(base19) + (469717497/50000000000000 : ℝ)*(base23) + (25467391/20000000000000 : ℝ)*(base32) + (169446451/100000000000000 : ℝ)*(upper3) + (3418757/6250000000000 : ℝ)*(upper5) + (385022825891197/50000000000000 : ℝ)*(major0) + (385022825891197/50000000000000 : ℝ)*(major1) + (385022825891197/50000000000000 : ℝ)*(major2) + (157926553/6250000000000 : ℝ)*(sp1) + (1347306433/50000000000000 : ℝ)*(sp2) + (545003585418663/50000000000000 : ℝ)*(sp4) + (1090003722977617/100000000000000 : ℝ)*(sp5) + (545001768394733/50000000000000 : ℝ)*(sp6) + (90016772574693/20000000000000 : ℝ)*(sp7) + (22504199510521/5000000000000 : ℝ)*(f.failure) + (545003585418663/50000000000000 : ℝ)*(f.sum) + (127206867585753/100000000000000000000000000000 : ℝ)*base65 + (243935813785753/200000000000000000000000000000 : ℝ)*base67 + (2140677971414247/200000000000000000000000000000 : ℝ)*base70 + (1717900708814247/200000000000000000000000000000 : ℝ)*base72 + (805791688085753/100000000000000000000000000000 : ℝ)*base73 + (1919599377214247/200000000000000000000000000000 : ℝ)*base76 + (931543944414247/200000000000000000000000000000 : ℝ)*base78 + (836066514614247/200000000000000000000000000000 : ℝ)*base80 + (125507985714247/100000000000000000000000000000 : ℝ)*base82 + (732717/500000000000000000000 : ℝ)*base90 + (732717/500000000000000000000 : ℝ)*base92 + (732717/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1599_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3779/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12249/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1599_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1599_s1_0 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343021731/2000000000 : ℝ)*x 0 + (1108108701/2000000000 : ℝ)*x 1 + (31957921/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343021731/2000000000 : ℝ)^4715 ≤ (105162269511/1000000000000 : ℝ)^3691 := by
    have hnat : (343021731 : ℕ)^4715*1000000000000^3691 ≤ 105162269511^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343021731 2000000000 105162269511 1000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108108701/2000000000 : ℝ)^4715 ≤ (11758331608977/25000000000000 : ℝ)^3691 := by
    have hnat : (1108108701 : ℕ)^4715*25000000000000^3691 ≤ 11758331608977^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108108701 2000000000 11758331608977 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31957921/62500000 : ℝ)^4715 ≤ (10612611647387/25000000000000 : ℝ)^3691 := by
    have hnat : (31957921 : ℕ)^4715*25000000000000^3691 ≤ 10612611647387^3691*62500000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31957921 62500000 10612611647387 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343021731/2000000000 : ℝ), (1108108701/2000000000 : ℝ), (31957921/62500000 : ℝ)] ![(105162269511/1000000000000 : ℝ), (11758331608977/25000000000000 : ℝ), (10612611647387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343021731/2000000000 : ℝ)|^4715 ≤ (105162269511/1000000000000 : ℝ)^3691
        have hw : |(-343021731/2000000000 : ℝ)|=(343021731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108108701/2000000000 : ℝ)|^4715 ≤ (11758331608977/25000000000000 : ℝ)^3691
        have hw : |(1108108701/2000000000 : ℝ)|=(1108108701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31957921/62500000 : ℝ)|^4715 ≤ (10612611647387/25000000000000 : ℝ)^3691
        have hw : |(31957921/62500000 : ℝ)|=(31957921/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_1 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537529967/1000000000 : ℝ)*x 0 + (-1938998009/10000000000 : ℝ)*x 1 + (1278316803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537529967/1000000000 : ℝ)^4715 ≤ (9049776707221/20000000000000 : ℝ)^3691 := by
    have hnat : (537529967 : ℕ)^4715*20000000000000^3691 ≤ 9049776707221^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537529967 1000000000 9049776707221 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938998009/10000000000 : ℝ)^4715 ≤ (12300671430357/100000000000000 : ℝ)^3691 := by
    have hnat : (1938998009 : ℕ)^4715*100000000000000^3691 ≤ 12300671430357^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938998009 10000000000 12300671430357 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278316803/2500000000 : ℝ)^4715 ≤ (42450445019969/100000000000000 : ℝ)^3691 := by
    have hnat : (1278316803 : ℕ)^4715*100000000000000^3691 ≤ 42450445019969^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278316803 2500000000 42450445019969 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537529967/1000000000 : ℝ), (-1938998009/10000000000 : ℝ), (1278316803/2500000000 : ℝ)] ![(9049776707221/20000000000000 : ℝ), (12300671430357/100000000000000 : ℝ), (42450445019969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537529967/1000000000 : ℝ)|^4715 ≤ (9049776707221/20000000000000 : ℝ)^3691
        have hw : |(537529967/1000000000 : ℝ)|=(537529967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938998009/10000000000 : ℝ)|^4715 ≤ (12300671430357/100000000000000 : ℝ)^3691
        have hw : |(-1938998009/10000000000 : ℝ)|=(1938998009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1278316803/2500000000 : ℝ)|^4715 ≤ (42450445019969/100000000000000 : ℝ)^3691
        have hw : |(1278316803/2500000000 : ℝ)|=(1278316803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_2 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075059861/2000000000 : ℝ)*x 0 + (2556633763/5000000000 : ℝ)*x 1 + (-1938998083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075059861/2000000000 : ℝ)^4715 ≤ (45248879611141/100000000000000 : ℝ)^3691 := by
    have hnat : (1075059861 : ℕ)^4715*100000000000000^3691 ≤ 45248879611141^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075059861 2000000000 45248879611141 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2556633763/5000000000 : ℝ)^4715 ≤ (42450448350021/100000000000000 : ℝ)^3691 := by
    have hnat : (2556633763 : ℕ)^4715*100000000000000^3691 ≤ 42450448350021^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556633763 5000000000 42450448350021 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1938998083/10000000000 : ℝ)^4715 ≤ (12300672030039/100000000000000 : ℝ)^3691 := by
    have hnat : (1938998083 : ℕ)^4715*100000000000000^3691 ≤ 12300672030039^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938998083 10000000000 12300672030039 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075059861/2000000000 : ℝ), (2556633763/5000000000 : ℝ), (-1938998083/10000000000 : ℝ)] ![(45248879611141/100000000000000 : ℝ), (42450448350021/100000000000000 : ℝ), (12300672030039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075059861/2000000000 : ℝ)|^4715 ≤ (45248879611141/100000000000000 : ℝ)^3691
        have hw : |(1075059861/2000000000 : ℝ)|=(1075059861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2556633763/5000000000 : ℝ)|^4715 ≤ (42450448350021/100000000000000 : ℝ)^3691
        have hw : |(2556633763/5000000000 : ℝ)|=(2556633763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1938998083/10000000000 : ℝ)|^4715 ≤ (12300672030039/100000000000000 : ℝ)^3691
        have hw : |(-1938998083/10000000000 : ℝ)|=(1938998083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_3 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209136893/10000000000 : ℝ)*x 0 + (3716578369/10000000000 : ℝ)*x 1 + (190054001/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209136893/10000000000 : ℝ)^4715 ≤ (33107953059289/100000000000000 : ℝ)^3691 := by
    have hnat : (4209136893 : ℕ)^4715*100000000000000^3691 ≤ 33107953059289^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209136893 10000000000 33107953059289 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3716578369/10000000000 : ℝ)^4715 ≤ (28241480867241/100000000000000 : ℝ)^3691 := by
    have hnat : (3716578369 : ℕ)^4715*100000000000000^3691 ≤ 28241480867241^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716578369 10000000000 28241480867241 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190054001/400000000 : ℝ)^4715 ≤ (38650566062811/100000000000000 : ℝ)^3691 := by
    have hnat : (190054001 : ℕ)^4715*100000000000000^3691 ≤ 38650566062811^3691*400000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190054001 400000000 38650566062811 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209136893/10000000000 : ℝ), (3716578369/10000000000 : ℝ), (190054001/400000000 : ℝ)] ![(33107953059289/100000000000000 : ℝ), (28241480867241/100000000000000 : ℝ), (38650566062811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209136893/10000000000 : ℝ)|^4715 ≤ (33107953059289/100000000000000 : ℝ)^3691
        have hw : |(4209136893/10000000000 : ℝ)|=(4209136893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3716578369/10000000000 : ℝ)|^4715 ≤ (28241480867241/100000000000000 : ℝ)^3691
        have hw : |(3716578369/10000000000 : ℝ)|=(3716578369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190054001/400000000 : ℝ)|^4715 ≤ (38650566062811/100000000000000 : ℝ)^3691
        have hw : |(190054001/400000000 : ℝ)|=(190054001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_4 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-857678059/5000000000 : ℝ)*x 0 + (5118017521/10000000000 : ℝ)*x 1 + (1383929503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857678059/5000000000 : ℝ)^4715 ≤ (5259082634327/50000000000000 : ℝ)^3691 := by
    have hnat : (857678059 : ℕ)^4715*50000000000000^3691 ≤ 5259082634327^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857678059 5000000000 5259082634327 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5118017521/10000000000 : ℝ)^4715 ≤ (42500829783213/100000000000000 : ℝ)^3691 := by
    have hnat : (5118017521 : ℕ)^4715*100000000000000^3691 ≤ 42500829783213^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118017521 10000000000 42500829783213 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383929503/2500000000 : ℝ)^4715 ≤ (23490502468027/50000000000000 : ℝ)^3691 := by
    have hnat : (1383929503 : ℕ)^4715*50000000000000^3691 ≤ 23490502468027^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383929503 2500000000 23490502468027 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-857678059/5000000000 : ℝ), (5118017521/10000000000 : ℝ), (1383929503/2500000000 : ℝ)] ![(5259082634327/50000000000000 : ℝ), (42500829783213/100000000000000 : ℝ), (23490502468027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-857678059/5000000000 : ℝ)|^4715 ≤ (5259082634327/50000000000000 : ℝ)^3691
        have hw : |(-857678059/5000000000 : ℝ)|=(857678059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5118017521/10000000000 : ℝ)|^4715 ≤ (42500829783213/100000000000000 : ℝ)^3691
        have hw : |(5118017521/10000000000 : ℝ)|=(5118017521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1383929503/2500000000 : ℝ)|^4715 ≤ (23490502468027/50000000000000 : ℝ)^3691
        have hw : |(1383929503/2500000000 : ℝ)|=(1383929503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_5 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261830889/10000000000 : ℝ)*x 0 + (-47392099/312500000 : ℝ)*x 1 + (5535718289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261830889/10000000000 : ℝ)^4715 ≤ (22016153942117/50000000000000 : ℝ)^3691 := by
    have hnat : (5261830889 : ℕ)^4715*50000000000000^3691 ≤ 22016153942117^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261830889 10000000000 22016153942117 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47392099/312500000 : ℝ)^4715 ≤ (8986684153091/100000000000000 : ℝ)^3691 := by
    have hnat : (47392099 : ℕ)^4715*100000000000000^3691 ≤ 8986684153091^3691*312500000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47392099 312500000 8986684153091 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5535718289/10000000000 : ℝ)^4715 ≤ (23490503969563/50000000000000 : ℝ)^3691 := by
    have hnat : (5535718289 : ℕ)^4715*50000000000000^3691 ≤ 23490503969563^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535718289 10000000000 23490503969563 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261830889/10000000000 : ℝ), (-47392099/312500000 : ℝ), (5535718289/10000000000 : ℝ)] ![(22016153942117/50000000000000 : ℝ), (8986684153091/100000000000000 : ℝ), (23490503969563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261830889/10000000000 : ℝ)|^4715 ≤ (22016153942117/50000000000000 : ℝ)^3691
        have hw : |(5261830889/10000000000 : ℝ)|=(5261830889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47392099/312500000 : ℝ)|^4715 ≤ (8986684153091/100000000000000 : ℝ)^3691
        have hw : |(-47392099/312500000 : ℝ)|=(47392099/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5535718289/10000000000 : ℝ)|^4715 ≤ (23490503969563/50000000000000 : ℝ)^3691
        have hw : |(5535718289/10000000000 : ℝ)|=(5535718289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_6 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261830353/10000000000 : ℝ)*x 0 + (2767859243/5000000000 : ℝ)*x 1 + (-303309529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261830353/10000000000 : ℝ)^4715 ≤ (44032302154467/100000000000000 : ℝ)^3691 := by
    have hnat : (5261830353 : ℕ)^4715*100000000000000^3691 ≤ 44032302154467^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261830353 10000000000 44032302154467 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767859243/5000000000 : ℝ)^4715 ≤ (9396202014977/20000000000000 : ℝ)^3691 := by
    have hnat : (2767859243 : ℕ)^4715*20000000000000^3691 ≤ 9396202014977^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767859243 5000000000 9396202014977 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303309529/2000000000 : ℝ)^4715 ≤ (8986687763859/100000000000000 : ℝ)^3691 := by
    have hnat : (303309529 : ℕ)^4715*100000000000000^3691 ≤ 8986687763859^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303309529 2000000000 8986687763859 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261830353/10000000000 : ℝ), (2767859243/5000000000 : ℝ), (-303309529/2000000000 : ℝ)] ![(44032302154467/100000000000000 : ℝ), (9396202014977/20000000000000 : ℝ), (8986687763859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261830353/10000000000 : ℝ)|^4715 ≤ (44032302154467/100000000000000 : ℝ)^3691
        have hw : |(5261830353/10000000000 : ℝ)|=(5261830353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767859243/5000000000 : ℝ)|^4715 ≤ (9396202014977/20000000000000 : ℝ)^3691
        have hw : |(2767859243/5000000000 : ℝ)|=(2767859243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303309529/2000000000 : ℝ)|^4715 ≤ (8986687763859/100000000000000 : ℝ)^3691
        have hw : |(-303309529/2000000000 : ℝ)|=(303309529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s1_7 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052433857/2500000000 : ℝ)*x 0 + (2369923479/5000000000 : ℝ)*x 1 + (3728263823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052433857/2500000000 : ℝ)^4715 ≤ (8278491805071/25000000000000 : ℝ)^3691 := by
    have hnat : (1052433857 : ℕ)^4715*25000000000000^3691 ≤ 8278491805071^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052433857 2500000000 8278491805071 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2369923479/5000000000 : ℝ)^4715 ≤ (38531072592279/100000000000000 : ℝ)^3691 := by
    have hnat : (2369923479 : ℕ)^4715*100000000000000^3691 ≤ 38531072592279^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369923479 5000000000 38531072592279 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3728263823/10000000000 : ℝ)^4715 ≤ (28354960165737/100000000000000 : ℝ)^3691 := by
    have hnat : (3728263823 : ℕ)^4715*100000000000000^3691 ≤ 28354960165737^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728263823 10000000000 28354960165737 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052433857/2500000000 : ℝ), (2369923479/5000000000 : ℝ), (3728263823/10000000000 : ℝ)] ![(8278491805071/25000000000000 : ℝ), (38531072592279/100000000000000 : ℝ), (28354960165737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052433857/2500000000 : ℝ)|^4715 ≤ (8278491805071/25000000000000 : ℝ)^3691
        have hw : |(1052433857/2500000000 : ℝ)|=(1052433857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2369923479/5000000000 : ℝ)|^4715 ≤ (38531072592279/100000000000000 : ℝ)^3691
        have hw : |(2369923479/5000000000 : ℝ)|=(2369923479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3728263823/10000000000 : ℝ)|^4715 ≤ (28354960165737/100000000000000 : ℝ)^3691
        have hw : |(3728263823/10000000000 : ℝ)|=(3728263823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1599_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12249/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4463/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (719/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12249/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12249/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12249/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12249/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12249/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12249/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3779/100000 : ℝ) ^ (4711/1024 : ℝ) ≤ (2851675698059/10000000000000000000 : ℝ) := by
    have hpowers : (3779/100000 : ℝ)^4711 ≤ (2851675698059/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3779 : ℕ)^4711*10000000000000000000^1024 ≤ 2851675698059^1024*100000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3779 100000 2851675698059 10000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3779/100000 : ℝ)) (X := (2851675698059/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12249/50000 : ℝ) ^ (4711/1024 : ℝ) ≤ (154754386582759853/100000000000000000000 : ℝ) := by
    have hpowers : (12249/50000 : ℝ)^4711 ≤ (154754386582759853/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12249 : ℕ)^4711*100000000000000000000^1024 ≤ 154754386582759853^1024*50000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12249 50000 154754386582759853 100000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12249/50000 : ℝ)) (X := (154754386582759853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000002851675698059/5000000000000000000 : ℝ) ≤ (10000001239700813/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (5000002851675698059/5000000000000000000 : ℝ)^1024 ≤ (10000001239700813/10000000000000000 : ℝ)^4711 := by
      have hnat : (5000002851675698059 : ℕ)^1024*10000000000000000^4711 ≤ 10000001239700813^4711*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000002851675698059 5000000000000000000 10000001239700813 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001239700813/10000000000000000 : ℝ)) (X := (5000002851675698059/5000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100154782903339740443/100000000000000000000 : ℝ) ≤ (5001681190619543/5000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (100154782903339740443/100000000000000000000 : ℝ)^1024 ≤ (5001681190619543/5000000000000000 : ℝ)^4711 := by
      have hnat : (100154782903339740443 : ℕ)^1024*5000000000000000^4711 ≤ 5001681190619543^4711*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100154782903339740443 100000000000000000000 5001681190619543 5000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001681190619543/5000000000000000 : ℝ)) (X := (100154782903339740443/100000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50154754386582759853/50000000000000000000 : ℝ) ≤ (10006723522777359/10000000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (50154754386582759853/50000000000000000000 : ℝ)^1024 ≤ (10006723522777359/10000000000000000 : ℝ)^4711 := by
      have hnat : (50154754386582759853 : ℕ)^1024*10000000000000000^4711 ≤ 10006723522777359^4711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50154754386582759853 50000000000000000000 10006723522777359 10000000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006723522777359/10000000000000000 : ℝ)) (X := (50154754386582759853/50000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2851675698059/10000000000000000000 : ℝ) ≤ ((207164622177614877213/207190000000000000000 : ℝ)+2*(3361141538273/2071900000000000 : ℝ)*(3779/100000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (207164622177614877213/207190000000000000000 : ℝ)+2*(3361141538273/2071900000000000 : ℝ)*(3779/100000 : ℝ)=(10000001239700813/10000000000000000 : ℝ) by norm_num, show 1+2*(2851675698059/10000000000000000000 : ℝ)=(5000002851675698059/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(154754386582759853/100000000000000000000 : ℝ)+(2851675698059/10000000000000000000 : ℝ) ≤ ((207164622177614877213/207190000000000000000 : ℝ)+(3361141538273/2071900000000000 : ℝ)*((12249/50000 : ℝ)+(3779/100000 : ℝ)))^(4711/1024 : ℝ) := by
    rw [show (207164622177614877213/207190000000000000000 : ℝ)+(3361141538273/2071900000000000 : ℝ)*((12249/50000 : ℝ)+(3779/100000 : ℝ))=(5001681190619543/5000000000000000 : ℝ) by norm_num, show 1+(154754386582759853/100000000000000000000 : ℝ)+(2851675698059/10000000000000000000 : ℝ)=(100154782903339740443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(154754386582759853/100000000000000000000 : ℝ) ≤ ((207164622177614877213/207190000000000000000 : ℝ)+2*(3361141538273/2071900000000000 : ℝ)*(12249/50000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (207164622177614877213/207190000000000000000 : ℝ)+2*(3361141538273/2071900000000000 : ℝ)*(12249/50000 : ℝ)=(10006723522777359/10000000000000000 : ℝ) by norm_num, show 1+2*(154754386582759853/100000000000000000000 : ℝ)=(50154754386582759853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (207164622177614877213/207190000000000000000 : ℝ)*(X 1 0+X 2 0)+(3361141538273/2071900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (3779/100000 : ℝ)) (hi := (12249/50000 : ℝ)) (c := (207164622177614877213/207190000000000000000 : ℝ)) (alpha := (3361141538273/2071900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (207164622177614877213/207190000000000000000 : ℝ)*(X 0 1+X 2 1)+(3361141538273/2071900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (3779/100000 : ℝ)) (hi := (12249/50000 : ℝ)) (c := (207164622177614877213/207190000000000000000 : ℝ)) (alpha := (3361141538273/2071900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (207164622177614877213/207190000000000000000 : ℝ)*(X 0 2+X 1 2)+(3361141538273/2071900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (3779/100000 : ℝ)) (hi := (12249/50000 : ℝ)) (c := (207164622177614877213/207190000000000000000 : ℝ)) (alpha := (3361141538273/2071900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-343021731/2000000000 : ℝ)*X 0 0+(1108108701/2000000000 : ℝ)*X 0 1+(31957921/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537529967/1000000000 : ℝ)*X 1 0+(-1938998009/10000000000 : ℝ)*X 1 1+(1278316803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075059861/2000000000 : ℝ)*X 2 0+(2556633763/5000000000 : ℝ)*X 2 1+(-1938998083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4209136893/10000000000 : ℝ)*X 0 0+(3716578369/10000000000 : ℝ)*X 0 1+(190054001/400000000 : ℝ)*X 0 2+(4209136893/10000000000 : ℝ)*X 1 0+(3716578369/10000000000 : ℝ)*X 1 1+(190054001/400000000 : ℝ)*X 1 2+(4209136893/10000000000 : ℝ)*X 2 0+(3716578369/10000000000 : ℝ)*X 2 1+(190054001/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-857678059/5000000000 : ℝ)*X 0 0+(5118017521/10000000000 : ℝ)*X 0 1+(1383929503/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5261830889/10000000000 : ℝ)*X 1 0+(-47392099/312500000 : ℝ)*X 1 1+(5535718289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261830353/10000000000 : ℝ)*X 2 0+(2767859243/5000000000 : ℝ)*X 2 1+(-303309529/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052433857/2500000000 : ℝ)*X 0 0+(2369923479/5000000000 : ℝ)*X 0 1+(3728263823/10000000000 : ℝ)*X 0 2+(1052433857/2500000000 : ℝ)*X 1 0+(2369923479/5000000000 : ℝ)*X 1 1+(3728263823/10000000000 : ℝ)*X 1 2+(1052433857/2500000000 : ℝ)*X 2 0+(2369923479/5000000000 : ℝ)*X 2 1+(3728263823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36676244993041448595228593787/5179750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70810133/100000000000000 : ℝ)*(base1) + (63689231/4000000000000 : ℝ)*(base19) + (716654027/50000000000000 : ℝ)*(base23) + (1950603/1000000000000 : ℝ)*(upper3) + (3930707/3125000000000 : ℝ)*(upper5) + (1653419962877667/100000000000000 : ℝ)*(major0) + (1653419962877667/100000000000000 : ℝ)*(major1) + (1653419962877667/100000000000000 : ℝ)*(major2) + (585105046770707/25000000000000 : ℝ)*(sp0) + (234043064793901/10000000000000 : ℝ)*(sp1) + (2340430806861731/100000000000000 : ℝ)*(sp2) + (966401917765581/100000000000000 : ℝ)*(sp3) + (1212389709/10000000000000 : ℝ)*(sp4) + (1365246641/25000000000000 : ℝ)*(sp7) + (966407449562277/100000000000000 : ℝ)*(f.failure) + (468086448033957/20000000000000 : ℝ)*(f.sum) + (2662285381847/809335937500000000000000000 : ℝ)*base65 + (5599320176665002071/20719000000000000000000000000000000 : ℝ)*base67 + (116951640566928997929/20719000000000000000000000000000000 : ℝ)*base70 + (134395664617179002071/20719000000000000000000000000000000 : ℝ)*base71 + (92896928727/51797500000000000000000000000 : ℝ)*base74 + (81278200802831002071/20719000000000000000000000000000000 : ℝ)*base75 + (25781067203834002071/20719000000000000000000000000000000 : ℝ)*base77 + (210694598695421002071/20719000000000000000000000000000000 : ℝ)*base79 + (190890686272811/103595000000000000000000000000 : ℝ)*base81 + (81731529/10000000000000000000000 : ℝ)*base90 + (81731529/10000000000000000000000 : ℝ)*base92 + (81731529/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7857694300422548314249762833/1294937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122666353/10000000000000 : ℝ)*(base19) + (51800161/5000000000000 : ℝ)*(base23) + (19852059/50000000000000 : ℝ)*(upper2) + (112682851/50000000000000 : ℝ)*(upper3) + (88107301/100000000000000 : ℝ)*(upper5) + (422825820307247/25000000000000 : ℝ)*(major0) + (422825820307247/25000000000000 : ℝ)*(major1) + (422825820307247/25000000000000 : ℝ)*(major2) + (4598956431/50000000000000 : ℝ)*(sp1) + (8166341361/100000000000000 : ℝ)*(sp2) + (74814265297853/3125000000000 : ℝ)*(sp4) + (299255758119363/12500000000000 : ℝ)*(sp5) + (1197023643593357/50000000000000 : ℝ)*(sp6) + (49427493532983/5000000000000 : ℝ)*(sp7) + (49427493532983/5000000000000 : ℝ)*(f.failure) + (74814265297853/3125000000000 : ℝ)*(f.sum) + (133477309924571/25898750000000000000000000000 : ℝ)*base65 + (20726337557123837389/5179750000000000000000000000000000 : ℝ)*base68 + (43333005431544837389/5179750000000000000000000000000000 : ℝ)*base70 + (23911201012478837389/5179750000000000000000000000000000 : ℝ)*base72 + (40491777364513/51797500000000000000000000000 : ℝ)*base74 + (19639878178072837389/5179750000000000000000000000000000 : ℝ)*base76 + (2275379828921087389/5179750000000000000000000000000000 : ℝ)*base78 + (4916011326724662611/5179750000000000000000000000000000 : ℝ)*base79 + (371771615712041/103595000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (359491/500000000000000000000 : ℝ)*base90 + (359491/500000000000000000000 : ℝ)*base92 + (359491/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1599_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12249/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4463/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (719/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1599_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1599_s2_0 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216325397/1250000000 : ℝ)*x 0 + (683953359/1250000000 : ℝ)*x 1 + (1034412449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216325397/1250000000 : ℝ)^4715 ≤ (10637741099417/100000000000000 : ℝ)^3691 := by
    have hnat : (216325397 : ℕ)^4715*100000000000000^3691 ≤ 10637741099417^3691*1250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216325397 1250000000 10637741099417 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683953359/1250000000 : ℝ)^4715 ≤ (5785910662247/12500000000000 : ℝ)^3691 := by
    have hnat : (683953359 : ℕ)^4715*12500000000000^3691 ≤ 5785910662247^3691*1250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683953359 1250000000 5785910662247 12500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034412449/2000000000 : ℝ)^4715 ≤ (21537486789127/50000000000000 : ℝ)^3691 := by
    have hnat : (1034412449 : ℕ)^4715*50000000000000^3691 ≤ 21537486789127^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034412449 2000000000 21537486789127 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216325397/1250000000 : ℝ), (683953359/1250000000 : ℝ), (1034412449/2000000000 : ℝ)] ![(10637741099417/100000000000000 : ℝ), (5785910662247/12500000000000 : ℝ), (21537486789127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216325397/1250000000 : ℝ)|^4715 ≤ (10637741099417/100000000000000 : ℝ)^3691
        have hw : |(-216325397/1250000000 : ℝ)|=(216325397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683953359/1250000000 : ℝ)|^4715 ≤ (5785910662247/12500000000000 : ℝ)^3691
        have hw : |(683953359/1250000000 : ℝ)|=(683953359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034412449/2000000000 : ℝ)|^4715 ≤ (21537486789127/50000000000000 : ℝ)^3691
        have hw : |(1034412449/2000000000 : ℝ)|=(1034412449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_1 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678715357/5000000000 : ℝ)*x 0 + (-942712847/5000000000 : ℝ)*x 1 + (5172062069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678715357/5000000000 : ℝ)^4715 ≤ (45056821492441/100000000000000 : ℝ)^3691 := by
    have hnat : (2678715357 : ℕ)^4715*100000000000000^3691 ≤ 45056821492441^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678715357 5000000000 45056821492441 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942712847/5000000000 : ℝ)^4715 ≤ (2967051696073/25000000000000 : ℝ)^3691 := by
    have hnat : (942712847 : ℕ)^4715*25000000000000^3691 ≤ 2967051696073^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942712847 5000000000 2967051696073 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172062069/10000000000 : ℝ)^4715 ≤ (21537485852899/50000000000000 : ℝ)^3691 := by
    have hnat : (5172062069 : ℕ)^4715*50000000000000^3691 ≤ 21537485852899^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172062069 10000000000 21537485852899 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678715357/5000000000 : ℝ), (-942712847/5000000000 : ℝ), (5172062069/10000000000 : ℝ)] ![(45056821492441/100000000000000 : ℝ), (2967051696073/25000000000000 : ℝ), (21537485852899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678715357/5000000000 : ℝ)|^4715 ≤ (45056821492441/100000000000000 : ℝ)^3691
        have hw : |(2678715357/5000000000 : ℝ)|=(2678715357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942712847/5000000000 : ℝ)|^4715 ≤ (2967051696073/25000000000000 : ℝ)^3691
        have hw : |(-942712847/5000000000 : ℝ)|=(942712847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172062069/10000000000 : ℝ)|^4715 ≤ (21537485852899/50000000000000 : ℝ)^3691
        have hw : |(5172062069/10000000000 : ℝ)|=(5172062069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_2 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669678803/1250000000 : ℝ)*x 0 + (129301561/250000000 : ℝ)*x 1 + (-188542559/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669678803/1250000000 : ℝ)^4715 ≤ (5632102297107/12500000000000 : ℝ)^3691 := by
    have hnat : (669678803 : ℕ)^4715*12500000000000^3691 ≤ 5632102297107^3691*1250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669678803 1250000000 5632102297107 12500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129301561/250000000 : ℝ)^4715 ≤ (861499513057/2000000000000 : ℝ)^3691 := by
    have hnat : (129301561 : ℕ)^4715*2000000000000^3691 ≤ 861499513057^3691*250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129301561 250000000 861499513057 2000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188542559/1000000000 : ℝ)^4715 ≤ (5934102974011/50000000000000 : ℝ)^3691 := by
    have hnat : (188542559 : ℕ)^4715*50000000000000^3691 ≤ 5934102974011^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188542559 1000000000 5934102974011 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669678803/1250000000 : ℝ), (129301561/250000000 : ℝ), (-188542559/1000000000 : ℝ)] ![(5632102297107/12500000000000 : ℝ), (861499513057/2000000000000 : ℝ), (5934102974011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669678803/1250000000 : ℝ)|^4715 ≤ (5632102297107/12500000000000 : ℝ)^3691
        have hw : |(669678803/1250000000 : ℝ)|=(669678803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129301561/250000000 : ℝ)|^4715 ≤ (861499513057/2000000000000 : ℝ)^3691
        have hw : |(129301561/250000000 : ℝ)|=(129301561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188542559/1000000000 : ℝ)|^4715 ≤ (5934102974011/50000000000000 : ℝ)^3691
        have hw : |(-188542559/1000000000 : ℝ)|=(188542559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_3 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2110267497/5000000000 : ℝ)*x 0 + (1935000123/5000000000 : ℝ)*x 1 + (4595481643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110267497/5000000000 : ℝ)^4715 ≤ (1661126173003/5000000000000 : ℝ)^3691 := by
    have hnat : (2110267497 : ℕ)^4715*5000000000000^3691 ≤ 1661126173003^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110267497 5000000000 1661126173003 5000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935000123/5000000000 : ℝ)^4715 ≤ (14869590277241/50000000000000 : ℝ)^3691 := by
    have hnat : (1935000123 : ℕ)^4715*50000000000000^3691 ≤ 14869590277241^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935000123 5000000000 14869590277241 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4595481643/10000000000 : ℝ)^4715 ≤ (4629786996713/12500000000000 : ℝ)^3691 := by
    have hnat : (4595481643 : ℕ)^4715*12500000000000^3691 ≤ 4629786996713^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595481643 10000000000 4629786996713 12500000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110267497/5000000000 : ℝ), (1935000123/5000000000 : ℝ), (4595481643/10000000000 : ℝ)] ![(1661126173003/5000000000000 : ℝ), (14869590277241/50000000000000 : ℝ), (4629786996713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110267497/5000000000 : ℝ)|^4715 ≤ (1661126173003/5000000000000 : ℝ)^3691
        have hw : |(2110267497/5000000000 : ℝ)|=(2110267497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1935000123/5000000000 : ℝ)|^4715 ≤ (14869590277241/50000000000000 : ℝ)^3691
        have hw : |(1935000123/5000000000 : ℝ)|=(1935000123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4595481643/10000000000 : ℝ)|^4715 ≤ (4629786996713/12500000000000 : ℝ)^3691
        have hw : |(4595481643/10000000000 : ℝ)|=(4595481643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_4 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-432672067/2500000000 : ℝ)*x 0 + (517440487/1000000000 : ℝ)*x 1 + (136731461/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432672067/2500000000 : ℝ)^4715 ≤ (10638409260637/100000000000000 : ℝ)^3691 := by
    have hnat : (432672067 : ℕ)^4715*100000000000000^3691 ≤ 10638409260637^3691*2500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432672067 2500000000 10638409260637 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517440487/1000000000 : ℝ)^4715 ≤ (10774974555867/25000000000000 : ℝ)^3691 := by
    have hnat : (517440487 : ℕ)^4715*25000000000000^3691 ≤ 10774974555867^3691*1000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517440487 1000000000 10774974555867 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136731461/250000000 : ℝ)^4715 ≤ (46261692502349/100000000000000 : ℝ)^3691 := by
    have hnat : (136731461 : ℕ)^4715*100000000000000^3691 ≤ 46261692502349^3691*250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136731461 250000000 46261692502349 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432672067/2500000000 : ℝ), (517440487/1000000000 : ℝ), (136731461/250000000 : ℝ)] ![(10638409260637/100000000000000 : ℝ), (10774974555867/25000000000000 : ℝ), (46261692502349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432672067/2500000000 : ℝ)|^4715 ≤ (10638409260637/100000000000000 : ℝ)^3691
        have hw : |(-432672067/2500000000 : ℝ)|=(432672067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517440487/1000000000 : ℝ)|^4715 ≤ (10774974555867/25000000000000 : ℝ)^3691
        have hw : |(517440487/1000000000 : ℝ)|=(517440487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136731461/250000000 : ℝ)|^4715 ≤ (46261692502349/100000000000000 : ℝ)^3691
        have hw : |(136731461/250000000 : ℝ)|=(136731461/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_5 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278024411/10000000000 : ℝ)*x 0 + (-39705737/250000000 : ℝ)*x 1 + (273462923/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278024411/10000000000 : ℝ)^4715 ≤ (22102744145561/50000000000000 : ℝ)^3691 := by
    have hnat : (5278024411 : ℕ)^4715*50000000000000^3691 ≤ 22102744145561^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278024411 10000000000 22102744145561 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39705737/250000000 : ℝ)^4715 ≤ (9532818972233/100000000000000 : ℝ)^3691 := by
    have hnat : (39705737 : ℕ)^4715*100000000000000^3691 ≤ 9532818972233^3691*250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39705737 250000000 9532818972233 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273462923/500000000 : ℝ)^4715 ≤ (11565423179613/25000000000000 : ℝ)^3691 := by
    have hnat : (273462923 : ℕ)^4715*25000000000000^3691 ≤ 11565423179613^3691*500000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273462923 500000000 11565423179613 25000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278024411/10000000000 : ℝ), (-39705737/250000000 : ℝ), (273462923/500000000 : ℝ)] ![(22102744145561/50000000000000 : ℝ), (9532818972233/100000000000000 : ℝ), (11565423179613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278024411/10000000000 : ℝ)|^4715 ≤ (22102744145561/50000000000000 : ℝ)^3691
        have hw : |(5278024411/10000000000 : ℝ)|=(5278024411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39705737/250000000 : ℝ)|^4715 ≤ (9532818972233/100000000000000 : ℝ)^3691
        have hw : |(-39705737/250000000 : ℝ)|=(39705737/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273462923/500000000 : ℝ)|^4715 ≤ (11565423179613/25000000000000 : ℝ)^3691
        have hw : |(273462923/500000000 : ℝ)|=(273462923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_6 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639012233/5000000000 : ℝ)*x 0 + (683657277/1250000000 : ℝ)*x 1 + (-1588229747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639012233/5000000000 : ℝ)^4715 ≤ (22102744439783/50000000000000 : ℝ)^3691 := by
    have hnat : (2639012233 : ℕ)^4715*50000000000000^3691 ≤ 22102744439783^3691*5000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639012233 5000000000 22102744439783 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683657277/1250000000 : ℝ)^4715 ≤ (9252338016399/20000000000000 : ℝ)^3691 := by
    have hnat : (683657277 : ℕ)^4715*20000000000000^3691 ≤ 9252338016399^3691*1250000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683657277 1250000000 9252338016399 20000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588229747/10000000000 : ℝ)^4715 ≤ (4766410509709/50000000000000 : ℝ)^3691 := by
    have hnat : (1588229747 : ℕ)^4715*50000000000000^3691 ≤ 4766410509709^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588229747 10000000000 4766410509709 50000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639012233/5000000000 : ℝ), (683657277/1250000000 : ℝ), (-1588229747/10000000000 : ℝ)] ![(22102744439783/50000000000000 : ℝ), (9252338016399/20000000000000 : ℝ), (4766410509709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639012233/5000000000 : ℝ)|^4715 ≤ (22102744439783/50000000000000 : ℝ)^3691
        have hw : |(2639012233/5000000000 : ℝ)|=(2639012233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683657277/1250000000 : ℝ)|^4715 ≤ (9252338016399/20000000000000 : ℝ)^3691
        have hw : |(683657277/1250000000 : ℝ)|=(683657277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1588229747/10000000000 : ℝ)|^4715 ≤ (4766410509709/50000000000000 : ℝ)^3691
        have hw : |(-1588229747/10000000000 : ℝ)|=(1588229747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1599_s2_7 (p : ℝ) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4220741699/10000000000 : ℝ)*x 0 + (4589808589/10000000000 : ℝ)*x 1 + (775147267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220741699/10000000000 : ℝ)^4715 ≤ (33224601991967/100000000000000 : ℝ)^3691 := by
    have hnat : (4220741699 : ℕ)^4715*100000000000000^3691 ≤ 33224601991967^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220741699 10000000000 33224601991967 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4589808589/10000000000 : ℝ)^4715 ≤ (36979897683309/100000000000000 : ℝ)^3691 := by
    have hnat : (4589808589 : ℕ)^4715*100000000000000^3691 ≤ 36979897683309^3691*10000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589808589 10000000000 36979897683309 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775147267/2000000000 : ℝ)^4715 ≤ (29795500313713/100000000000000 : ℝ)^3691 := by
    have hnat : (775147267 : ℕ)^4715*100000000000000^3691 ≤ 29795500313713^3691*2000000000^4715 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775147267 2000000000 29795500313713 100000000000000 4715 3691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4715/1024 : ℝ)) 4715 3691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220741699/10000000000 : ℝ), (4589808589/10000000000 : ℝ), (775147267/2000000000 : ℝ)] ![(33224601991967/100000000000000 : ℝ), (36979897683309/100000000000000 : ℝ), (29795500313713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220741699/10000000000 : ℝ)|^4715 ≤ (33224601991967/100000000000000 : ℝ)^3691
        have hw : |(4220741699/10000000000 : ℝ)|=(4220741699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4589808589/10000000000 : ℝ)|^4715 ≤ (36979897683309/100000000000000 : ℝ)^3691
        have hw : |(4589808589/10000000000 : ℝ)|=(4589808589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(775147267/2000000000 : ℝ)|^4715 ≤ (29795500313713/100000000000000 : ℝ)^3691
        have hw : |(775147267/2000000000 : ℝ)|=(775147267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1599_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (719/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4463/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2549/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16543/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (719/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4463/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (719/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4463/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (719/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4463/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (719/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4463/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (719/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4463/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (719/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4463/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4463/50000 : ℝ) ^ (4711/1024 : ℝ) ≤ (1487328192198391/100000000000000000000 : ℝ) := by
    have hpowers : (4463/50000 : ℝ)^4711 ≤ (1487328192198391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4463 : ℕ)^4711*100000000000000000000^1024 ≤ 1487328192198391^1024*50000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4463 50000 1487328192198391 100000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4463/50000 : ℝ)) (X := (1487328192198391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (719/4000 : ℝ) ^ (4711/1024 : ℝ) ≤ (18621309675138741/50000000000000000000 : ℝ) := by
    have hpowers : (719/4000 : ℝ)^4711 ≤ (18621309675138741/50000000000000000000 : ℝ)^1024 := by
      have hnat : (719 : ℕ)^4711*50000000000000000000^1024 ≤ 18621309675138741^1024*4000^4711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        719 4000 18621309675138741 50000000000000000000 4711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (719/4000 : ℝ)) (X := (18621309675138741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001487328192198391/50000000000000000000 : ℝ) ≤ (2500016164363623/2500000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (50001487328192198391/50000000000000000000 : ℝ)^1024 ≤ (2500016164363623/2500000000000000 : ℝ)^4711 := by
      have hnat : (50001487328192198391 : ℕ)^1024*2500000000000000^4711 ≤ 2500016164363623^4711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001487328192198391 50000000000000000000 2500016164363623 2500000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016164363623/2500000000000000 : ℝ)) (X := (50001487328192198391/50000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038729947542475873/100000000000000000000 : ℝ) ≤ (31252630376843/31250000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (100038729947542475873/100000000000000000000 : ℝ)^1024 ≤ (31252630376843/31250000000000 : ℝ)^4711 := by
      have hnat : (100038729947542475873 : ℕ)^1024*31250000000000^4711 ≤ 31252630376843^4711*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038729947542475873 100000000000000000000 31252630376843 31250000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252630376843/31250000000000 : ℝ)) (X := (100038729947542475873/100000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018621309675138741/25000000000000000000 : ℝ) ≤ (2500404695931257/2500000000000000 : ℝ) ^ (4711/1024 : ℝ) := by
    have hpowers : (25018621309675138741/25000000000000000000 : ℝ)^1024 ≤ (2500404695931257/2500000000000000 : ℝ)^4711 := by
      have hnat : (25018621309675138741 : ℕ)^1024*2500000000000000^4711 ≤ 2500404695931257^4711*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018621309675138741 25000000000000000000 2500404695931257 2500000000000000 1024 4711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500404695931257/2500000000000000 : ℝ)) (X := (25018621309675138741/25000000000000000000 : ℝ)) (by norm_num) 4711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1487328192198391/100000000000000000000 : ℝ) ≤ ((22619178238553723443/22622500000000000000 : ℝ)+2*(194265783817/226225000000000 : ℝ)*(4463/50000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (22619178238553723443/22622500000000000000 : ℝ)+2*(194265783817/226225000000000 : ℝ)*(4463/50000 : ℝ)=(2500016164363623/2500000000000000 : ℝ) by norm_num, show 1+2*(1487328192198391/100000000000000000000 : ℝ)=(50001487328192198391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18621309675138741/50000000000000000000 : ℝ)+(1487328192198391/100000000000000000000 : ℝ) ≤ ((22619178238553723443/22622500000000000000 : ℝ)+(194265783817/226225000000000 : ℝ)*((719/4000 : ℝ)+(4463/50000 : ℝ)))^(4711/1024 : ℝ) := by
    rw [show (22619178238553723443/22622500000000000000 : ℝ)+(194265783817/226225000000000 : ℝ)*((719/4000 : ℝ)+(4463/50000 : ℝ))=(31252630376843/31250000000000 : ℝ) by norm_num, show 1+(18621309675138741/50000000000000000000 : ℝ)+(1487328192198391/100000000000000000000 : ℝ)=(100038729947542475873/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18621309675138741/50000000000000000000 : ℝ) ≤ ((22619178238553723443/22622500000000000000 : ℝ)+2*(194265783817/226225000000000 : ℝ)*(719/4000 : ℝ))^(4711/1024 : ℝ) := by
    rw [show (22619178238553723443/22622500000000000000 : ℝ)+2*(194265783817/226225000000000 : ℝ)*(719/4000 : ℝ)=(2500404695931257/2500000000000000 : ℝ) by norm_num, show 1+2*(18621309675138741/50000000000000000000 : ℝ)=(25018621309675138741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22619178238553723443/22622500000000000000 : ℝ)*(X 1 0+X 2 0)+(194265783817/226225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (4463/50000 : ℝ)) (hi := (719/4000 : ℝ)) (c := (22619178238553723443/22622500000000000000 : ℝ)) (alpha := (194265783817/226225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22619178238553723443/22622500000000000000 : ℝ)*(X 0 1+X 2 1)+(194265783817/226225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (4463/50000 : ℝ)) (hi := (719/4000 : ℝ)) (c := (22619178238553723443/22622500000000000000 : ℝ)) (alpha := (194265783817/226225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22619178238553723443/22622500000000000000 : ℝ)*(X 0 2+X 1 2)+(194265783817/226225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4711/1024 : ℝ)) (lo := (4463/50000 : ℝ)) (hi := (719/4000 : ℝ)) (c := (22619178238553723443/22622500000000000000 : ℝ)) (alpha := (194265783817/226225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216325397/1250000000 : ℝ)*X 0 0+(683953359/1250000000 : ℝ)*X 0 1+(1034412449/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678715357/5000000000 : ℝ)*X 1 0+(-942712847/5000000000 : ℝ)*X 1 1+(5172062069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669678803/1250000000 : ℝ)*X 2 0+(129301561/250000000 : ℝ)*X 2 1+(-188542559/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2110267497/5000000000 : ℝ)*X 0 0+(1935000123/5000000000 : ℝ)*X 0 1+(4595481643/10000000000 : ℝ)*X 0 2+(2110267497/5000000000 : ℝ)*X 1 0+(1935000123/5000000000 : ℝ)*X 1 1+(4595481643/10000000000 : ℝ)*X 1 2+(2110267497/5000000000 : ℝ)*X 2 0+(1935000123/5000000000 : ℝ)*X 2 1+(4595481643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432672067/2500000000 : ℝ)*X 0 0+(517440487/1000000000 : ℝ)*X 0 1+(136731461/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278024411/10000000000 : ℝ)*X 1 0+(-39705737/250000000 : ℝ)*X 1 1+(273462923/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639012233/5000000000 : ℝ)*X 2 0+(683657277/1250000000 : ℝ)*X 2 1+(-1588229747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4220741699/10000000000 : ℝ)*X 0 0+(4589808589/10000000000 : ℝ)*X 0 1+(775147267/2000000000 : ℝ)*X 0 2+(4220741699/10000000000 : ℝ)*X 1 0+(4589808589/10000000000 : ℝ)*X 1 1+(775147267/2000000000 : ℝ)*X 1 2+(4220741699/10000000000 : ℝ)*X 2 0+(4589808589/10000000000 : ℝ)*X 2 1+(775147267/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1599_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (511859483054903184996919311/56556250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1413724731/100000000000000 : ℝ)*(base19) + (1184480187/100000000000000 : ℝ)*(base23) + (2600821/10000000000000 : ℝ)*(lower2) + (190717163/100000000000000 : ℝ)*(upper3) + (2490427/1250000000000 : ℝ)*(upper5) + (235830706609341/10000000000000 : ℝ)*(major0) + (235830706609341/10000000000000 : ℝ)*(major1) + (235830706609341/10000000000000 : ℝ)*(major2) + (834548084901979/25000000000000 : ℝ)*(sp0) + (834551374417177/25000000000000 : ℝ)*(sp1) + (834551431728313/25000000000000 : ℝ)*(sp2) + (1378401079043519/100000000000000 : ℝ)*(sp3) + (14571785523/100000000000000 : ℝ)*(sp4) + (5840068207/100000000000000 : ℝ)*(sp7) + (689203459555863/50000000000000 : ℝ)*(f.failure) + (3338206911393439/100000000000000 : ℝ)*(f.sum) + (357669462321/361960000000000000000000000 : ℝ)*base65 + (1992525239924406063/226225000000000000000000000000000 : ℝ)*base67 + (540350317123268937/226225000000000000000000000000000 : ℝ)*base70 + (1220076870902706063/226225000000000000000000000000000 : ℝ)*base71 + (7901800988229/9049000000000000000000000000 : ℝ)*base74 + (683359229569531063/226225000000000000000000000000000 : ℝ)*base75 + (1166307410666106063/226225000000000000000000000000000 : ℝ)*base77 + (2021654170454856063/226225000000000000000000000000000 : ℝ)*base79 + (20391812037971/4524500000000000000000000000 : ℝ)*base82 + (18649251/5000000000000000000000 : ℝ)*base90 + (18649251/5000000000000000000000 : ℝ)*base92 + (18649251/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6760092887868063548536987299/565562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (678183417/50000000000000 : ℝ)*(base19) + (13054799/800000000000 : ℝ)*(base23) + (198662759/100000000000000 : ℝ)*(upper3) + (16326813/12500000000000 : ℝ)*(lower4) + (42792091/20000000000000 : ℝ)*(upper5) + (1197982701047431/50000000000000 : ℝ)*(major0) + (1197982701047431/50000000000000 : ℝ)*(major1) + (1197982701047431/50000000000000 : ℝ)*(major2) + (2844280981/20000000000000 : ℝ)*(sp1) + (13734451251/100000000000000 : ℝ)*(sp2) + (678302513097503/20000000000000 : ℝ)*(sp4) + (52992140433059/1562500000000 : ℝ)*(sp5) + (339149719918639/10000000000000 : ℝ)*(sp6) + (140041784027333/10000000000000 : ℝ)*(sp7) + (140041784027333/10000000000000 : ℝ)*(f.failure) + (678302513097503/20000000000000 : ℝ)*(f.sum) + (61440872099383/22622500000000000000000000000 : ℝ)*base65 + (453826933414824933/1131125000000000000000000000000000 : ℝ)*base67 + (1321352418306425067/1131125000000000000000000000000000 : ℝ)*base70 + (177472332984324933/1131125000000000000000000000000000 : ℝ)*base71 + (1366473516779/11311250000000000000000000000 : ℝ)*base73 + (9099122661862050067/1131125000000000000000000000000000 : ℝ)*base76 + (3930115417870925067/1131125000000000000000000000000000 : ℝ)*base78 + (10620785642443925067/1131125000000000000000000000000000 : ℝ)*base80 + (111292367803083/22622500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3534441/1000000000000000000000 : ℝ)*base90 + (3534441/1000000000000000000000 : ℝ)*base92 + (3534441/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1599_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (719/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4463/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1599_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1599_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1599_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1599_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1599_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4711/1024 : ℝ) ≤ p) (hpb : p ≤ (4715/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171089323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16543/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1599_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
