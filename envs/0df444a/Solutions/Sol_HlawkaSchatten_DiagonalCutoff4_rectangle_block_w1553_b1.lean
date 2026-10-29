-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1553_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:44.617873+00:00
-- url     : https://prove2.me/submissions/2fd6613a-14e7-40e4-8c52-077629e60b22

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
theorem support_rectangle_w1553_s3_0 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-361759731/2000000000 : ℝ)*x 0 + (54299911/100000000 : ℝ)*x 1 + (5217613209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361759731/2000000000 : ℝ)^4603 ≤ (11089694692487/100000000000000 : ℝ)^3579 := by
    have hnat : (361759731 : ℕ)^4603*100000000000000^3579 ≤ 11089694692487^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361759731 2000000000 11089694692487 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54299911/100000000 : ℝ)^4603 ≤ (45595457862413/100000000000000 : ℝ)^3579 := by
    have hnat : (54299911 : ℕ)^4603*100000000000000^3579 ≤ 45595457862413^3579*100000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54299911 100000000 45595457862413 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217613209/10000000000 : ℝ)^4603 ≤ (21657423716243/50000000000000 : ℝ)^3579 := by
    have hnat : (5217613209 : ℕ)^4603*50000000000000^3579 ≤ 21657423716243^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217613209 10000000000 21657423716243 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361759731/2000000000 : ℝ), (54299911/100000000 : ℝ), (5217613209/10000000000 : ℝ)] ![(11089694692487/100000000000000 : ℝ), (45595457862413/100000000000000 : ℝ), (21657423716243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361759731/2000000000 : ℝ)|^4603 ≤ (11089694692487/100000000000000 : ℝ)^3579
        have hw : |(-361759731/2000000000 : ℝ)|=(361759731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54299911/100000000 : ℝ)|^4603 ≤ (45595457862413/100000000000000 : ℝ)^3579
        have hw : |(54299911/100000000 : ℝ)|=(54299911/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217613209/10000000000 : ℝ)|^4603 ≤ (21657423716243/50000000000000 : ℝ)^3579
        have hw : |(5217613209/10000000000 : ℝ)|=(5217613209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_1 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349759851/10000000000 : ℝ)*x 0 + (-479382039/2500000000 : ℝ)*x 1 + (5217613211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349759851/10000000000 : ℝ)^4603 ≤ (44730842240103/100000000000000 : ℝ)^3579 := by
    have hnat : (5349759851 : ℕ)^4603*100000000000000^3579 ≤ 44730842240103^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349759851 10000000000 44730842240103 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479382039/2500000000 : ℝ)^4603 ≤ (11954310297181/100000000000000 : ℝ)^3579 := by
    have hnat : (479382039 : ℕ)^4603*100000000000000^3579 ≤ 11954310297181^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479382039 2500000000 11954310297181 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217613211/10000000000 : ℝ)^4603 ≤ (541435593173/1250000000000 : ℝ)^3579 := by
    have hnat : (5217613211 : ℕ)^4603*1250000000000^3579 ≤ 541435593173^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217613211 10000000000 541435593173 1250000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349759851/10000000000 : ℝ), (-479382039/2500000000 : ℝ), (5217613211/10000000000 : ℝ)] ![(44730842240103/100000000000000 : ℝ), (11954310297181/100000000000000 : ℝ), (541435593173/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349759851/10000000000 : ℝ)|^4603 ≤ (44730842240103/100000000000000 : ℝ)^3579
        have hw : |(5349759851/10000000000 : ℝ)|=(5349759851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479382039/2500000000 : ℝ)|^4603 ≤ (11954310297181/100000000000000 : ℝ)^3579
        have hw : |(-479382039/2500000000 : ℝ)|=(479382039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217613211/10000000000 : ℝ)|^4603 ≤ (541435593173/1250000000000 : ℝ)^3579
        have hw : |(5217613211/10000000000 : ℝ)|=(5217613211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_2 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334359991/625000000 : ℝ)*x 0 + (5217613189/10000000000 : ℝ)*x 1 + (-1917528177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334359991/625000000 : ℝ)^4603 ≤ (4473084229387/10000000000000 : ℝ)^3579 := by
    have hnat : (334359991 : ℕ)^4603*10000000000000^3579 ≤ 4473084229387^3579*625000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334359991 625000000 4473084229387 10000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217613189/10000000000 : ℝ)^4603 ≤ (10828711804737/25000000000000 : ℝ)^3579 := by
    have hnat : (5217613189 : ℕ)^4603*25000000000000^3579 ≤ 10828711804737^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217613189 10000000000 10828711804737 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917528177/10000000000 : ℝ)^4603 ≤ (5977155232779/50000000000000 : ℝ)^3579 := by
    have hnat : (1917528177 : ℕ)^4603*50000000000000^3579 ≤ 5977155232779^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917528177 10000000000 5977155232779 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334359991/625000000 : ℝ), (5217613189/10000000000 : ℝ), (-1917528177/10000000000 : ℝ)] ![(4473084229387/10000000000000 : ℝ), (10828711804737/25000000000000 : ℝ), (5977155232779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334359991/625000000 : ℝ)|^4603 ≤ (4473084229387/10000000000000 : ℝ)^3579
        have hw : |(334359991/625000000 : ℝ)|=(334359991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217613189/10000000000 : ℝ)|^4603 ≤ (10828711804737/25000000000000 : ℝ)^3579
        have hw : |(5217613189/10000000000 : ℝ)|=(5217613189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1917528177/10000000000 : ℝ)|^4603 ≤ (5977155232779/50000000000000 : ℝ)^3579
        have hw : |(-1917528177/10000000000 : ℝ)|=(1917528177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_3 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850172113/2000000000 : ℝ)*x 0 + (400902299/1000000000 : ℝ)*x 1 + (563069193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850172113/2000000000 : ℝ)^4603 ≤ (16639838253507/50000000000000 : ℝ)^3579 := by
    have hnat : (850172113 : ℕ)^4603*50000000000000^3579 ≤ 16639838253507^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850172113 2000000000 16639838253507 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400902299/1000000000 : ℝ)^4603 ≤ (6172946821949/20000000000000 : ℝ)^3579 := by
    have hnat : (400902299 : ℕ)^4603*20000000000000^3579 ≤ 6172946821949^3579*1000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400902299 1000000000 6172946821949 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563069193/1250000000 : ℝ)^4603 ≤ (1120487167817/3125000000000 : ℝ)^3579 := by
    have hnat : (563069193 : ℕ)^4603*3125000000000^3579 ≤ 1120487167817^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563069193 1250000000 1120487167817 3125000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850172113/2000000000 : ℝ), (400902299/1000000000 : ℝ), (563069193/1250000000 : ℝ)] ![(16639838253507/50000000000000 : ℝ), (6172946821949/20000000000000 : ℝ), (1120487167817/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850172113/2000000000 : ℝ)|^4603 ≤ (16639838253507/50000000000000 : ℝ)^3579
        have hw : |(850172113/2000000000 : ℝ)|=(850172113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400902299/1000000000 : ℝ)|^4603 ≤ (6172946821949/20000000000000 : ℝ)^3579
        have hw : |(400902299/1000000000 : ℝ)|=(400902299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563069193/1250000000 : ℝ)|^4603 ≤ (1120487167817/3125000000000 : ℝ)^3579
        have hw : |(563069193/1250000000 : ℝ)|=(563069193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_4 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-226103459/1250000000 : ℝ)*x 0 + (2609367899/5000000000 : ℝ)*x 1 + (2714429999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226103459/1250000000 : ℝ)^4603 ≤ (5544961747857/50000000000000 : ℝ)^3579 := by
    have hnat : (226103459 : ℕ)^4603*50000000000000^3579 ≤ 5544961747857^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226103459 1250000000 5544961747857 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609367899/5000000000 : ℝ)^4603 ≤ (5415854193067/12500000000000 : ℝ)^3579 := by
    have hnat : (2609367899 : ℕ)^4603*12500000000000^3579 ≤ 5415854193067^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609367899 5000000000 5415854193067 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714429999/5000000000 : ℝ)^4603 ≤ (45583242944083/100000000000000 : ℝ)^3579 := by
    have hnat : (2714429999 : ℕ)^4603*100000000000000^3579 ≤ 45583242944083^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714429999 5000000000 45583242944083 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226103459/1250000000 : ℝ), (2609367899/5000000000 : ℝ), (2714429999/5000000000 : ℝ)] ![(5544961747857/50000000000000 : ℝ), (5415854193067/12500000000000 : ℝ), (45583242944083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226103459/1250000000 : ℝ)|^4603 ≤ (5544961747857/50000000000000 : ℝ)^3579
        have hw : |(-226103459/1250000000 : ℝ)|=(226103459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609367899/5000000000 : ℝ)|^4603 ≤ (5415854193067/12500000000000 : ℝ)^3579
        have hw : |(2609367899/5000000000 : ℝ)|=(2609367899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714429999/5000000000 : ℝ)|^4603 ≤ (45583242944083/100000000000000 : ℝ)^3579
        have hw : |(2714429999/5000000000 : ℝ)|=(2714429999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_5 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646844139/5000000000 : ℝ)*x 0 + (-426570307/2500000000 : ℝ)*x 1 + (1357215011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646844139/5000000000 : ℝ)^4603 ≤ (4412877984471/10000000000000 : ℝ)^3579 := by
    have hnat : (2646844139 : ℕ)^4603*10000000000000^3579 ≤ 4412877984471^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646844139 5000000000 4412877984471 10000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426570307/2500000000 : ℝ)^4603 ≤ (2571994176721/25000000000000 : ℝ)^3579 := by
    have hnat : (426570307 : ℕ)^4603*25000000000000^3579 ≤ 2571994176721^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426570307 2500000000 2571994176721 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357215011/2500000000 : ℝ)^4603 ≤ (11395810860207/25000000000000 : ℝ)^3579 := by
    have hnat : (1357215011 : ℕ)^4603*25000000000000^3579 ≤ 11395810860207^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357215011 2500000000 11395810860207 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646844139/5000000000 : ℝ), (-426570307/2500000000 : ℝ), (1357215011/2500000000 : ℝ)] ![(4412877984471/10000000000000 : ℝ), (2571994176721/25000000000000 : ℝ), (11395810860207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646844139/5000000000 : ℝ)|^4603 ≤ (4412877984471/10000000000000 : ℝ)^3579
        have hw : |(2646844139/5000000000 : ℝ)|=(2646844139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426570307/2500000000 : ℝ)|^4603 ≤ (2571994176721/25000000000000 : ℝ)^3579
        have hw : |(-426570307/2500000000 : ℝ)|=(426570307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357215011/2500000000 : ℝ)|^4603 ≤ (11395810860207/25000000000000 : ℝ)^3579
        have hw : |(1357215011/2500000000 : ℝ)|=(1357215011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_6 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20678469/39062500 : ℝ)*x 0 + (5428860109/10000000000 : ℝ)*x 1 + (-1706281433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20678469/39062500 : ℝ)^4603 ≤ (44128777550377/100000000000000 : ℝ)^3579 := by
    have hnat : (20678469 : ℕ)^4603*100000000000000^3579 ≤ 44128777550377^3579*39062500^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20678469 39062500 44128777550377 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428860109/10000000000 : ℝ)^4603 ≤ (45583244142751/100000000000000 : ℝ)^3579 := by
    have hnat : (5428860109 : ℕ)^4603*100000000000000^3579 ≤ 45583244142751^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428860109 10000000000 45583244142751 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1706281433/10000000000 : ℝ)^4603 ≤ (411519131863/4000000000000 : ℝ)^3579 := by
    have hnat : (1706281433 : ℕ)^4603*4000000000000^3579 ≤ 411519131863^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706281433 10000000000 411519131863 4000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20678469/39062500 : ℝ), (5428860109/10000000000 : ℝ), (-1706281433/10000000000 : ℝ)] ![(44128777550377/100000000000000 : ℝ), (45583244142751/100000000000000 : ℝ), (411519131863/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20678469/39062500 : ℝ)|^4603 ≤ (44128777550377/100000000000000 : ℝ)^3579
        have hw : |(20678469/39062500 : ℝ)|=(20678469/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428860109/10000000000 : ℝ)|^4603 ≤ (45583244142751/100000000000000 : ℝ)^3579
        have hw : |(5428860109/10000000000 : ℝ)|=(5428860109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1706281433/10000000000 : ℝ)|^4603 ≤ (411519131863/4000000000000 : ℝ)^3579
        have hw : |(-1706281433/10000000000 : ℝ)|=(1706281433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s3_7 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250928097/10000000000 : ℝ)*x 0 + (140685437/312500000 : ℝ)*x 1 + (2005831111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250928097/10000000000 : ℝ)^4603 ≤ (8320089120177/25000000000000 : ℝ)^3579 := by
    have hnat : (4250928097 : ℕ)^4603*25000000000000^3579 ≤ 8320089120177^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250928097 10000000000 8320089120177 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140685437/312500000 : ℝ)^4603 ≤ (8957193611047/25000000000000 : ℝ)^3579 := by
    have hnat : (140685437 : ℕ)^4603*25000000000000^3579 ≤ 8957193611047^3579*312500000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140685437 312500000 8957193611047 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005831111/5000000000 : ℝ)^4603 ≤ (30890869063171/100000000000000 : ℝ)^3579 := by
    have hnat : (2005831111 : ℕ)^4603*100000000000000^3579 ≤ 30890869063171^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005831111 5000000000 30890869063171 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250928097/10000000000 : ℝ), (140685437/312500000 : ℝ), (2005831111/5000000000 : ℝ)] ![(8320089120177/25000000000000 : ℝ), (8957193611047/25000000000000 : ℝ), (30890869063171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250928097/10000000000 : ℝ)|^4603 ≤ (8320089120177/25000000000000 : ℝ)^3579
        have hw : |(4250928097/10000000000 : ℝ)|=(4250928097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140685437/312500000 : ℝ)|^4603 ≤ (8957193611047/25000000000000 : ℝ)^3579
        have hw : |(140685437/312500000 : ℝ)|=(140685437/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005831111/5000000000 : ℝ)|^4603 ≤ (30890869063171/100000000000000 : ℝ)^3579
        have hw : |(2005831111/5000000000 : ℝ)|=(2005831111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1553_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h) :
    (441/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15527/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (67/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (67/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (67/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (67/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (67/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (67/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (67/625 : ℝ) ^ (4601/1024 : ℝ) ≤ (439041993804431/10000000000000000000 : ℝ) := by
    have hpowers : (67/625 : ℝ)^4601 ≤ (439041993804431/10000000000000000000 : ℝ)^1024 := by
      have hnat : (67 : ℕ)^4601*10000000000000000000^1024 ≤ 439041993804431^1024*625^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67 625 439041993804431 10000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67/625 : ℝ)) (X := (439041993804431/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15859/100000 : ℝ) ^ (4601/1024 : ℝ) ≤ (25509853273357847/100000000000000000000 : ℝ) := by
    have hpowers : (15859/100000 : ℝ)^4601 ≤ (25509853273357847/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15859 : ℕ)^4601*100000000000000000000^1024 ≤ 25509853273357847^1024*100000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15859 100000 25509853273357847 100000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15859/100000 : ℝ)) (X := (25509853273357847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000439041993804431/5000000000000000000 : ℝ) ≤ (10000195419976977/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (5000439041993804431/5000000000000000000 : ℝ)^1024 ≤ (10000195419976977/10000000000000000 : ℝ)^4601 := by
      have hnat : (5000439041993804431 : ℕ)^1024*10000000000000000^4601 ≤ 10000195419976977^4601*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000439041993804431 5000000000000000000 10000195419976977 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000195419976977/10000000000000000 : ℝ)) (X := (5000439041993804431/5000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029900273211402157/100000000000000000000 : ℝ) ≤ (2500166346021163/2500000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (100029900273211402157/100000000000000000000 : ℝ)^1024 ≤ (2500166346021163/2500000000000000 : ℝ)^4601 := by
      have hnat : (100029900273211402157 : ℕ)^1024*2500000000000000^4601 ≤ 2500166346021163^4601*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029900273211402157 100000000000000000000 2500166346021163 2500000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166346021163/2500000000000000 : ℝ)) (X := (100029900273211402157/100000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025509853273357847/50000000000000000000 : ℝ) ≤ (10001135348192327/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (50025509853273357847/50000000000000000000 : ℝ)^1024 ≤ (10001135348192327/10000000000000000 : ℝ)^4601 := by
      have hnat : (50025509853273357847 : ℕ)^1024*10000000000000000^4601 ≤ 10001135348192327^4601*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025509853273357847 50000000000000000000 10001135348192327 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001135348192327/10000000000000000 : ℝ)) (X := (50025509853273357847/50000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(439041993804431/10000000000000000000 : ℝ) ≤ ((51380928232793132803/51390000000000000000 : ℝ)+2*(18798564307/20556000000000 : ℝ)*(67/625 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (51380928232793132803/51390000000000000000 : ℝ)+2*(18798564307/20556000000000 : ℝ)*(67/625 : ℝ)=(10000195419976977/10000000000000000 : ℝ) by norm_num, show 1+2*(439041993804431/10000000000000000000 : ℝ)=(5000439041993804431/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25509853273357847/100000000000000000000 : ℝ)+(439041993804431/10000000000000000000 : ℝ) ≤ ((51380928232793132803/51390000000000000000 : ℝ)+(18798564307/20556000000000 : ℝ)*((15859/100000 : ℝ)+(67/625 : ℝ)))^(4601/1024 : ℝ) := by
    rw [show (51380928232793132803/51390000000000000000 : ℝ)+(18798564307/20556000000000 : ℝ)*((15859/100000 : ℝ)+(67/625 : ℝ))=(2500166346021163/2500000000000000 : ℝ) by norm_num, show 1+(25509853273357847/100000000000000000000 : ℝ)+(439041993804431/10000000000000000000 : ℝ)=(100029900273211402157/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25509853273357847/100000000000000000000 : ℝ) ≤ ((51380928232793132803/51390000000000000000 : ℝ)+2*(18798564307/20556000000000 : ℝ)*(15859/100000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (51380928232793132803/51390000000000000000 : ℝ)+2*(18798564307/20556000000000 : ℝ)*(15859/100000 : ℝ)=(10001135348192327/10000000000000000 : ℝ) by norm_num, show 1+2*(25509853273357847/100000000000000000000 : ℝ)=(50025509853273357847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (51380928232793132803/51390000000000000000 : ℝ)*(X 1 0+X 2 0)+(18798564307/20556000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (67/625 : ℝ)) (hi := (15859/100000 : ℝ)) (c := (51380928232793132803/51390000000000000000 : ℝ)) (alpha := (18798564307/20556000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (51380928232793132803/51390000000000000000 : ℝ)*(X 0 1+X 2 1)+(18798564307/20556000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (67/625 : ℝ)) (hi := (15859/100000 : ℝ)) (c := (51380928232793132803/51390000000000000000 : ℝ)) (alpha := (18798564307/20556000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (51380928232793132803/51390000000000000000 : ℝ)*(X 0 2+X 1 2)+(18798564307/20556000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (67/625 : ℝ)) (hi := (15859/100000 : ℝ)) (c := (51380928232793132803/51390000000000000000 : ℝ)) (alpha := (18798564307/20556000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-361759731/2000000000 : ℝ)*X 0 0+(54299911/100000000 : ℝ)*X 0 1+(5217613209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349759851/10000000000 : ℝ)*X 1 0+(-479382039/2500000000 : ℝ)*X 1 1+(5217613211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334359991/625000000 : ℝ)*X 2 0+(5217613189/10000000000 : ℝ)*X 2 1+(-1917528177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((850172113/2000000000 : ℝ)*X 0 0+(400902299/1000000000 : ℝ)*X 0 1+(563069193/1250000000 : ℝ)*X 0 2+(850172113/2000000000 : ℝ)*X 1 0+(400902299/1000000000 : ℝ)*X 1 1+(563069193/1250000000 : ℝ)*X 1 2+(850172113/2000000000 : ℝ)*X 2 0+(400902299/1000000000 : ℝ)*X 2 1+(563069193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-226103459/1250000000 : ℝ)*X 0 0+(2609367899/5000000000 : ℝ)*X 0 1+(2714429999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646844139/5000000000 : ℝ)*X 1 0+(-426570307/2500000000 : ℝ)*X 1 1+(1357215011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20678469/39062500 : ℝ)*X 2 0+(5428860109/10000000000 : ℝ)*X 2 1+(-1706281433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250928097/10000000000 : ℝ)*X 0 0+(140685437/312500000 : ℝ)*X 0 1+(2005831111/5000000000 : ℝ)*X 0 2+(4250928097/10000000000 : ℝ)*X 1 0+(140685437/312500000 : ℝ)*X 1 1+(2005831111/5000000000 : ℝ)*X 1 2+(4250928097/10000000000 : ℝ)*X 2 0+(140685437/312500000 : ℝ)*X 2 1+(2005831111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1415890199158153658617/114200000000000000000000000 : ℝ) := by norm_num
    linear_combination (2092274127/100000000000000 : ℝ)*(base19) + (482162539/25000000000000 : ℝ)*(base23) + (4494461/5000000000000 : ℝ)*(lower2) + (319511131/100000000000000 : ℝ)*(upper3) + (176610821/100000000000000 : ℝ)*(upper5) + (672672324563957/20000000000000 : ℝ)*(major0) + (672672324563957/20000000000000 : ℝ)*(major1) + (672672324563957/20000000000000 : ℝ)*(major2) + (588577818951017/12500000000000 : ℝ)*(sp0) + (2354326372800297/50000000000000 : ℝ)*(sp1) + (941730581844913/20000000000000 : ℝ)*(sp2) + (403610481094687/20000000000000 : ℝ)*(sp3) + (4035783323/12500000000000 : ℝ)*(sp4) + (15589013473/100000000000000 : ℝ)*(sp7) + (504516998621727/25000000000000 : ℝ)*(f.failure) + (4708654837874721/100000000000000 : ℝ)*(f.sum) + (44376558795817/5139000000000000000000000000 : ℝ)*base66 + (3546200134116481471/1027800000000000000000000000000000 : ℝ)*base67 + (2739382079890081471/1027800000000000000000000000000000 : ℝ)*base69 + (3256080831604318529/1027800000000000000000000000000000 : ℝ)*base72 + (19013745246127/5139000000000000000000000000 : ℝ)*base74 + (1532845481878318529/1027800000000000000000000000000000 : ℝ)*base76 + (18943506467463118529/1027800000000000000000000000000000 : ℝ)*base78 + (18709103149663081471/1027800000000000000000000000000000 : ℝ)*base79 + (2371047588031/1284750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (15916331/2500000000000000000000 : ℝ)*base89 + (15916331/2500000000000000000000 : ℝ)*base91 + (15916331/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (494076146818695424119594953/214125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12665927/2500000000000 : ℝ)*(base19) + (256954291/100000000000000 : ℝ)*(base23) + (1465333/25000000000000 : ℝ)*(upper2) + (7162829/20000000000000 : ℝ)*(upper3) + (23335273/25000000000000 : ℝ)*(upper5) + (1699693554499051/50000000000000 : ℝ)*(major0) + (1699693554499051/50000000000000 : ℝ)*(major1) + (1699693554499051/50000000000000 : ℝ)*(major2) + (1030399209/10000000000000 : ℝ)*(sp1) + (192476587/5000000000000 : ℝ)*(sp2) + (2379545154198353/50000000000000 : ℝ)*(sp4) + (297442468610471/6250000000000 : ℝ)*(sp5) + (190363448076427/4000000000000 : ℝ)*(sp6) + (2039683832685519/100000000000000 : ℝ)*(sp7) + (2039683832685519/100000000000000 : ℝ)*(f.failure) + (2379545154198353/50000000000000 : ℝ)*(f.sum) + (15531265802941/5139000000000000000000000000 : ℝ)*base65 + (336769237115030047/2569500000000000000000000000000000 : ℝ)*base68 + (407433192705969953/2569500000000000000000000000000000 : ℝ)*base69 + (4689219224676530047/2569500000000000000000000000000000 : ℝ)*base72 + (13690389760649/2569500000000000000000000000 : ℝ)*base73 + (18853194458321030047/2569500000000000000000000000000000 : ℝ)*base76 + (6477054307095530047/2569500000000000000000000000000000 : ℝ)*base78 + (4446430227381530047/2569500000000000000000000000000000 : ℝ)*base80 + (26424665924713/5139000000000000000000000000 : ℝ)*base81 + (25881893/10000000000000000000000 : ℝ)*base90 + (25881893/10000000000000000000000 : ℝ)*base92 + (25881893/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1553_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1553_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1553_s4_0 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-904537117/5000000000 : ℝ)*x 0 + (5428163511/10000000000 : ℝ)*x 1 + (521925809/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904537117/5000000000 : ℝ)^4603 ≤ (2772966928749/25000000000000 : ℝ)^3579 := by
    have hnat : (904537117 : ℕ)^4603*25000000000000^3579 ≤ 2772966928749^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904537117 5000000000 2772966928749 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428163511/10000000000 : ℝ)^4603 ≤ (911514437043/2000000000000 : ℝ)^3579 := by
    have hnat : (5428163511 : ℕ)^4603*2000000000000^3579 ≤ 911514437043^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428163511 10000000000 911514437043 2000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521925809/1000000000 : ℝ)^4603 ≤ (10833102603591/25000000000000 : ℝ)^3579 := by
    have hnat : (521925809 : ℕ)^4603*25000000000000^3579 ≤ 10833102603591^3579*1000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521925809 1000000000 10833102603591 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-904537117/5000000000 : ℝ), (5428163511/10000000000 : ℝ), (521925809/1000000000 : ℝ)] ![(2772966928749/25000000000000 : ℝ), (911514437043/2000000000000 : ℝ), (10833102603591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-904537117/5000000000 : ℝ)|^4603 ≤ (2772966928749/25000000000000 : ℝ)^3579
        have hw : |(-904537117/5000000000 : ℝ)|=(904537117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428163511/10000000000 : ℝ)|^4603 ≤ (911514437043/2000000000000 : ℝ)^3579
        have hw : |(5428163511/10000000000 : ℝ)|=(5428163511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521925809/1000000000 : ℝ)|^4603 ≤ (10833102603591/25000000000000 : ℝ)^3579
        have hw : |(521925809/1000000000 : ℝ)|=(521925809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_1 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674638493/5000000000 : ℝ)*x 0 + (-1915984877/10000000000 : ℝ)*x 1 + (5219258273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674638493/5000000000 : ℝ)^4603 ≤ (11181412447941/25000000000000 : ℝ)^3579 := by
    have hnat : (2674638493 : ℕ)^4603*25000000000000^3579 ≤ 11181412447941^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674638493 5000000000 11181412447941 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915984877/10000000000 : ℝ)^4603 ≤ (11941937825093/100000000000000 : ℝ)^3579 := by
    have hnat : (1915984877 : ℕ)^4603*100000000000000^3579 ≤ 11941937825093^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915984877 10000000000 11941937825093 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219258273/10000000000 : ℝ)^4603 ≤ (43332412368409/100000000000000 : ℝ)^3579 := by
    have hnat : (5219258273 : ℕ)^4603*100000000000000^3579 ≤ 43332412368409^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219258273 10000000000 43332412368409 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674638493/5000000000 : ℝ), (-1915984877/10000000000 : ℝ), (5219258273/10000000000 : ℝ)] ![(11181412447941/25000000000000 : ℝ), (11941937825093/100000000000000 : ℝ), (43332412368409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674638493/5000000000 : ℝ)|^4603 ≤ (11181412447941/25000000000000 : ℝ)^3579
        have hw : |(2674638493/5000000000 : ℝ)|=(2674638493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1915984877/10000000000 : ℝ)|^4603 ≤ (11941937825093/100000000000000 : ℝ)^3579
        have hw : |(-1915984877/10000000000 : ℝ)|=(1915984877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219258273/10000000000 : ℝ)|^4603 ≤ (43332412368409/100000000000000 : ℝ)^3579
        have hw : |(5219258273/10000000000 : ℝ)|=(5219258273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_2 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8558843/16000000 : ℝ)*x 0 + (5219258341/10000000000 : ℝ)*x 1 + (-383196987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8558843/16000000 : ℝ)^4603 ≤ (894512971963/2000000000000 : ℝ)^3579 := by
    have hnat : (8558843 : ℕ)^4603*2000000000000^3579 ≤ 894512971963^3579*16000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8558843 16000000 894512971963 2000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219258341/10000000000 : ℝ)^4603 ≤ (21666206547251/50000000000000 : ℝ)^3579 := by
    have hnat : (5219258341 : ℕ)^4603*50000000000000^3579 ≤ 21666206547251^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219258341 10000000000 21666206547251 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383196987/2000000000 : ℝ)^4603 ≤ (5970969145013/50000000000000 : ℝ)^3579 := by
    have hnat : (383196987 : ℕ)^4603*50000000000000^3579 ≤ 5970969145013^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383196987 2000000000 5970969145013 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8558843/16000000 : ℝ), (5219258341/10000000000 : ℝ), (-383196987/2000000000 : ℝ)] ![(894512971963/2000000000000 : ℝ), (21666206547251/50000000000000 : ℝ), (5970969145013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8558843/16000000 : ℝ)|^4603 ≤ (894512971963/2000000000000 : ℝ)^3579
        have hw : |(8558843/16000000 : ℝ)|=(8558843/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219258341/10000000000 : ℝ)|^4603 ≤ (21666206547251/50000000000000 : ℝ)^3579
        have hw : |(5219258341/10000000000 : ℝ)|=(5219258341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383196987/2000000000 : ℝ)|^4603 ≤ (5970969145013/50000000000000 : ℝ)^3579
        have hw : |(-383196987/2000000000 : ℝ)|=(383196987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_3 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251033267/10000000000 : ℝ)*x 0 + (4013055139/10000000000 : ℝ)*x 1 + (4500482677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251033267/10000000000 : ℝ)^4603 ≤ (33281415434227/100000000000000 : ℝ)^3579 := by
    have hnat : (4251033267 : ℕ)^4603*100000000000000^3579 ≤ 33281415434227^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251033267 10000000000 33281415434227 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013055139/10000000000 : ℝ)^4603 ≤ (1236186575421/4000000000000 : ℝ)^3579 := by
    have hnat : (4013055139 : ℕ)^4603*4000000000000^3579 ≤ 1236186575421^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013055139 10000000000 1236186575421 4000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500482677/10000000000 : ℝ)^4603 ≤ (1790696008619/5000000000000 : ℝ)^3579 := by
    have hnat : (4500482677 : ℕ)^4603*5000000000000^3579 ≤ 1790696008619^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500482677 10000000000 1790696008619 5000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251033267/10000000000 : ℝ), (4013055139/10000000000 : ℝ), (4500482677/10000000000 : ℝ)] ![(33281415434227/100000000000000 : ℝ), (1236186575421/4000000000000 : ℝ), (1790696008619/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251033267/10000000000 : ℝ)|^4603 ≤ (33281415434227/100000000000000 : ℝ)^3579
        have hw : |(4251033267/10000000000 : ℝ)|=(4251033267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013055139/10000000000 : ℝ)|^4603 ≤ (1236186575421/4000000000000 : ℝ)^3579
        have hw : |(4013055139/10000000000 : ℝ)|=(4013055139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500482677/10000000000 : ℝ)|^4603 ≤ (1790696008619/5000000000000 : ℝ)^3579
        have hw : |(4500482677/10000000000 : ℝ)|=(4500482677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_4 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-452275417/2500000000 : ℝ)*x 0 + (1044068927/2000000000 : ℝ)*x 1 + (5427069001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452275417/2500000000 : ℝ)^4603 ≤ (5546042022721/50000000000000 : ℝ)^3579 := by
    have hnat : (452275417 : ℕ)^4603*50000000000000^3579 ≤ 5546042022721^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452275417 2500000000 5546042022721 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044068927/2000000000 : ℝ)^4603 ≤ (43344012711993/100000000000000 : ℝ)^3579 := by
    have hnat : (1044068927 : ℕ)^4603*100000000000000^3579 ≤ 43344012711993^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044068927 2000000000 43344012711993 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427069001/10000000000 : ℝ)^4603 ≤ (45563903222687/100000000000000 : ℝ)^3579 := by
    have hnat : (5427069001 : ℕ)^4603*100000000000000^3579 ≤ 45563903222687^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427069001 10000000000 45563903222687 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-452275417/2500000000 : ℝ), (1044068927/2000000000 : ℝ), (5427069001/10000000000 : ℝ)] ![(5546042022721/50000000000000 : ℝ), (43344012711993/100000000000000 : ℝ), (45563903222687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-452275417/2500000000 : ℝ)|^4603 ≤ (5546042022721/50000000000000 : ℝ)^3579
        have hw : |(-452275417/2500000000 : ℝ)|=(452275417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044068927/2000000000 : ℝ)|^4603 ≤ (43344012711993/100000000000000 : ℝ)^3579
        have hw : |(1044068927/2000000000 : ℝ)|=(1044068927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427069001/10000000000 : ℝ)|^4603 ≤ (45563903222687/100000000000000 : ℝ)^3579
        have hw : |(5427069001/10000000000 : ℝ)|=(5427069001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_5 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058824573/2000000000 : ℝ)*x 0 + (-1708174143/10000000000 : ℝ)*x 1 + (5427068979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058824573/2000000000 : ℝ)^4603 ≤ (2758339949219/6250000000000 : ℝ)^3579 := by
    have hnat : (1058824573 : ℕ)^4603*6250000000000^3579 ≤ 2758339949219^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058824573 2000000000 2758339949219 6250000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708174143/10000000000 : ℝ)^4603 ≤ (5151328904331/50000000000000 : ℝ)^3579 := by
    have hnat : (1708174143 : ℕ)^4603*50000000000000^3579 ≤ 5151328904331^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708174143 10000000000 5151328904331 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427068979/10000000000 : ℝ)^4603 ≤ (2847743936571/6250000000000 : ℝ)^3579 := by
    have hnat : (5427068979 : ℕ)^4603*6250000000000^3579 ≤ 2847743936571^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427068979 10000000000 2847743936571 6250000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058824573/2000000000 : ℝ), (-1708174143/10000000000 : ℝ), (5427068979/10000000000 : ℝ)] ![(2758339949219/6250000000000 : ℝ), (5151328904331/50000000000000 : ℝ), (2847743936571/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058824573/2000000000 : ℝ)|^4603 ≤ (2758339949219/6250000000000 : ℝ)^3579
        have hw : |(1058824573/2000000000 : ℝ)|=(1058824573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1708174143/10000000000 : ℝ)|^4603 ≤ (5151328904331/50000000000000 : ℝ)^3579
        have hw : |(-1708174143/10000000000 : ℝ)|=(1708174143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427068979/10000000000 : ℝ)|^4603 ≤ (2847743936571/6250000000000 : ℝ)^3579
        have hw : |(5427068979/10000000000 : ℝ)|=(5427068979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_6 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647061423/5000000000 : ℝ)*x 0 + (678383621/1250000000 : ℝ)*x 1 + (-341634837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647061423/5000000000 : ℝ)^4603 ≤ (11033359745949/25000000000000 : ℝ)^3579 := by
    have hnat : (2647061423 : ℕ)^4603*25000000000000^3579 ≤ 11033359745949^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647061423 5000000000 11033359745949 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678383621/1250000000 : ℝ)^4603 ≤ (1139097571659/2500000000000 : ℝ)^3579 := by
    have hnat : (678383621 : ℕ)^4603*2500000000000^3579 ≤ 1139097571659^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678383621 1250000000 1139097571659 2500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341634837/2000000000 : ℝ)^4603 ≤ (5151329067229/50000000000000 : ℝ)^3579 := by
    have hnat : (341634837 : ℕ)^4603*50000000000000^3579 ≤ 5151329067229^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341634837 2000000000 5151329067229 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647061423/5000000000 : ℝ), (678383621/1250000000 : ℝ), (-341634837/2000000000 : ℝ)] ![(11033359745949/25000000000000 : ℝ), (1139097571659/2500000000000 : ℝ), (5151329067229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647061423/5000000000 : ℝ)|^4603 ≤ (11033359745949/25000000000000 : ℝ)^3579
        have hw : |(2647061423/5000000000 : ℝ)|=(2647061423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678383621/1250000000 : ℝ)|^4603 ≤ (1139097571659/2500000000000 : ℝ)^3579
        have hw : |(678383621/1250000000 : ℝ)|=(678383621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341634837/2000000000 : ℝ)|^4603 ≤ (5151329067229/50000000000000 : ℝ)^3579
        have hw : |(-341634837/2000000000 : ℝ)|=(341634837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s4_7 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251097489/10000000000 : ℝ)*x 0 + (4497948013/10000000000 : ℝ)*x 1 + (200780429/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251097489/10000000000 : ℝ)^4603 ≤ (33282062087271/100000000000000 : ℝ)^3579 := by
    have hnat : (4251097489 : ℕ)^4603*100000000000000^3579 ≤ 33282062087271^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251097489 10000000000 33282062087271 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497948013/10000000000 : ℝ)^4603 ≤ (35787980920697/100000000000000 : ℝ)^3579 := by
    have hnat : (4497948013 : ℕ)^4603*100000000000000^3579 ≤ 35787980920697^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497948013 10000000000 35787980920697 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200780429/500000000 : ℝ)^4603 ≤ (3866244623603/12500000000000 : ℝ)^3579 := by
    have hnat : (200780429 : ℕ)^4603*12500000000000^3579 ≤ 3866244623603^3579*500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200780429 500000000 3866244623603 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251097489/10000000000 : ℝ), (4497948013/10000000000 : ℝ), (200780429/500000000 : ℝ)] ![(33282062087271/100000000000000 : ℝ), (35787980920697/100000000000000 : ℝ), (3866244623603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251097489/10000000000 : ℝ)|^4603 ≤ (33282062087271/100000000000000 : ℝ)^3579
        have hw : |(4251097489/10000000000 : ℝ)|=(4251097489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497948013/10000000000 : ℝ)|^4603 ≤ (35787980920697/100000000000000 : ℝ)^3579
        have hw : |(4497948013/10000000000 : ℝ)|=(4497948013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200780429/500000000 : ℝ)|^4603 ≤ (3866244623603/12500000000000 : ℝ)^3579
        have hw : |(200780429/500000000 : ℝ)|=(200780429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1553_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11061/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (441/4000 : ℝ) ^ (4601/1024 : ℝ) ≤ (2490118048080073/50000000000000000000 : ℝ) := by
    have hpowers : (441/4000 : ℝ)^4601 ≤ (2490118048080073/50000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^4601*50000000000000000000^1024 ≤ 2490118048080073^1024*4000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 4000 2490118048080073 50000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/4000 : ℝ)) (X := (2490118048080073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15527/100000 : ℝ) ^ (4601/1024 : ℝ) ≤ (23196564204785139/100000000000000000000 : ℝ) := by
    have hpowers : (15527/100000 : ℝ)^4601 ≤ (23196564204785139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15527 : ℕ)^4601*100000000000000000000^1024 ≤ 23196564204785139^1024*100000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15527 100000 23196564204785139 100000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15527/100000 : ℝ)) (X := (23196564204785139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002490118048080073/25000000000000000000 : ℝ) ≤ (2000044334399651/2000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (25002490118048080073/25000000000000000000 : ℝ)^1024 ≤ (2000044334399651/2000000000000000 : ℝ)^4601 := by
      have hnat : (25002490118048080073 : ℕ)^1024*2000000000000000^4601 ≤ 2000044334399651^4601*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002490118048080073 25000000000000000000 2000044334399651 2000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000044334399651/2000000000000000 : ℝ)) (X := (25002490118048080073/25000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005635360060189057/20000000000000000000 : ℝ) ≤ (10000627035074897/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (20005635360060189057/20000000000000000000 : ℝ)^1024 ≤ (10000627035074897/10000000000000000 : ℝ)^4601 := by
      have hnat : (20005635360060189057 : ℕ)^1024*10000000000000000^4601 ≤ 10000627035074897^4601*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005635360060189057 20000000000000000000 10000627035074897 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000627035074897/10000000000000000 : ℝ)) (X := (20005635360060189057/20000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023196564204785139/50000000000000000000 : ℝ) ≤ (10001032398151539/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (50023196564204785139/50000000000000000000 : ℝ)^1024 ≤ (10001032398151539/10000000000000000 : ℝ)^4601 := by
      have hnat : (50023196564204785139 : ℕ)^1024*10000000000000000^4601 ≤ 10001032398151539^4601*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023196564204785139 50000000000000000000 10001032398151539 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001032398151539/10000000000000000 : ℝ)) (X := (50023196564204785139/50000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2490118048080073/50000000000000000000 : ℝ) ≤ ((4501205971149618791/4502000000000000000 : ℝ)+2*(202681538321/225100000000000 : ℝ)*(441/4000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (4501205971149618791/4502000000000000000 : ℝ)+2*(202681538321/225100000000000 : ℝ)*(441/4000 : ℝ)=(2000044334399651/2000000000000000 : ℝ) by norm_num, show 1+2*(2490118048080073/50000000000000000000 : ℝ)=(25002490118048080073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23196564204785139/100000000000000000000 : ℝ)+(2490118048080073/50000000000000000000 : ℝ) ≤ ((4501205971149618791/4502000000000000000 : ℝ)+(202681538321/225100000000000 : ℝ)*((15527/100000 : ℝ)+(441/4000 : ℝ)))^(4601/1024 : ℝ) := by
    rw [show (4501205971149618791/4502000000000000000 : ℝ)+(202681538321/225100000000000 : ℝ)*((15527/100000 : ℝ)+(441/4000 : ℝ))=(10000627035074897/10000000000000000 : ℝ) by norm_num, show 1+(23196564204785139/100000000000000000000 : ℝ)+(2490118048080073/50000000000000000000 : ℝ)=(20005635360060189057/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23196564204785139/100000000000000000000 : ℝ) ≤ ((4501205971149618791/4502000000000000000 : ℝ)+2*(202681538321/225100000000000 : ℝ)*(15527/100000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (4501205971149618791/4502000000000000000 : ℝ)+2*(202681538321/225100000000000 : ℝ)*(15527/100000 : ℝ)=(10001032398151539/10000000000000000 : ℝ) by norm_num, show 1+2*(23196564204785139/100000000000000000000 : ℝ)=(50023196564204785139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4501205971149618791/4502000000000000000 : ℝ)*(X 1 0+X 2 0)+(202681538321/225100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (4501205971149618791/4502000000000000000 : ℝ)) (alpha := (202681538321/225100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4501205971149618791/4502000000000000000 : ℝ)*(X 0 1+X 2 1)+(202681538321/225100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (4501205971149618791/4502000000000000000 : ℝ)) (alpha := (202681538321/225100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4501205971149618791/4502000000000000000 : ℝ)*(X 0 2+X 1 2)+(202681538321/225100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (4501205971149618791/4502000000000000000 : ℝ)) (alpha := (202681538321/225100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-904537117/5000000000 : ℝ)*X 0 0+(5428163511/10000000000 : ℝ)*X 0 1+(521925809/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674638493/5000000000 : ℝ)*X 1 0+(-1915984877/10000000000 : ℝ)*X 1 1+(5219258273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8558843/16000000 : ℝ)*X 2 0+(5219258341/10000000000 : ℝ)*X 2 1+(-383196987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4251033267/10000000000 : ℝ)*X 0 0+(4013055139/10000000000 : ℝ)*X 0 1+(4500482677/10000000000 : ℝ)*X 0 2+(4251033267/10000000000 : ℝ)*X 1 0+(4013055139/10000000000 : ℝ)*X 1 1+(4500482677/10000000000 : ℝ)*X 1 2+(4251033267/10000000000 : ℝ)*X 2 0+(4013055139/10000000000 : ℝ)*X 2 1+(4500482677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-452275417/2500000000 : ℝ)*X 0 0+(1044068927/2000000000 : ℝ)*X 0 1+(5427069001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058824573/2000000000 : ℝ)*X 1 0+(-1708174143/10000000000 : ℝ)*X 1 1+(5427068979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647061423/5000000000 : ℝ)*X 2 0+(678383621/1250000000 : ℝ)*X 2 1+(-341634837/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251097489/10000000000 : ℝ)*X 0 0+(4497948013/10000000000 : ℝ)*X 0 1+(200780429/500000000 : ℝ)*X 0 2+(4251097489/10000000000 : ℝ)*X 1 0+(4497948013/10000000000 : ℝ)*X 1 1+(200780429/500000000 : ℝ)*X 1 2+(4251097489/10000000000 : ℝ)*X 2 0+(4497948013/10000000000 : ℝ)*X 2 1+(200780429/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (972300624758581570860695019/225100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432569369/50000000000000 : ℝ)*(base19) + (705054437/100000000000000 : ℝ)*(base23) + (44058613/25000000000000 : ℝ)*(upper3) + (32499059/100000000000000 : ℝ)*(upper4) + (30482797/50000000000000 : ℝ)*(upper5) + (3419244094926101/100000000000000 : ℝ)*(major0) + (3419244094926101/100000000000000 : ℝ)*(major1) + (3419244094926101/100000000000000 : ℝ)*(major2) + (957374816564053/20000000000000 : ℝ)*(sp0) + (2393444427634193/50000000000000 : ℝ)*(sp1) + (4786889015352687/100000000000000 : ℝ)*(sp2) + (2051592046558161/100000000000000 : ℝ)*(sp3) + (7818793429/50000000000000 : ℝ)*(sp4) + (1569726591/25000000000000 : ℝ)*(sp7) + (82063933018581/4000000000000 : ℝ)*(f.failure) + (1196722430101781/25000000000000 : ℝ)*(f.sum) + (13394297318013/5627500000000000000000000000 : ℝ)*base65 + (1535549624676816109/450200000000000000000000000000000 : ℝ)*base68 + (5987267448020616109/450200000000000000000000000000000 : ℝ)*base70 + (4529368470071416109/450200000000000000000000000000000 : ℝ)*base72 + (21737264381113/5627500000000000000000000000 : ℝ)*base73 + (4930141424454616109/450200000000000000000000000000000 : ℝ)*base76 + (2933431317827216109/450200000000000000000000000000000 : ℝ)*base78 + (4115355455581216109/450200000000000000000000000000000 : ℝ)*base80 + (42813213867439/11255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (39193/400000000000000000000 : ℝ)*base89 + (39193/400000000000000000000 : ℝ)*base91 + (39193/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14418130051409414142095109/3517187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (379536399/50000000000000 : ℝ)*(base19) + (376047201/50000000000000 : ℝ)*(base23) + (43897829/50000000000000 : ℝ)*(upper3) + (9438419/100000000000000 : ℝ)*(lower4) + (17237641/20000000000000 : ℝ)*(upper5) + (13497241353627/390625000000 : ℝ)*(major0) + (13497241353627/390625000000 : ℝ)*(major1) + (13497241353627/390625000000 : ℝ)*(major2) + (5983351671/50000000000000 : ℝ)*(sp1) + (11252018047/100000000000000 : ℝ)*(sp2) + (604669843640967/12500000000000 : ℝ)*(sp4) + (1209336505837899/25000000000000 : ℝ)*(sp5) + (4837346745015287/100000000000000 : ℝ)*(sp6) + (103661434364239/5000000000000 : ℝ)*(sp7) + (103661434364239/5000000000000 : ℝ)*(f.failure) + (604669843640967/12500000000000 : ℝ)*(f.sum) + (4482958523877/2813750000000000000000000000 : ℝ)*base66 + (5124729668907209/879296875000000000000000000000 : ℝ)*base68 + (10144098344501207/1758593750000000000000000000000 : ℝ)*base69 + (9087552450419709/879296875000000000000000000000 : ℝ)*base72 + (6267796449519/5627500000000000000000000000 : ℝ)*base74 + (10802070777105539/3517187500000000000000000000000 : ℝ)*base75 + (68887648896873297/7034375000000000000000000000000 : ℝ)*base78 + (41654126833235797/7034375000000000000000000000000 : ℝ)*base80 + (334137445431/1406875000000000000000000000 : ℝ)*base82 + (7218267/500000000000000000000 : ℝ)*base89 + (7218267/500000000000000000000 : ℝ)*base91 + (7218267/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1553_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1553_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1553_s5_0 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-904551039/5000000000 : ℝ)*x 0 + (2713983431/5000000000 : ℝ)*x 1 + (1043887279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904551039/5000000000 : ℝ)^4603 ≤ (11092087278499/100000000000000 : ℝ)^3579 := by
    have hnat : (904551039 : ℕ)^4603*100000000000000^3579 ≤ 11092087278499^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904551039 5000000000 11092087278499 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713983431/5000000000 : ℝ)^4603 ≤ (45573598366147/100000000000000 : ℝ)^3579 := by
    have hnat : (2713983431 : ℕ)^4603*100000000000000^3579 ≤ 45573598366147^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713983431 5000000000 45573598366147 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043887279/2000000000 : ℝ)^4603 ≤ (43334314335677/100000000000000 : ℝ)^3579 := by
    have hnat : (1043887279 : ℕ)^4603*100000000000000^3579 ≤ 43334314335677^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043887279 2000000000 43334314335677 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-904551039/5000000000 : ℝ), (2713983431/5000000000 : ℝ), (1043887279/2000000000 : ℝ)] ![(11092087278499/100000000000000 : ℝ), (45573598366147/100000000000000 : ℝ), (43334314335677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-904551039/5000000000 : ℝ)|^4603 ≤ (11092087278499/100000000000000 : ℝ)^3579
        have hw : |(-904551039/5000000000 : ℝ)|=(904551039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713983431/5000000000 : ℝ)|^4603 ≤ (45573598366147/100000000000000 : ℝ)^3579
        have hw : |(2713983431/5000000000 : ℝ)|=(2713983431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043887279/2000000000 : ℝ)|^4603 ≤ (43334314335677/100000000000000 : ℝ)^3579
        have hw : |(1043887279/2000000000 : ℝ)|=(1043887279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_1 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674612687/5000000000 : ℝ)*x 0 + (-478954201/2500000000 : ℝ)*x 1 + (5219436423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674612687/5000000000 : ℝ)^4603 ≤ (44725094794377/100000000000000 : ℝ)^3579 := by
    have hnat : (2674612687 : ℕ)^4603*100000000000000^3579 ≤ 44725094794377^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674612687 5000000000 44725094794377 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478954201/2500000000 : ℝ)^4603 ≤ (11940590555503/100000000000000 : ℝ)^3579 := by
    have hnat : (478954201 : ℕ)^4603*100000000000000^3579 ≤ 11940590555503^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478954201 2500000000 11940590555503 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219436423/10000000000 : ℝ)^4603 ≤ (2166715731733/5000000000000 : ℝ)^3579 := by
    have hnat : (5219436423 : ℕ)^4603*5000000000000^3579 ≤ 2166715731733^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219436423 10000000000 2166715731733 5000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674612687/5000000000 : ℝ), (-478954201/2500000000 : ℝ), (5219436423/10000000000 : ℝ)] ![(44725094794377/100000000000000 : ℝ), (11940590555503/100000000000000 : ℝ), (2166715731733/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674612687/5000000000 : ℝ)|^4603 ≤ (44725094794377/100000000000000 : ℝ)^3579
        have hw : |(2674612687/5000000000 : ℝ)|=(2674612687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478954201/2500000000 : ℝ)|^4603 ≤ (11940590555503/100000000000000 : ℝ)^3579
        have hw : |(-478954201/2500000000 : ℝ)|=(478954201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219436423/10000000000 : ℝ)|^4603 ≤ (2166715731733/5000000000000 : ℝ)^3579
        have hw : |(5219436423/10000000000 : ℝ)|=(5219436423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_2 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069845047/2000000000 : ℝ)*x 0 + (5219436621/10000000000 : ℝ)*x 1 + (-239477091/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069845047/2000000000 : ℝ)^4603 ≤ (11181273324919/25000000000000 : ℝ)^3579 := by
    have hnat : (1069845047 : ℕ)^4603*25000000000000^3579 ≤ 11181273324919^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069845047 2000000000 11181273324919 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219436621/10000000000 : ℝ)^4603 ≤ (10833579187223/25000000000000 : ℝ)^3579 := by
    have hnat : (5219436621 : ℕ)^4603*25000000000000^3579 ≤ 10833579187223^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219436621 10000000000 10833579187223 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239477091/1250000000 : ℝ)^4603 ≤ (1492573743287/12500000000000 : ℝ)^3579 := by
    have hnat : (239477091 : ℕ)^4603*12500000000000^3579 ≤ 1492573743287^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239477091 1250000000 1492573743287 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069845047/2000000000 : ℝ), (5219436621/10000000000 : ℝ), (-239477091/1250000000 : ℝ)] ![(11181273324919/25000000000000 : ℝ), (10833579187223/25000000000000 : ℝ), (1492573743287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069845047/2000000000 : ℝ)|^4603 ≤ (11181273324919/25000000000000 : ℝ)^3579
        have hw : |(1069845047/2000000000 : ℝ)|=(1069845047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219436621/10000000000 : ℝ)|^4603 ≤ (10833579187223/25000000000000 : ℝ)^3579
        have hw : |(5219436621/10000000000 : ℝ)|=(5219436621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239477091/1250000000 : ℝ)|^4603 ≤ (1492573743287/12500000000000 : ℝ)^3579
        have hw : |(-239477091/1250000000 : ℝ)|=(239477091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_3 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125525869/5000000000 : ℝ)*x 0 + (4013490073/10000000000 : ℝ)*x 1 + (4500043591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125525869/5000000000 : ℝ)^4603 ≤ (4160200177367/12500000000000 : ℝ)^3579 := by
    have hnat : (2125525869 : ℕ)^4603*12500000000000^3579 ≤ 4160200177367^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125525869 5000000000 4160200177367 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013490073/10000000000 : ℝ)^4603 ≤ (30908972212719/100000000000000 : ℝ)^3579 := by
    have hnat : (4013490073 : ℕ)^4603*100000000000000^3579 ≤ 30908972212719^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013490073 10000000000 30908972212719 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500043591/10000000000 : ℝ)^4603 ≤ (1432377054137/4000000000000 : ℝ)^3579 := by
    have hnat : (4500043591 : ℕ)^4603*4000000000000^3579 ≤ 1432377054137^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500043591 10000000000 1432377054137 4000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125525869/5000000000 : ℝ), (4013490073/10000000000 : ℝ), (4500043591/10000000000 : ℝ)] ![(4160200177367/12500000000000 : ℝ), (30908972212719/100000000000000 : ℝ), (1432377054137/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125525869/5000000000 : ℝ)|^4603 ≤ (4160200177367/12500000000000 : ℝ)^3579
        have hw : |(2125525869/5000000000 : ℝ)|=(2125525869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013490073/10000000000 : ℝ)|^4603 ≤ (30908972212719/100000000000000 : ℝ)^3579
        have hw : |(4013490073/10000000000 : ℝ)|=(4013490073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500043591/10000000000 : ℝ)|^4603 ≤ (1432377054137/4000000000000 : ℝ)^3579
        have hw : |(4500043591/10000000000 : ℝ)|=(4500043591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_4 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1809129563/10000000000 : ℝ)*x 0 + (1305129721/2500000000 : ℝ)*x 1 + (1085375261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1809129563/10000000000 : ℝ)^4603 ≤ (554615200603/5000000000000 : ℝ)^3579 := by
    have hnat : (1809129563 : ℕ)^4603*5000000000000^3579 ≤ 554615200603^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809129563 10000000000 554615200603 5000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305129721/2500000000 : ℝ)^4603 ≤ (43345873434387/100000000000000 : ℝ)^3579 := by
    have hnat : (1305129721 : ℕ)^4603*100000000000000^3579 ≤ 43345873434387^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305129721 2500000000 43345873434387 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085375261/2000000000 : ℝ)^4603 ≤ (5695227817803/12500000000000 : ℝ)^3579 := by
    have hnat : (1085375261 : ℕ)^4603*12500000000000^3579 ≤ 5695227817803^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085375261 2000000000 5695227817803 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1809129563/10000000000 : ℝ), (1305129721/2500000000 : ℝ), (1085375261/2000000000 : ℝ)] ![(554615200603/5000000000000 : ℝ), (43345873434387/100000000000000 : ℝ), (5695227817803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1809129563/10000000000 : ℝ)|^4603 ≤ (554615200603/5000000000000 : ℝ)^3579
        have hw : |(-1809129563/10000000000 : ℝ)|=(1809129563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305129721/2500000000 : ℝ)|^4603 ≤ (43345873434387/100000000000000 : ℝ)^3579
        have hw : |(1305129721/2500000000 : ℝ)|=(1305129721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085375261/2000000000 : ℝ)|^4603 ≤ (5695227817803/12500000000000 : ℝ)^3579
        have hw : |(1085375261/2000000000 : ℝ)|=(1085375261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_5 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647085111/5000000000 : ℝ)*x 0 + (-1708376887/10000000000 : ℝ)*x 1 + (339179769/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647085111/5000000000 : ℝ)^4603 ≤ (22066973461643/50000000000000 : ℝ)^3579 := by
    have hnat : (2647085111 : ℕ)^4603*50000000000000^3579 ≤ 22066973461643^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647085111 5000000000 22066973461643 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708376887/10000000000 : ℝ)^4603 ≤ (10304230530049/100000000000000 : ℝ)^3579 := by
    have hnat : (1708376887 : ℕ)^4603*100000000000000^3579 ≤ 10304230530049^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708376887 10000000000 10304230530049 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339179769/625000000 : ℝ)^4603 ≤ (22780911265813/50000000000000 : ℝ)^3579 := by
    have hnat : (339179769 : ℕ)^4603*50000000000000^3579 ≤ 22780911265813^3579*625000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339179769 625000000 22780911265813 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647085111/5000000000 : ℝ), (-1708376887/10000000000 : ℝ), (339179769/625000000 : ℝ)] ![(22066973461643/50000000000000 : ℝ), (10304230530049/100000000000000 : ℝ), (22780911265813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647085111/5000000000 : ℝ)|^4603 ≤ (22066973461643/50000000000000 : ℝ)^3579
        have hw : |(2647085111/5000000000 : ℝ)|=(2647085111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1708376887/10000000000 : ℝ)|^4603 ≤ (10304230530049/100000000000000 : ℝ)^3579
        have hw : |(-1708376887/10000000000 : ℝ)|=(1708376887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339179769/625000000 : ℝ)|^4603 ≤ (22780911265813/50000000000000 : ℝ)^3579
        have hw : |(339179769/625000000 : ℝ)|=(339179769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_6 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211766809/400000000 : ℝ)*x 0 + (2713438151/5000000000 : ℝ)*x 1 + (-1708376887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211766809/400000000 : ℝ)^4603 ≤ (882678939109/2000000000000 : ℝ)^3579 := by
    have hnat : (211766809 : ℕ)^4603*2000000000000^3579 ≤ 882678939109^3579*400000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211766809 400000000 882678939109 2000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713438151/5000000000 : ℝ)^4603 ≤ (45561822510031/100000000000000 : ℝ)^3579 := by
    have hnat : (2713438151 : ℕ)^4603*100000000000000^3579 ≤ 45561822510031^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713438151 5000000000 45561822510031 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1708376887/10000000000 : ℝ)^4603 ≤ (10304230530049/100000000000000 : ℝ)^3579 := by
    have hnat : (1708376887 : ℕ)^4603*100000000000000^3579 ≤ 10304230530049^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708376887 10000000000 10304230530049 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211766809/400000000 : ℝ), (2713438151/5000000000 : ℝ), (-1708376887/10000000000 : ℝ)] ![(882678939109/2000000000000 : ℝ), (45561822510031/100000000000000 : ℝ), (10304230530049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211766809/400000000 : ℝ)|^4603 ≤ (882678939109/2000000000000 : ℝ)^3579
        have hw : |(211766809/400000000 : ℝ)|=(211766809/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713438151/5000000000 : ℝ)|^4603 ≤ (45561822510031/100000000000000 : ℝ)^3579
        have hw : |(2713438151/5000000000 : ℝ)|=(2713438151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1708376887/10000000000 : ℝ)|^4603 ≤ (10304230530049/100000000000000 : ℝ)^3579
        have hw : |(-1708376887/10000000000 : ℝ)|=(1708376887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s5_7 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251115653/10000000000 : ℝ)*x 0 + (1124379447/2500000000 : ℝ)*x 1 + (4016034521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251115653/10000000000 : ℝ)^4603 ≤ (16641122490791/50000000000000 : ℝ)^3579 := by
    have hnat : (4251115653 : ℕ)^4603*50000000000000^3579 ≤ 16641122490791^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251115653 10000000000 16641122490791 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124379447/2500000000 : ℝ)^4603 ≤ (17891789248981/50000000000000 : ℝ)^3579 := by
    have hnat : (1124379447 : ℕ)^4603*50000000000000^3579 ≤ 17891789248981^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124379447 2500000000 17891789248981 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016034521/10000000000 : ℝ)^4603 ≤ (30934176510819/100000000000000 : ℝ)^3579 := by
    have hnat : (4016034521 : ℕ)^4603*100000000000000^3579 ≤ 30934176510819^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016034521 10000000000 30934176510819 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251115653/10000000000 : ℝ), (1124379447/2500000000 : ℝ), (4016034521/10000000000 : ℝ)] ![(16641122490791/50000000000000 : ℝ), (17891789248981/50000000000000 : ℝ), (30934176510819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251115653/10000000000 : ℝ)|^4603 ≤ (16641122490791/50000000000000 : ℝ)^3579
        have hw : |(4251115653/10000000000 : ℝ)|=(4251115653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124379447/2500000000 : ℝ)|^4603 ≤ (17891789248981/50000000000000 : ℝ)^3579
        have hw : |(1124379447/2500000000 : ℝ)|=(1124379447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016034521/10000000000 : ℝ)|^4603 ≤ (30934176510819/100000000000000 : ℝ)^3579
        have hw : |(4016034521/10000000000 : ℝ)|=(4016034521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1553_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2213/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11061/100000 : ℝ) ^ (4601/1024 : ℝ) ≤ (5053721756617507/100000000000000000000 : ℝ) := by
    have hpowers : (11061/100000 : ℝ)^4601 ≤ (5053721756617507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11061 : ℕ)^4601*100000000000000000000^1024 ≤ 5053721756617507^1024*100000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11061 100000 5053721756617507 100000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11061/100000 : ℝ)) (X := (5053721756617507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4601/1024 : ℝ) ≤ (11471287457799599/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4601 ≤ (11471287457799599/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4601*50000000000000000000^1024 ≤ 11471287457799599^1024*100000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 11471287457799599 50000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (11471287457799599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005053721756617507/50000000000000000000 : ℝ) ≤ (1250028117842679/1250000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (50005053721756617507/50000000000000000000 : ℝ)^1024 ≤ (1250028117842679/1250000000000000 : ℝ)^4601 := by
      have hnat : (50005053721756617507 : ℕ)^1024*1250000000000000^4601 ≤ 1250028117842679^4601*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005053721756617507 50000000000000000000 1250028117842679 1250000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250028117842679/1250000000000000 : ℝ)) (X := (50005053721756617507/50000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005599259334443341/20000000000000000000 : ℝ) ≤ (2500155754664367/2500000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (20005599259334443341/20000000000000000000 : ℝ)^1024 ≤ (2500155754664367/2500000000000000 : ℝ)^4601 := by
      have hnat : (20005599259334443341 : ℕ)^1024*2500000000000000^4601 ≤ 2500155754664367^4601*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005599259334443341 20000000000000000000 2500155754664367 2500000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500155754664367/2500000000000000 : ℝ)) (X := (20005599259334443341/20000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011471287457799599/25000000000000000000 : ℝ) ≤ (156265954602711/156250000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (25011471287457799599/25000000000000000000 : ℝ)^1024 ≤ (156265954602711/156250000000000 : ℝ)^4601 := by
      have hnat : (25011471287457799599 : ℕ)^1024*156250000000000^4601 ≤ 156265954602711^4601*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011471287457799599 25000000000000000000 156265954602711 156250000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156265954602711/156250000000000 : ℝ)) (X := (25011471287457799599/25000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5053721756617507/100000000000000000000 : ℝ) ≤ ((204963841717798669/205000000000000000 : ℝ)+2*(33172993003/36900000000000 : ℝ)*(11061/100000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (204963841717798669/205000000000000000 : ℝ)+2*(33172993003/36900000000000 : ℝ)*(11061/100000 : ℝ)=(1250028117842679/1250000000000000 : ℝ) by norm_num, show 1+2*(5053721756617507/100000000000000000000 : ℝ)=(50005053721756617507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11471287457799599/50000000000000000000 : ℝ)+(5053721756617507/100000000000000000000 : ℝ) ≤ ((204963841717798669/205000000000000000 : ℝ)+(33172993003/36900000000000 : ℝ)*((15489/100000 : ℝ)+(11061/100000 : ℝ)))^(4601/1024 : ℝ) := by
    rw [show (204963841717798669/205000000000000000 : ℝ)+(33172993003/36900000000000 : ℝ)*((15489/100000 : ℝ)+(11061/100000 : ℝ))=(2500155754664367/2500000000000000 : ℝ) by norm_num, show 1+(11471287457799599/50000000000000000000 : ℝ)+(5053721756617507/100000000000000000000 : ℝ)=(20005599259334443341/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11471287457799599/50000000000000000000 : ℝ) ≤ ((204963841717798669/205000000000000000 : ℝ)+2*(33172993003/36900000000000 : ℝ)*(15489/100000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (204963841717798669/205000000000000000 : ℝ)+2*(33172993003/36900000000000 : ℝ)*(15489/100000 : ℝ)=(156265954602711/156250000000000 : ℝ) by norm_num, show 1+2*(11471287457799599/50000000000000000000 : ℝ)=(25011471287457799599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (204963841717798669/205000000000000000 : ℝ)*(X 1 0+X 2 0)+(33172993003/36900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (204963841717798669/205000000000000000 : ℝ)) (alpha := (33172993003/36900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (204963841717798669/205000000000000000 : ℝ)*(X 0 1+X 2 1)+(33172993003/36900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (204963841717798669/205000000000000000 : ℝ)) (alpha := (33172993003/36900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (204963841717798669/205000000000000000 : ℝ)*(X 0 2+X 1 2)+(33172993003/36900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (204963841717798669/205000000000000000 : ℝ)) (alpha := (33172993003/36900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-904551039/5000000000 : ℝ)*X 0 0+(2713983431/5000000000 : ℝ)*X 0 1+(1043887279/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674612687/5000000000 : ℝ)*X 1 0+(-478954201/2500000000 : ℝ)*X 1 1+(5219436423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069845047/2000000000 : ℝ)*X 2 0+(5219436621/10000000000 : ℝ)*X 2 1+(-239477091/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125525869/5000000000 : ℝ)*X 0 0+(4013490073/10000000000 : ℝ)*X 0 1+(4500043591/10000000000 : ℝ)*X 0 2+(2125525869/5000000000 : ℝ)*X 1 0+(4013490073/10000000000 : ℝ)*X 1 1+(4500043591/10000000000 : ℝ)*X 1 2+(2125525869/5000000000 : ℝ)*X 2 0+(4013490073/10000000000 : ℝ)*X 2 1+(4500043591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1809129563/10000000000 : ℝ)*X 0 0+(1305129721/2500000000 : ℝ)*X 0 1+(1085375261/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647085111/5000000000 : ℝ)*X 1 0+(-1708376887/10000000000 : ℝ)*X 1 1+(339179769/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211766809/400000000 : ℝ)*X 2 0+(2713438151/5000000000 : ℝ)*X 2 1+(-1708376887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251115653/10000000000 : ℝ)*X 0 0+(1124379447/2500000000 : ℝ)*X 0 1+(4016034521/10000000000 : ℝ)*X 0 2+(4251115653/10000000000 : ℝ)*X 1 0+(1124379447/2500000000 : ℝ)*X 1 1+(4016034521/10000000000 : ℝ)*X 1 2+(4251115653/10000000000 : ℝ)*X 2 0+(1124379447/2500000000 : ℝ)*X 2 1+(4016034521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161609961733330422491/51250000000000000000000000 : ℝ) := by norm_num
    linear_combination (36759149/10000000000000 : ℝ)*(base19) + (129560841/100000000000000 : ℝ)*(base23) + (7583857/12500000000000 : ℝ)*(lower2) + (7237841/12500000000000 : ℝ)*(upper3) + (1022301/3125000000000 : ℝ)*(upper5) + (107043019951083/3125000000000 : ℝ)*(major0) + (107043019951083/3125000000000 : ℝ)*(major1) + (107043019951083/3125000000000 : ℝ)*(major2) + (4795468899830517/100000000000000 : ℝ)*(sp0) + (959094971913571/20000000000000 : ℝ)*(sp1) + (599434387199813/12500000000000 : ℝ)*(sp2) + (1027637487471123/50000000000000 : ℝ)*(sp3) + (6327328829/100000000000000 : ℝ)*(sp4) + (2969655543/100000000000000 : ℝ)*(sp7) + (2055277944597789/100000000000000 : ℝ)*(f.failure) + (2397737613579673/50000000000000 : ℝ)*(f.sum) + (884359772573/307500000000000000000000000 : ℝ)*base65 + (8984830888261919/1921875000000000000000000000000 : ℝ)*base68 + (5398724624529397/960937500000000000000000000000 : ℝ)*base70 + (8992229729248147/960937500000000000000000000000 : ℝ)*base72 + (1652330153063/307500000000000000000000000 : ℝ)*base73 + (14913356822581831/1921875000000000000000000000000 : ℝ)*base75 + (429523881340307/240234375000000000000000000000 : ℝ)*base77 + (9911081599831831/1921875000000000000000000000000 : ℝ)*base79 + (2307880711199/615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13116417/10000000000000000000000 : ℝ)*base89 + (13116417/10000000000000000000000 : ℝ)*base91 + (13116417/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41791690601416411155964979/7687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (862087767/100000000000000 : ℝ)*(base19) + (466289231/50000000000000 : ℝ)*(base23) + (68927201/25000000000000 : ℝ)*(lower1) + (2361/2000000000 : ℝ)*(upper3) + (60713/200000000000 : ℝ)*(lower4) + (58101949/50000000000000 : ℝ)*(upper5) + (865357082344501/25000000000000 : ℝ)*(major0) + (865357082344501/25000000000000 : ℝ)*(major1) + (865357082344501/25000000000000 : ℝ)*(major2) + (100057891/10000000000000 : ℝ)*(sp2) + (4845946971492479/100000000000000 : ℝ)*(sp4) + (4845946109404713/100000000000000 : ℝ)*(sp5) + (1211486259583777/25000000000000 : ℝ)*(sp6) + (1038454753026467/50000000000000 : ℝ)*(sp7) + (1038454753026467/50000000000000 : ℝ)*(f.failure) + (4845946971492479/100000000000000 : ℝ)*(f.sum) + (2042451864113/1845000000000000000000000000 : ℝ)*base66 + (557386775664072521/46125000000000000000000000000000 : ℝ)*base67 + (668645751577947521/46125000000000000000000000000000 : ℝ)*base69 + (557517608390927479/46125000000000000000000000000000 : ℝ)*base72 + (6567051825967/1845000000000000000000000000 : ℝ)*base73 + (34205110023822521/46125000000000000000000000000000 : ℝ)*base75 + (290467598757072521/46125000000000000000000000000000 : ℝ)*base77 + (729989662712177479/46125000000000000000000000000000 : ℝ)*base80 + (2221767363701/922500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (35856449/5000000000000000000000 : ℝ)*base90 + (35856449/5000000000000000000000 : ℝ)*base92 + (35856449/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1553_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1553_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1553_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1553_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1553_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1553_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1553_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
