-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1686_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:34.629832+00:00
-- url     : https://prove2.me/submissions/ae8f5fa0-4048-4f92-bfa4-d8bb228549d4

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
theorem support_rectangle_w1686_s0_0 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35258667/250000000 : ℝ)*x 0 + (5748549661/10000000000 : ℝ)*x 1 + (2466547357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35258667/250000000 : ℝ)^5111 ≤ (4316771261533/50000000000000 : ℝ)^4087 := by
    have hnat : (35258667 : ℕ)^5111*50000000000000^4087 ≤ 4316771261533^4087*250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35258667 250000000 4316771261533 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5748549661/10000000000 : ℝ)^5111 ≤ (25019895665047/50000000000000 : ℝ)^4087 := by
    have hnat : (5748549661 : ℕ)^5111*50000000000000^4087 ≤ 25019895665047^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5748549661 10000000000 25019895665047 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2466547357/5000000000 : ℝ)^5111 ≤ (41326666124827/100000000000000 : ℝ)^4087 := by
    have hnat : (2466547357 : ℕ)^5111*100000000000000^4087 ≤ 41326666124827^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466547357 5000000000 41326666124827 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35258667/250000000 : ℝ), (5748549661/10000000000 : ℝ), (2466547357/5000000000 : ℝ)] ![(4316771261533/50000000000000 : ℝ), (25019895665047/50000000000000 : ℝ), (41326666124827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35258667/250000000 : ℝ)|^5111 ≤ (4316771261533/50000000000000 : ℝ)^4087
        have hw : |(-35258667/250000000 : ℝ)|=(35258667/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5748549661/10000000000 : ℝ)|^5111 ≤ (25019895665047/50000000000000 : ℝ)^4087
        have hw : |(5748549661/10000000000 : ℝ)|=(5748549661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2466547357/5000000000 : ℝ)|^5111 ≤ (41326666124827/100000000000000 : ℝ)^4087
        have hw : |(2466547357/5000000000 : ℝ)|=(2466547357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_1 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084309899/2000000000 : ℝ)*x 0 + (-1855587613/10000000000 : ℝ)*x 1 + (4933095851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084309899/2000000000 : ℝ)^5111 ≤ (9301176964451/20000000000000 : ℝ)^4087 := by
    have hnat : (1084309899 : ℕ)^5111*20000000000000^4087 ≤ 9301176964451^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084309899 2000000000 9301176964451 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1855587613/10000000000 : ℝ)^5111 ≤ (3041859282431/25000000000000 : ℝ)^4087 := by
    have hnat : (1855587613 : ℕ)^5111*25000000000000^4087 ≤ 3041859282431^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855587613 10000000000 3041859282431 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4933095851/10000000000 : ℝ)^5111 ≤ (41326678036497/100000000000000 : ℝ)^4087 := by
    have hnat : (4933095851 : ℕ)^5111*100000000000000^4087 ≤ 41326678036497^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933095851 10000000000 41326678036497 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084309899/2000000000 : ℝ), (-1855587613/10000000000 : ℝ), (4933095851/10000000000 : ℝ)] ![(9301176964451/20000000000000 : ℝ), (3041859282431/25000000000000 : ℝ), (41326678036497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084309899/2000000000 : ℝ)|^5111 ≤ (9301176964451/20000000000000 : ℝ)^4087
        have hw : |(1084309899/2000000000 : ℝ)|=(1084309899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1855587613/10000000000 : ℝ)|^5111 ≤ (3041859282431/25000000000000 : ℝ)^4087
        have hw : |(-1855587613/10000000000 : ℝ)|=(1855587613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4933095851/10000000000 : ℝ)|^5111 ≤ (41326678036497/100000000000000 : ℝ)^4087
        have hw : |(4933095851/10000000000 : ℝ)|=(4933095851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_2 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2710775759/5000000000 : ℝ)*x 0 + (4933094741/10000000000 : ℝ)*x 1 + (-115974149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710775759/5000000000 : ℝ)^5111 ≤ (46505906523349/100000000000000 : ℝ)^4087 := by
    have hnat : (2710775759 : ℕ)^5111*100000000000000^4087 ≤ 46505906523349^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710775759 5000000000 46505906523349 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4933094741/10000000000 : ℝ)^5111 ≤ (4132666640769/10000000000000 : ℝ)^4087 := by
    have hnat : (4933094741 : ℕ)^5111*10000000000000^4087 ≤ 4132666640769^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933094741 10000000000 4132666640769 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115974149/625000000 : ℝ)^5111 ≤ (380232095369/3125000000000 : ℝ)^4087 := by
    have hnat : (115974149 : ℕ)^5111*3125000000000^4087 ≤ 380232095369^4087*625000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115974149 625000000 380232095369 3125000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710775759/5000000000 : ℝ), (4933094741/10000000000 : ℝ), (-115974149/625000000 : ℝ)] ![(46505906523349/100000000000000 : ℝ), (4132666640769/10000000000000 : ℝ), (380232095369/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710775759/5000000000 : ℝ)|^5111 ≤ (46505906523349/100000000000000 : ℝ)^4087
        have hw : |(2710775759/5000000000 : ℝ)|=(2710775759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4933094741/10000000000 : ℝ)|^5111 ≤ (4132666640769/10000000000000 : ℝ)^4087
        have hw : |(4933094741/10000000000 : ℝ)|=(4933094741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115974149/625000000 : ℝ)|^5111 ≤ (380232095369/3125000000000 : ℝ)^4087
        have hw : |(-115974149/625000000 : ℝ)|=(115974149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_3 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (507515859/1250000000 : ℝ)*x 0 + (609071999/2000000000 : ℝ)*x 1 + (5280550061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507515859/1250000000 : ℝ)^5111 ≤ (3239358371101/10000000000000 : ℝ)^4087 := by
    have hnat : (507515859 : ℕ)^5111*10000000000000^4087 ≤ 3239358371101^4087*1250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507515859 1250000000 3239358371101 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609071999/2000000000 : ℝ)^5111 ≤ (11304049013893/50000000000000 : ℝ)^4087 := by
    have hnat : (609071999 : ℕ)^5111*50000000000000^4087 ≤ 11304049013893^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609071999 2000000000 11304049013893 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280550061/10000000000 : ℝ)^5111 ≤ (5624789781059/12500000000000 : ℝ)^4087 := by
    have hnat : (5280550061 : ℕ)^5111*12500000000000^4087 ≤ 5624789781059^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280550061 10000000000 5624789781059 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(507515859/1250000000 : ℝ), (609071999/2000000000 : ℝ), (5280550061/10000000000 : ℝ)] ![(3239358371101/10000000000000 : ℝ), (11304049013893/50000000000000 : ℝ), (5624789781059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(507515859/1250000000 : ℝ)|^5111 ≤ (3239358371101/10000000000000 : ℝ)^4087
        have hw : |(507515859/1250000000 : ℝ)|=(507515859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(609071999/2000000000 : ℝ)|^5111 ≤ (11304049013893/50000000000000 : ℝ)^4087
        have hw : |(609071999/2000000000 : ℝ)|=(609071999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280550061/10000000000 : ℝ)|^5111 ≤ (5624789781059/12500000000000 : ℝ)^4087
        have hw : |(5280550061/10000000000 : ℝ)|=(5280550061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_4 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35310829/250000000 : ℝ)*x 0 + (1238411889/2500000000 : ℝ)*x 1 + (2863640969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35310829/250000000 : ℝ)^5111 ≤ (540594887049/6250000000000 : ℝ)^4087 := by
    have hnat : (35310829 : ℕ)^5111*6250000000000^4087 ≤ 540594887049^4087*250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35310829 250000000 540594887049 6250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238411889/2500000000 : ℝ)^5111 ≤ (41542098229469/100000000000000 : ℝ)^4087 := by
    have hnat : (1238411889 : ℕ)^5111*100000000000000^4087 ≤ 41542098229469^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238411889 2500000000 41542098229469 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2863640969/5000000000 : ℝ)^5111 ≤ (49808383567971/100000000000000 : ℝ)^4087 := by
    have hnat : (2863640969 : ℕ)^5111*100000000000000^4087 ≤ 49808383567971^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2863640969 5000000000 49808383567971 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35310829/250000000 : ℝ), (1238411889/2500000000 : ℝ), (2863640969/5000000000 : ℝ)] ![(540594887049/6250000000000 : ℝ), (41542098229469/100000000000000 : ℝ), (49808383567971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35310829/250000000 : ℝ)|^5111 ≤ (540594887049/6250000000000 : ℝ)^4087
        have hw : |(-35310829/250000000 : ℝ)|=(35310829/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1238411889/2500000000 : ℝ)|^5111 ≤ (41542098229469/100000000000000 : ℝ)^4087
        have hw : |(1238411889/2500000000 : ℝ)|=(1238411889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2863640969/5000000000 : ℝ)|^5111 ≤ (49808383567971/100000000000000 : ℝ)^4087
        have hw : |(2863640969/5000000000 : ℝ)|=(2863640969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_5 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599963963/5000000000 : ℝ)*x 0 + (-21228017/200000000 : ℝ)*x 1 + (5727282201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599963963/5000000000 : ℝ)^5111 ≤ (11035202649807/25000000000000 : ℝ)^4087 := by
    have hnat : (2599963963 : ℕ)^5111*25000000000000^4087 ≤ 11035202649807^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599963963 5000000000 11035202649807 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21228017/200000000 : ℝ)^5111 ≤ (1512700737999/25000000000000 : ℝ)^4087 := by
    have hnat : (21228017 : ℕ)^5111*25000000000000^4087 ≤ 1512700737999^4087*200000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21228017 200000000 1512700737999 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5727282201/10000000000 : ℝ)^5111 ≤ (24904193214133/50000000000000 : ℝ)^4087 := by
    have hnat : (5727282201 : ℕ)^5111*50000000000000^4087 ≤ 24904193214133^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5727282201 10000000000 24904193214133 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599963963/5000000000 : ℝ), (-21228017/200000000 : ℝ), (5727282201/10000000000 : ℝ)] ![(11035202649807/25000000000000 : ℝ), (1512700737999/25000000000000 : ℝ), (24904193214133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599963963/5000000000 : ℝ)|^5111 ≤ (11035202649807/25000000000000 : ℝ)^4087
        have hw : |(2599963963/5000000000 : ℝ)|=(2599963963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21228017/200000000 : ℝ)|^5111 ≤ (1512700737999/25000000000000 : ℝ)^4087
        have hw : |(-21228017/200000000 : ℝ)|=(21228017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5727282201/10000000000 : ℝ)|^5111 ≤ (24904193214133/50000000000000 : ℝ)^4087
        have hw : |(5727282201/10000000000 : ℝ)|=(5727282201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_6 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599963993/5000000000 : ℝ)*x 0 + (1145456443/2000000000 : ℝ)*x 1 + (-53070037/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599963993/5000000000 : ℝ)^5111 ≤ (44140811236163/100000000000000 : ℝ)^4087 := by
    have hnat : (2599963993 : ℕ)^5111*100000000000000^4087 ≤ 44140811236163^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599963993 5000000000 44140811236163 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145456443/2000000000 : ℝ)^5111 ≤ (1992335463221/4000000000000 : ℝ)^4087 := by
    have hnat : (1145456443 : ℕ)^5111*4000000000000^4087 ≤ 1992335463221^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145456443 2000000000 1992335463221 4000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53070037/500000000 : ℝ)^5111 ≤ (1210160433559/20000000000000 : ℝ)^4087 := by
    have hnat : (53070037 : ℕ)^5111*20000000000000^4087 ≤ 1210160433559^4087*500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53070037 500000000 1210160433559 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599963993/5000000000 : ℝ), (1145456443/2000000000 : ℝ), (-53070037/500000000 : ℝ)] ![(44140811236163/100000000000000 : ℝ), (1992335463221/4000000000000 : ℝ), (1210160433559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599963993/5000000000 : ℝ)|^5111 ≤ (44140811236163/100000000000000 : ℝ)^4087
        have hw : |(2599963993/5000000000 : ℝ)|=(2599963993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145456443/2000000000 : ℝ)|^5111 ≤ (1992335463221/4000000000000 : ℝ)^4087
        have hw : |(1145456443/2000000000 : ℝ)|=(1145456443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53070037/500000000 : ℝ)|^5111 ≤ (1210160433559/20000000000000 : ℝ)^4087
        have hw : |(-53070037/500000000 : ℝ)|=(53070037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s0_7 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2032922811/5000000000 : ℝ)*x 0 + (5224213117/10000000000 : ℝ)*x 1 + (3103654427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032922811/5000000000 : ℝ)^5111 ≤ (8112663114761/25000000000000 : ℝ)^4087 := by
    have hnat : (2032922811 : ℕ)^5111*25000000000000^4087 ≤ 8112663114761^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032922811 5000000000 8112663114761 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224213117/10000000000 : ℝ)^5111 ≤ (44398762938437/100000000000000 : ℝ)^4087 := by
    have hnat : (5224213117 : ℕ)^5111*100000000000000^4087 ≤ 44398762938437^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224213117 10000000000 44398762938437 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3103654427/10000000000 : ℝ)^5111 ≤ (180863942089/781250000000 : ℝ)^4087 := by
    have hnat : (3103654427 : ℕ)^5111*781250000000^4087 ≤ 180863942089^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103654427 10000000000 180863942089 781250000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2032922811/5000000000 : ℝ), (5224213117/10000000000 : ℝ), (3103654427/10000000000 : ℝ)] ![(8112663114761/25000000000000 : ℝ), (44398762938437/100000000000000 : ℝ), (180863942089/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2032922811/5000000000 : ℝ)|^5111 ≤ (8112663114761/25000000000000 : ℝ)^4087
        have hw : |(2032922811/5000000000 : ℝ)|=(2032922811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224213117/10000000000 : ℝ)|^5111 ≤ (44398762938437/100000000000000 : ℝ)^4087
        have hw : |(5224213117/10000000000 : ℝ)|=(5224213117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3103654427/10000000000 : ℝ)|^5111 ≤ (180863942089/781250000000 : ℝ)^4087
        have hw : |(3103654427/10000000000 : ℝ)|=(3103654427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1686_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2849/12500 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5103/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5103 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5103*1^1024 ≤ 0^1024*1^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5103/1024 : ℝ) ≤ (1039696022602931581/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5103 ≤ (1039696022602931581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5103*100000000000000000000^1024 ≤ 1039696022602931581^1024*5^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1039696022602931581 100000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1039696022602931581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5103 := by
      have hnat : (1 : ℕ)^1024*1^5103 ≤ 1^5103*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101039696022602931581/100000000000000000000 : ℝ) ≤ (10020777036224601/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (101039696022602931581/100000000000000000000 : ℝ)^1024 ≤ (10020777036224601/10000000000000000 : ℝ)^5103 := by
      have hnat : (101039696022602931581 : ℕ)^1024*10000000000000000^5103 ≤ 10020777036224601^5103*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101039696022602931581 100000000000000000000 10020777036224601 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020777036224601/10000000000000000 : ℝ)) (X := (101039696022602931581/100000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51039696022602931581/50000000000000000000 : ℝ) ≤ (5020777036224601/5000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (51039696022602931581/50000000000000000000 : ℝ)^1024 ≤ (5020777036224601/5000000000000000 : ℝ)^5103 := by
      have hnat : (51039696022602931581 : ℕ)^1024*5000000000000000^5103 ≤ 5020777036224601^5103*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51039696022602931581 50000000000000000000 5020777036224601 5000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020777036224601/5000000000000000 : ℝ)) (X := (51039696022602931581/50000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(20777036224601/4000000000000000 : ℝ)*(0 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20777036224601/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1039696022602931581/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(20777036224601/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5103/1024 : ℝ) := by
    rw [show (1 : ℝ)+(20777036224601/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10020777036224601/10000000000000000 : ℝ) by norm_num, show 1+(1039696022602931581/100000000000000000000 : ℝ)+(0 : ℝ)=(101039696022602931581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1039696022602931581/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(20777036224601/4000000000000000 : ℝ)*(2/5 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20777036224601/4000000000000000 : ℝ)*(2/5 : ℝ)=(5020777036224601/5000000000000000 : ℝ) by norm_num, show 1+2*(1039696022602931581/100000000000000000000 : ℝ)=(51039696022602931581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(20777036224601/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20777036224601/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(20777036224601/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20777036224601/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(20777036224601/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20777036224601/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-35258667/250000000 : ℝ)*X 0 0+(5748549661/10000000000 : ℝ)*X 0 1+(2466547357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1084309899/2000000000 : ℝ)*X 1 0+(-1855587613/10000000000 : ℝ)*X 1 1+(4933095851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710775759/5000000000 : ℝ)*X 2 0+(4933094741/10000000000 : ℝ)*X 2 1+(-115974149/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((507515859/1250000000 : ℝ)*X 0 0+(609071999/2000000000 : ℝ)*X 0 1+(5280550061/10000000000 : ℝ)*X 0 2+(507515859/1250000000 : ℝ)*X 1 0+(609071999/2000000000 : ℝ)*X 1 1+(5280550061/10000000000 : ℝ)*X 1 2+(507515859/1250000000 : ℝ)*X 2 0+(609071999/2000000000 : ℝ)*X 2 1+(5280550061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-35310829/250000000 : ℝ)*X 0 0+(1238411889/2500000000 : ℝ)*X 0 1+(2863640969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599963963/5000000000 : ℝ)*X 1 0+(-21228017/200000000 : ℝ)*X 1 1+(5727282201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599963993/5000000000 : ℝ)*X 2 0+(1145456443/2000000000 : ℝ)*X 2 1+(-53070037/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2032922811/5000000000 : ℝ)*X 0 0+(5224213117/10000000000 : ℝ)*X 0 1+(3103654427/10000000000 : ℝ)*X 0 2+(2032922811/5000000000 : ℝ)*X 1 0+(5224213117/10000000000 : ℝ)*X 1 1+(3103654427/10000000000 : ℝ)*X 1 2+(2032922811/5000000000 : ℝ)*X 2 0+(5224213117/10000000000 : ℝ)*X 2 1+(3103654427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (340702819980649469705949/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5924719/50000000000000 : ℝ)*(base1) + (221712491/50000000000000 : ℝ)*(base19) + (762939699/100000000000000 : ℝ)*(base23) + (138073351/100000000000000 : ℝ)*(base24) + (92019027/100000000000000 : ℝ)*(upper5) + (836854266099939/100000000000000 : ℝ)*(major0) + (836854266099939/100000000000000 : ℝ)*(major1) + (836854266099939/100000000000000 : ℝ)*(major2) + (153288993776281/12500000000000 : ℝ)*(sp0) + (1226316006037463/100000000000000 : ℝ)*(sp1) + (306578887112349/25000000000000 : ℝ)*(sp2) + (223695276837847/50000000000000 : ℝ)*(sp3) + (1127775409/25000000000000 : ℝ)*(sp4) + (350911171/25000000000000 : ℝ)*(sp7) + (55923996146227/12500000000000 : ℝ)*(f.failure) + (613158224731223/50000000000000 : ℝ)*(f.sum) + (420781873199339/200000000000000000000000000000 : ℝ)*base65 + (1305337475599339/400000000000000000000000000000 : ℝ)*base67 + (277215899599339/400000000000000000000000000000 : ℝ)*base69 + (1778679595999339/400000000000000000000000000000 : ℝ)*base71 + (534253968599339/200000000000000000000000000000 : ℝ)*base73 + (2783861350399339/400000000000000000000000000000 : ℝ)*base75 + (1398178818799339/400000000000000000000000000000 : ℝ)*base77 + (483697918799339/400000000000000000000000000000 : ℝ)*base79 + (1191839248799339/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (821813/78125000000000000000 : ℝ)*base90 + (821813/78125000000000000000 : ℝ)*base92 + (821813/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1117430318874570881676183/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (291556399/25000000000000 : ℝ)*(base19) + (149482249/12500000000000 : ℝ)*(base23) + (691551/100000000000000 : ℝ)*(upper2) + (205203881/100000000000000 : ℝ)*(upper3) + (174655159/100000000000000 : ℝ)*(upper5) + (882087064351461/100000000000000 : ℝ)*(major0) + (882087064351461/100000000000000 : ℝ)*(major1) + (882087064351461/100000000000000 : ℝ)*(major2) + (4118514319/100000000000000 : ℝ)*(sp1) + (138518471/3125000000000 : ℝ)*(sp2) + (1292599996216291/100000000000000 : ℝ)*(sp4) + (10340757691811/800000000000 : ℝ)*(sp5) + (1292594367767227/100000000000000 : ℝ)*(sp6) + (5894674328103/1250000000000 : ℝ)*(sp7) + (5894674328103/1250000000000 : ℝ)*(f.failure) + (1292599996216291/100000000000000 : ℝ)*(f.sum) + (939129145507939/200000000000000000000000000000 : ℝ)*base66 + (2456310448092061/400000000000000000000000000000 : ℝ)*base67 + (102454176707939/400000000000000000000000000000 : ℝ)*base70 + (1736321024492061/400000000000000000000000000000 : ℝ)*base71 + (714752958107939/200000000000000000000000000000 : ℝ)*base74 + (3686809868892061/400000000000000000000000000000 : ℝ)*base75 + (252603039292061/400000000000000000000000000000 : ℝ)*base77 + (222636303692061/400000000000000000000000000000 : ℝ)*base79 + (579059371907939/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5667/1953125000000000000 : ℝ)*base89 + (5667/1953125000000000000 : ℝ)*base91 + (5667/1953125000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1686_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2849/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1686_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1686_s1_0 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1497635731/10000000000 : ℝ)*x 0 + (5510258863/10000000000 : ℝ)*x 1 + (204571983/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1497635731/10000000000 : ℝ)^5111 ≤ (4653436427873/50000000000000 : ℝ)^4087 := by
    have hnat : (1497635731 : ℕ)^5111*50000000000000^4087 ≤ 4653436427873^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497635731 10000000000 4653436427873 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510258863/10000000000 : ℝ)^5111 ≤ (47459429206949/100000000000000 : ℝ)^4087 := by
    have hnat : (5510258863 : ℕ)^5111*100000000000000^4087 ≤ 47459429206949^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510258863 10000000000 47459429206949 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204571983/400000000 : ℝ)^5111 ≤ (10808424480107/25000000000000 : ℝ)^4087 := by
    have hnat : (204571983 : ℕ)^5111*25000000000000^4087 ≤ 10808424480107^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204571983 400000000 10808424480107 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1497635731/10000000000 : ℝ), (5510258863/10000000000 : ℝ), (204571983/400000000 : ℝ)] ![(4653436427873/50000000000000 : ℝ), (47459429206949/100000000000000 : ℝ), (10808424480107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1497635731/10000000000 : ℝ)|^5111 ≤ (4653436427873/50000000000000 : ℝ)^4087
        have hw : |(-1497635731/10000000000 : ℝ)|=(1497635731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510258863/10000000000 : ℝ)|^5111 ≤ (47459429206949/100000000000000 : ℝ)^4087
        have hw : |(5510258863/10000000000 : ℝ)|=(5510258863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204571983/400000000 : ℝ)|^5111 ≤ (10808424480107/25000000000000 : ℝ)^4087
        have hw : |(204571983/400000000 : ℝ)|=(204571983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_1 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214322573/400000000 : ℝ)*x 0 + (-1704378659/10000000000 : ℝ)*x 1 + (639287423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214322573/400000000 : ℝ)^5111 ≤ (5728233709807/12500000000000 : ℝ)^4087 := by
    have hnat : (214322573 : ℕ)^5111*12500000000000^4087 ≤ 5728233709807^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214322573 400000000 5728233709807 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1704378659/10000000000 : ℝ)^5111 ≤ (5470217203229/50000000000000 : ℝ)^4087 := by
    have hnat : (1704378659 : ℕ)^5111*50000000000000^4087 ≤ 5470217203229^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704378659 10000000000 5470217203229 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639287423/1250000000 : ℝ)^5111 ≤ (10808423975317/25000000000000 : ℝ)^4087 := by
    have hnat : (639287423 : ℕ)^5111*25000000000000^4087 ≤ 10808423975317^4087*1250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639287423 1250000000 10808423975317 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214322573/400000000 : ℝ), (-1704378659/10000000000 : ℝ), (639287423/1250000000 : ℝ)] ![(5728233709807/12500000000000 : ℝ), (5470217203229/50000000000000 : ℝ), (10808423975317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214322573/400000000 : ℝ)|^5111 ≤ (5728233709807/12500000000000 : ℝ)^4087
        have hw : |(214322573/400000000 : ℝ)|=(214322573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1704378659/10000000000 : ℝ)|^5111 ≤ (5470217203229/50000000000000 : ℝ)^4087
        have hw : |(-1704378659/10000000000 : ℝ)|=(1704378659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639287423/1250000000 : ℝ)|^5111 ≤ (10808423975317/25000000000000 : ℝ)^4087
        have hw : |(639287423/1250000000 : ℝ)|=(639287423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_2 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358063659/10000000000 : ℝ)*x 0 + (2557149987/5000000000 : ℝ)*x 1 + (-1704378769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358063659/10000000000 : ℝ)^5111 ≤ (11456465638801/25000000000000 : ℝ)^4087 := by
    have hnat : (5358063659 : ℕ)^5111*25000000000000^4087 ≤ 11456465638801^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358063659 10000000000 11456465638801 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2557149987/5000000000 : ℝ)^5111 ≤ (8646740427693/20000000000000 : ℝ)^4087 := by
    have hnat : (2557149987 : ℕ)^5111*20000000000000^4087 ≤ 8646740427693^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557149987 5000000000 8646740427693 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704378769/10000000000 : ℝ)^5111 ≤ (5470217644731/50000000000000 : ℝ)^4087 := by
    have hnat : (1704378769 : ℕ)^5111*50000000000000^4087 ≤ 5470217644731^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704378769 10000000000 5470217644731 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358063659/10000000000 : ℝ), (2557149987/5000000000 : ℝ), (-1704378769/10000000000 : ℝ)] ![(11456465638801/25000000000000 : ℝ), (8646740427693/20000000000000 : ℝ), (5470217644731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358063659/10000000000 : ℝ)|^5111 ≤ (11456465638801/25000000000000 : ℝ)^4087
        have hw : |(5358063659/10000000000 : ℝ)|=(5358063659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2557149987/5000000000 : ℝ)|^5111 ≤ (8646740427693/20000000000000 : ℝ)^4087
        have hw : |(2557149987/5000000000 : ℝ)|=(2557149987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1704378769/10000000000 : ℝ)|^5111 ≤ (5470217644731/50000000000000 : ℝ)^4087
        have hw : |(-1704378769/10000000000 : ℝ)|=(1704378769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_3 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (258255907/625000000 : ℝ)*x 0 + (3613447269/10000000000 : ℝ)*x 1 + (4698784891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258255907/625000000 : ℝ)^5111 ≤ (4139153312337/12500000000000 : ℝ)^4087 := by
    have hnat : (258255907 : ℕ)^5111*12500000000000^4087 ≤ 4139153312337^4087*625000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258255907 625000000 4139153312337 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3613447269/10000000000 : ℝ)^5111 ≤ (7000012005609/25000000000000 : ℝ)^4087 := by
    have hnat : (3613447269 : ℕ)^5111*25000000000000^4087 ≤ 7000012005609^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613447269 10000000000 7000012005609 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4698784891/10000000000 : ℝ)^5111 ≤ (7777345092349/20000000000000 : ℝ)^4087 := by
    have hnat : (4698784891 : ℕ)^5111*20000000000000^4087 ≤ 7777345092349^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698784891 10000000000 7777345092349 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258255907/625000000 : ℝ), (3613447269/10000000000 : ℝ), (4698784891/10000000000 : ℝ)] ![(4139153312337/12500000000000 : ℝ), (7000012005609/25000000000000 : ℝ), (7777345092349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258255907/625000000 : ℝ)|^5111 ≤ (4139153312337/12500000000000 : ℝ)^4087
        have hw : |(258255907/625000000 : ℝ)|=(258255907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3613447269/10000000000 : ℝ)|^5111 ≤ (7000012005609/25000000000000 : ℝ)^4087
        have hw : |(3613447269/10000000000 : ℝ)|=(3613447269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4698784891/10000000000 : ℝ)|^5111 ≤ (7777345092349/20000000000000 : ℝ)^4087
        have hw : |(4698784891/10000000000 : ℝ)|=(4698784891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_4 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-299574201/2000000000 : ℝ)*x 0 + (5119133743/10000000000 : ℝ)*x 1 + (5505343309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299574201/2000000000 : ℝ)^5111 ≤ (4654350649137/50000000000000 : ℝ)^4087 := by
    have hnat : (299574201 : ℕ)^5111*50000000000000^4087 ≤ 4654350649137^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299574201 2000000000 4654350649137 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5119133743/10000000000 : ℝ)^5111 ≤ (43284808477401/100000000000000 : ℝ)^4087 := by
    have hnat : (5119133743 : ℕ)^5111*100000000000000^4087 ≤ 43284808477401^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119133743 10000000000 43284808477401 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505343309/10000000000 : ℝ)^5111 ≤ (23703245106997/50000000000000 : ℝ)^4087 := by
    have hnat : (5505343309 : ℕ)^5111*50000000000000^4087 ≤ 23703245106997^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505343309 10000000000 23703245106997 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-299574201/2000000000 : ℝ), (5119133743/10000000000 : ℝ), (5505343309/10000000000 : ℝ)] ![(4654350649137/50000000000000 : ℝ), (43284808477401/100000000000000 : ℝ), (23703245106997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-299574201/2000000000 : ℝ)|^5111 ≤ (4654350649137/50000000000000 : ℝ)^4087
        have hw : |(-299574201/2000000000 : ℝ)|=(299574201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5119133743/10000000000 : ℝ)|^5111 ≤ (43284808477401/100000000000000 : ℝ)^4087
        have hw : |(5119133743/10000000000 : ℝ)|=(5119133743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505343309/10000000000 : ℝ)|^5111 ≤ (23703245106997/50000000000000 : ℝ)^4087
        have hw : |(5505343309/10000000000 : ℝ)|=(5505343309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_5 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252172121/10000000000 : ℝ)*x 0 + (-656667541/5000000000 : ℝ)*x 1 + (5505343393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252172121/10000000000 : ℝ)^5111 ≤ (44696109972427/100000000000000 : ℝ)^4087 := by
    have hnat : (5252172121 : ℕ)^5111*100000000000000^4087 ≤ 44696109972427^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252172121 10000000000 44696109972427 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656667541/5000000000 : ℝ)^5111 ≤ (7897398891771/100000000000000 : ℝ)^4087 := by
    have hnat : (656667541 : ℕ)^5111*100000000000000^4087 ≤ 7897398891771^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656667541 5000000000 7897398891771 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505343393/10000000000 : ℝ)^5111 ≤ (47406491118547/100000000000000 : ℝ)^4087 := by
    have hnat : (5505343393 : ℕ)^5111*100000000000000^4087 ≤ 47406491118547^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505343393 10000000000 47406491118547 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252172121/10000000000 : ℝ), (-656667541/5000000000 : ℝ), (5505343393/10000000000 : ℝ)] ![(44696109972427/100000000000000 : ℝ), (7897398891771/100000000000000 : ℝ), (47406491118547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252172121/10000000000 : ℝ)|^5111 ≤ (44696109972427/100000000000000 : ℝ)^4087
        have hw : |(5252172121/10000000000 : ℝ)|=(5252172121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-656667541/5000000000 : ℝ)|^5111 ≤ (7897398891771/100000000000000 : ℝ)^4087
        have hw : |(-656667541/5000000000 : ℝ)|=(656667541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505343393/10000000000 : ℝ)|^5111 ≤ (47406491118547/100000000000000 : ℝ)^4087
        have hw : |(5505343393/10000000000 : ℝ)|=(5505343393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_6 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252172273/10000000000 : ℝ)*x 0 + (5505343189/10000000000 : ℝ)*x 1 + (-1313335159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252172273/10000000000 : ℝ)^5111 ≤ (11174027897511/25000000000000 : ℝ)^4087 := by
    have hnat : (5252172273 : ℕ)^5111*25000000000000^4087 ≤ 11174027897511^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252172273 10000000000 11174027897511 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505343189/10000000000 : ℝ)^5111 ≤ (2962905557611/6250000000000 : ℝ)^4087 := by
    have hnat : (5505343189 : ℕ)^5111*6250000000000^4087 ≤ 2962905557611^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505343189 10000000000 2962905557611 6250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313335159/10000000000 : ℝ)^5111 ≤ (19743498677/250000000000 : ℝ)^4087 := by
    have hnat : (1313335159 : ℕ)^5111*250000000000^4087 ≤ 19743498677^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313335159 10000000000 19743498677 250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252172273/10000000000 : ℝ), (5505343189/10000000000 : ℝ), (-1313335159/10000000000 : ℝ)] ![(11174027897511/25000000000000 : ℝ), (2962905557611/6250000000000 : ℝ), (19743498677/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252172273/10000000000 : ℝ)|^5111 ≤ (11174027897511/25000000000000 : ℝ)^4087
        have hw : |(5252172273/10000000000 : ℝ)|=(5252172273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505343189/10000000000 : ℝ)|^5111 ≤ (2962905557611/6250000000000 : ℝ)^4087
        have hw : |(5505343189/10000000000 : ℝ)|=(5505343189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1313335159/10000000000 : ℝ)|^5111 ≤ (19743498677/250000000000 : ℝ)^4087
        have hw : |(-1313335159/10000000000 : ℝ)|=(1313335159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s1_7 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2066370241/5000000000 : ℝ)*x 0 + (4685533331/10000000000 : ℝ)*x 1 + (3626920829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066370241/5000000000 : ℝ)^5111 ≤ (6623940042067/20000000000000 : ℝ)^4087 := by
    have hnat : (2066370241 : ℕ)^5111*20000000000000^4087 ≤ 6623940042067^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066370241 5000000000 6623940042067 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4685533331/10000000000 : ℝ)^5111 ≤ (4843703457621/12500000000000 : ℝ)^4087 := by
    have hnat : (4685533331 : ℕ)^5111*12500000000000^4087 ≤ 4843703457621^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4685533331 10000000000 4843703457621 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3626920829/10000000000 : ℝ)^5111 ≤ (2813067211583/10000000000000 : ℝ)^4087 := by
    have hnat : (3626920829 : ℕ)^5111*10000000000000^4087 ≤ 2813067211583^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3626920829 10000000000 2813067211583 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066370241/5000000000 : ℝ), (4685533331/10000000000 : ℝ), (3626920829/10000000000 : ℝ)] ![(6623940042067/20000000000000 : ℝ), (4843703457621/12500000000000 : ℝ), (2813067211583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066370241/5000000000 : ℝ)|^5111 ≤ (6623940042067/20000000000000 : ℝ)^4087
        have hw : |(2066370241/5000000000 : ℝ)|=(2066370241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4685533331/10000000000 : ℝ)|^5111 ≤ (4843703457621/12500000000000 : ℝ)^4087
        have hw : |(4685533331/10000000000 : ℝ)|=(4685533331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3626920829/10000000000 : ℝ)|^5111 ≤ (2813067211583/10000000000000 : ℝ)^4087
        have hw : |(3626920829/10000000000 : ℝ)|=(3626920829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1686_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4443/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5299/100000 : ℝ) ^ (5103/1024 : ℝ) ≤ (21934107937163/50000000000000000000 : ℝ) := by
    have hpowers : (5299/100000 : ℝ)^5103 ≤ (21934107937163/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5299 : ℕ)^5103*50000000000000000000^1024 ≤ 21934107937163^1024*100000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5299 100000 21934107937163 50000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5299/100000 : ℝ)) (X := (21934107937163/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2849/12500 : ℝ) ^ (5103/1024 : ℝ) ≤ (63033873553306037/100000000000000000000 : ℝ) := by
    have hpowers : (2849/12500 : ℝ)^5103 ≤ (63033873553306037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2849 : ℕ)^5103*100000000000000000000^1024 ≤ 63033873553306037^1024*12500^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 12500 63033873553306037 100000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/12500 : ℝ)) (X := (63033873553306037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000021934107937163/25000000000000000000 : ℝ) ≤ (400000070422947/400000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (25000021934107937163/25000000000000000000 : ℝ)^1024 ≤ (400000070422947/400000000000000 : ℝ)^5103 := by
      have hnat : (25000021934107937163 : ℕ)^1024*400000000000000^5103 ≤ 400000070422947^5103*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000021934107937163 25000000000000000000 400000070422947 400000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000070422947/400000000000000 : ℝ)) (X := (25000021934107937163/25000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100063077741769180363/100000000000000000000 : ℝ) ≤ (5000632719284063/5000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (100063077741769180363/100000000000000000000 : ℝ)^1024 ≤ (5000632719284063/5000000000000000 : ℝ)^5103 := by
      have hnat : (100063077741769180363 : ℕ)^1024*5000000000000000^5103 ≤ 5000632719284063^5103*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100063077741769180363 100000000000000000000 5000632719284063 5000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000632719284063/5000000000000000 : ℝ)) (X := (100063077741769180363/100000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063033873553306037/50000000000000000000 : ℝ) ≤ (10002529116562577/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (50063033873553306037/50000000000000000000 : ℝ)^1024 ≤ (10002529116562577/10000000000000000 : ℝ)^5103 := by
      have hnat : (50063033873553306037 : ℕ)^1024*10000000000000000^5103 ≤ 10002529116562577^5103*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063033873553306037 50000000000000000000 10002529116562577 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002529116562577/10000000000000000 : ℝ)) (X := (50063033873553306037/50000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21934107937163/50000000000000000000 : ℝ) ≤ ((24988091191190015011/24990000000000000000 : ℝ)+2*(1263677994451/1749300000000000 : ℝ)*(5299/100000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (24988091191190015011/24990000000000000000 : ℝ)+2*(1263677994451/1749300000000000 : ℝ)*(5299/100000 : ℝ)=(400000070422947/400000000000000 : ℝ) by norm_num, show 1+2*(21934107937163/50000000000000000000 : ℝ)=(25000021934107937163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63033873553306037/100000000000000000000 : ℝ)+(21934107937163/50000000000000000000 : ℝ) ≤ ((24988091191190015011/24990000000000000000 : ℝ)+(1263677994451/1749300000000000 : ℝ)*((2849/12500 : ℝ)+(5299/100000 : ℝ)))^(5103/1024 : ℝ) := by
    rw [show (24988091191190015011/24990000000000000000 : ℝ)+(1263677994451/1749300000000000 : ℝ)*((2849/12500 : ℝ)+(5299/100000 : ℝ))=(5000632719284063/5000000000000000 : ℝ) by norm_num, show 1+(63033873553306037/100000000000000000000 : ℝ)+(21934107937163/50000000000000000000 : ℝ)=(100063077741769180363/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63033873553306037/100000000000000000000 : ℝ) ≤ ((24988091191190015011/24990000000000000000 : ℝ)+2*(1263677994451/1749300000000000 : ℝ)*(2849/12500 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (24988091191190015011/24990000000000000000 : ℝ)+2*(1263677994451/1749300000000000 : ℝ)*(2849/12500 : ℝ)=(10002529116562577/10000000000000000 : ℝ) by norm_num, show 1+2*(63033873553306037/100000000000000000000 : ℝ)=(50063033873553306037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24988091191190015011/24990000000000000000 : ℝ)*(X 1 0+X 2 0)+(1263677994451/1749300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (5299/100000 : ℝ)) (hi := (2849/12500 : ℝ)) (c := (24988091191190015011/24990000000000000000 : ℝ)) (alpha := (1263677994451/1749300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24988091191190015011/24990000000000000000 : ℝ)*(X 0 1+X 2 1)+(1263677994451/1749300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (5299/100000 : ℝ)) (hi := (2849/12500 : ℝ)) (c := (24988091191190015011/24990000000000000000 : ℝ)) (alpha := (1263677994451/1749300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24988091191190015011/24990000000000000000 : ℝ)*(X 0 2+X 1 2)+(1263677994451/1749300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (5299/100000 : ℝ)) (hi := (2849/12500 : ℝ)) (c := (24988091191190015011/24990000000000000000 : ℝ)) (alpha := (1263677994451/1749300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1497635731/10000000000 : ℝ)*X 0 0+(5510258863/10000000000 : ℝ)*X 0 1+(204571983/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214322573/400000000 : ℝ)*X 1 0+(-1704378659/10000000000 : ℝ)*X 1 1+(639287423/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358063659/10000000000 : ℝ)*X 2 0+(2557149987/5000000000 : ℝ)*X 2 1+(-1704378769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((258255907/625000000 : ℝ)*X 0 0+(3613447269/10000000000 : ℝ)*X 0 1+(4698784891/10000000000 : ℝ)*X 0 2+(258255907/625000000 : ℝ)*X 1 0+(3613447269/10000000000 : ℝ)*X 1 1+(4698784891/10000000000 : ℝ)*X 1 2+(258255907/625000000 : ℝ)*X 2 0+(3613447269/10000000000 : ℝ)*X 2 1+(4698784891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-299574201/2000000000 : ℝ)*X 0 0+(5119133743/10000000000 : ℝ)*X 0 1+(5505343309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252172121/10000000000 : ℝ)*X 1 0+(-656667541/5000000000 : ℝ)*X 1 1+(5505343393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252172273/10000000000 : ℝ)*X 2 0+(5505343189/10000000000 : ℝ)*X 2 1+(-1313335159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2066370241/5000000000 : ℝ)*X 0 0+(4685533331/10000000000 : ℝ)*X 0 1+(3626920829/10000000000 : ℝ)*X 0 2+(2066370241/5000000000 : ℝ)*X 1 0+(4685533331/10000000000 : ℝ)*X 1 1+(3626920829/10000000000 : ℝ)*X 1 2+(2066370241/5000000000 : ℝ)*X 2 0+(4685533331/10000000000 : ℝ)*X 2 1+(3626920829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27454500039141909629752636407/2915500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1441969859/100000000000000 : ℝ)*(base19) + (547201337/50000000000000 : ℝ)*(base23) + (61690163/25000000000000 : ℝ)*(upper3) + (18028127/100000000000000 : ℝ)*(upper4) + (2248577/2000000000000 : ℝ)*(upper5) + (1723458419610903/100000000000000 : ℝ)*(major0) + (1723458419610903/100000000000000 : ℝ)*(major1) + (1723458419610903/100000000000000 : ℝ)*(major2) + (2525525249705817/100000000000000 : ℝ)*(sp0) + (2525534279836223/100000000000000 : ℝ)*(sp1) + (157845914212713/6250000000000 : ℝ)*(sp2) + (28793008383183/3125000000000 : ℝ)*(sp3) + (2094420053/20000000000000 : ℝ)*(sp4) + (4535262589/100000000000000 : ℝ)*(sp7) + (460690401762223/50000000000000 : ℝ)*(f.failure) + (1262767860903041/50000000000000 : ℝ)*(f.sum) + (132587228491961/29155000000000000000000000000 : ℝ)*base65 + (26425934961397718177/5831000000000000000000000000000000 : ℝ)*base67 + (42161381484109718177/5831000000000000000000000000000000 : ℝ)*base69 + (21120696079461718177/5831000000000000000000000000000000 : ℝ)*base71 + (68514403144521/29155000000000000000000000000 : ℝ)*base73 + (70985285805377718177/5831000000000000000000000000000000 : ℝ)*base75 + (5735571109554718177/5831000000000000000000000000000000 : ℝ)*base77 + (47917464924391718177/5831000000000000000000000000000000 : ℝ)*base79 + (27340292898719/7288750000000000000000000000 : ℝ)*base81 + (3180013/312500000000000000000 : ℝ)*base89 + (3180013/312500000000000000000 : ℝ)*base91 + (3180013/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1818557942831641983932028861/291550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864888879/100000000000000 : ℝ)*(base19) + (13254209/1250000000000 : ℝ)*(base23) + (64808589/50000000000000 : ℝ)*(upper3) + (6605793/10000000000000 : ℝ)*(lower4) + (25536417/12500000000000 : ℝ)*(upper5) + (176695047304269/10000000000000 : ℝ)*(major0) + (176695047304269/10000000000000 : ℝ)*(major1) + (176695047304269/10000000000000 : ℝ)*(major2) + (359129053/5000000000000 : ℝ)*(sp1) + (6921781871/100000000000000 : ℝ)*(sp2) + (2589268579877093/100000000000000 : ℝ)*(sp4) + (1294630266203577/50000000000000 : ℝ)*(sp5) + (1294630298879251/50000000000000 : ℝ)*(sp6) + (472316079144957/50000000000000 : ℝ)*(sp7) + (472316079144957/50000000000000 : ℝ)*(f.failure) + (2589268579877093/100000000000000 : ℝ)*(f.sum) + (16663578913573/5831000000000000000000000000 : ℝ)*base65 + (5122544490195224571/583100000000000000000000000000000 : ℝ)*base67 + (5872780303284224571/583100000000000000000000000000000 : ℝ)*base69 + (2634477753223324571/583100000000000000000000000000000 : ℝ)*base71 + (195890064427/29155000000000000000000000 : ℝ)*base73 + (4497842267326724571/583100000000000000000000000000000 : ℝ)*base75 + (3556881951650224571/583100000000000000000000000000000 : ℝ)*base77 + (3389300071142924571/583100000000000000000000000000000 : ℝ)*base79 + (35053153438587/5831000000000000000000000000 : ℝ)*base81 + (3956433/312500000000000000000 : ℝ)*base90 + (3956433/312500000000000000000 : ℝ)*base92 + (3956433/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1686_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4443/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1686_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1686_s2_0 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-60137061/400000000 : ℝ)*x 0 + (5487170831/10000000000 : ℝ)*x 1 + (2566771297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60137061/400000000 : ℝ)^5111 ≤ (292246786417/3125000000000 : ℝ)^4087 := by
    have hnat : (60137061 : ℕ)^5111*3125000000000^4087 ≤ 292246786417^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60137061 400000000 292246786417 3125000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487170831/10000000000 : ℝ)^5111 ≤ (47210881130919/100000000000000 : ℝ)^4087 := by
    have hnat : (5487170831 : ℕ)^5111*100000000000000^4087 ≤ 47210881130919^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487170831 10000000000 47210881130919 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566771297/5000000000 : ℝ)^5111 ≤ (43437221691319/100000000000000 : ℝ)^4087 := by
    have hnat : (2566771297 : ℕ)^5111*100000000000000^4087 ≤ 43437221691319^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566771297 5000000000 43437221691319 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60137061/400000000 : ℝ), (5487170831/10000000000 : ℝ), (2566771297/5000000000 : ℝ)] ![(292246786417/3125000000000 : ℝ), (47210881130919/100000000000000 : ℝ), (43437221691319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60137061/400000000 : ℝ)|^5111 ≤ (292246786417/3125000000000 : ℝ)^4087
        have hw : |(-60137061/400000000 : ℝ)|=(60137061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487170831/10000000000 : ℝ)|^5111 ≤ (47210881130919/100000000000000 : ℝ)^4087
        have hw : |(5487170831/10000000000 : ℝ)|=(5487170831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566771297/5000000000 : ℝ)|^5111 ≤ (43437221691319/100000000000000 : ℝ)^4087
        have hw : |(2566771297/5000000000 : ℝ)|=(2566771297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_1 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675944417/5000000000 : ℝ)*x 0 + (-84361491/500000000 : ℝ)*x 1 + (2566771301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675944417/5000000000 : ℝ)^5111 ≤ (5719978600793/12500000000000 : ℝ)^4087 := by
    have hnat : (2675944417 : ℕ)^5111*12500000000000^4087 ≤ 5719978600793^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675944417 5000000000 5719978600793 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84361491/500000000 : ℝ)^5111 ≤ (2700737353101/25000000000000 : ℝ)^4087 := by
    have hnat : (84361491 : ℕ)^5111*25000000000000^4087 ≤ 2700737353101^4087*500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84361491 500000000 2700737353101 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566771301/5000000000 : ℝ)^5111 ≤ (43437221775971/100000000000000 : ℝ)^4087 := by
    have hnat : (2566771301 : ℕ)^5111*100000000000000^4087 ≤ 43437221775971^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566771301 5000000000 43437221775971 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675944417/5000000000 : ℝ), (-84361491/500000000 : ℝ), (2566771301/5000000000 : ℝ)] ![(5719978600793/12500000000000 : ℝ), (2700737353101/25000000000000 : ℝ), (43437221775971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675944417/5000000000 : ℝ)|^5111 ≤ (5719978600793/12500000000000 : ℝ)^4087
        have hw : |(2675944417/5000000000 : ℝ)|=(2675944417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84361491/500000000 : ℝ)|^5111 ≤ (2700737353101/25000000000000 : ℝ)^4087
        have hw : |(-84361491/500000000 : ℝ)|=(84361491/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566771301/5000000000 : ℝ)|^5111 ≤ (43437221775971/100000000000000 : ℝ)^4087
        have hw : |(2566771301/5000000000 : ℝ)|=(2566771301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_2 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070377779/2000000000 : ℝ)*x 0 + (5133542457/10000000000 : ℝ)*x 1 + (-1687229929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070377779/2000000000 : ℝ)^5111 ≤ (22879914729293/50000000000000 : ℝ)^4087 := by
    have hnat : (1070377779 : ℕ)^5111*50000000000000^4087 ≤ 22879914729293^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070377779 2000000000 22879914729293 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133542457/10000000000 : ℝ)^5111 ≤ (43437220241657/100000000000000 : ℝ)^4087 := by
    have hnat : (5133542457 : ℕ)^5111*100000000000000^4087 ≤ 43437220241657^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133542457 10000000000 43437220241657 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1687229929/10000000000 : ℝ)^5111 ≤ (5401475142583/50000000000000 : ℝ)^4087 := by
    have hnat : (1687229929 : ℕ)^5111*50000000000000^4087 ≤ 5401475142583^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687229929 10000000000 5401475142583 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070377779/2000000000 : ℝ), (5133542457/10000000000 : ℝ), (-1687229929/10000000000 : ℝ)] ![(22879914729293/50000000000000 : ℝ), (43437220241657/100000000000000 : ℝ), (5401475142583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070377779/2000000000 : ℝ)|^5111 ≤ (22879914729293/50000000000000 : ℝ)^4087
        have hw : |(1070377779/2000000000 : ℝ)|=(1070377779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133542457/10000000000 : ℝ)|^5111 ≤ (43437220241657/100000000000000 : ℝ)^4087
        have hw : |(5133542457/10000000000 : ℝ)|=(5133542457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1687229929/10000000000 : ℝ)|^5111 ≤ (5401475142583/50000000000000 : ℝ)^4087
        have hw : |(-1687229929/10000000000 : ℝ)|=(1687229929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_3 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2068270249/5000000000 : ℝ)*x 0 + (1835522147/5000000000 : ℝ)*x 1 + (2320175881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068270249/5000000000 : ℝ)^5111 ≤ (8289446981863/25000000000000 : ℝ)^4087 := by
    have hnat : (2068270249 : ℕ)^5111*25000000000000^4087 ≤ 8289446981863^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068270249 5000000000 8289446981863 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1835522147/5000000000 : ℝ)^5111 ≤ (28559291953657/100000000000000 : ℝ)^4087 := by
    have hnat : (1835522147 : ℕ)^5111*100000000000000^4087 ≤ 28559291953657^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835522147 5000000000 28559291953657 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320175881/5000000000 : ℝ)^5111 ≤ (9570730024823/25000000000000 : ℝ)^4087 := by
    have hnat : (2320175881 : ℕ)^5111*25000000000000^4087 ≤ 9570730024823^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320175881 5000000000 9570730024823 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2068270249/5000000000 : ℝ), (1835522147/5000000000 : ℝ), (2320175881/5000000000 : ℝ)] ![(8289446981863/25000000000000 : ℝ), (28559291953657/100000000000000 : ℝ), (9570730024823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2068270249/5000000000 : ℝ)|^5111 ≤ (8289446981863/25000000000000 : ℝ)^4087
        have hw : |(2068270249/5000000000 : ℝ)|=(2068270249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1835522147/5000000000 : ℝ)|^5111 ≤ (28559291953657/100000000000000 : ℝ)^4087
        have hw : |(1835522147/5000000000 : ℝ)|=(1835522147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2320175881/5000000000 : ℝ)|^5111 ≤ (9570730024823/25000000000000 : ℝ)^4087
        have hw : |(2320175881/5000000000 : ℝ)|=(2320175881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_4 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-751797129/5000000000 : ℝ)*x 0 + (2568701073/5000000000 : ℝ)*x 1 + (5483253187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751797129/5000000000 : ℝ)^5111 ≤ (2338300490881/25000000000000 : ℝ)^4087 := by
    have hnat : (751797129 : ℕ)^5111*25000000000000^4087 ≤ 2338300490881^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751797129 5000000000 2338300490881 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568701073/5000000000 : ℝ)^5111 ≤ (43478065280957/100000000000000 : ℝ)^4087 := by
    have hnat : (2568701073 : ℕ)^5111*100000000000000^4087 ≤ 43478065280957^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568701073 5000000000 43478065280957 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483253187/10000000000 : ℝ)^5111 ≤ (23584366370751/50000000000000 : ℝ)^4087 := by
    have hnat : (5483253187 : ℕ)^5111*50000000000000^4087 ≤ 23584366370751^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483253187 10000000000 23584366370751 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-751797129/5000000000 : ℝ), (2568701073/5000000000 : ℝ), (5483253187/10000000000 : ℝ)] ![(2338300490881/25000000000000 : ℝ), (43478065280957/100000000000000 : ℝ), (23584366370751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-751797129/5000000000 : ℝ)|^5111 ≤ (2338300490881/25000000000000 : ℝ)^4087
        have hw : |(-751797129/5000000000 : ℝ)|=(751797129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568701073/5000000000 : ℝ)|^5111 ≤ (43478065280957/100000000000000 : ℝ)^4087
        have hw : |(2568701073/5000000000 : ℝ)|=(2568701073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483253187/10000000000 : ℝ)|^5111 ≤ (23584366370751/50000000000000 : ℝ)^4087
        have hw : |(5483253187/10000000000 : ℝ)|=(5483253187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_5 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257384609/10000000000 : ℝ)*x 0 + (-1337519243/10000000000 : ℝ)*x 1 + (5483253181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257384609/10000000000 : ℝ)^5111 ≤ (44751589284431/100000000000000 : ℝ)^4087 := by
    have hnat : (5257384609 : ℕ)^5111*100000000000000^4087 ≤ 44751589284431^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257384609 10000000000 44751589284431 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1337519243/10000000000 : ℝ)^5111 ≤ (8079678017969/100000000000000 : ℝ)^4087 := by
    have hnat : (1337519243 : ℕ)^5111*100000000000000^4087 ≤ 8079678017969^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337519243 10000000000 8079678017969 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483253181/10000000000 : ℝ)^5111 ≤ (11792183169239/25000000000000 : ℝ)^4087 := by
    have hnat : (5483253181 : ℕ)^5111*25000000000000^4087 ≤ 11792183169239^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483253181 10000000000 11792183169239 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257384609/10000000000 : ℝ), (-1337519243/10000000000 : ℝ), (5483253181/10000000000 : ℝ)] ![(44751589284431/100000000000000 : ℝ), (8079678017969/100000000000000 : ℝ), (11792183169239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257384609/10000000000 : ℝ)|^5111 ≤ (44751589284431/100000000000000 : ℝ)^4087
        have hw : |(5257384609/10000000000 : ℝ)|=(5257384609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1337519243/10000000000 : ℝ)|^5111 ≤ (8079678017969/100000000000000 : ℝ)^4087
        have hw : |(-1337519243/10000000000 : ℝ)|=(1337519243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483253181/10000000000 : ℝ)|^5111 ≤ (11792183169239/25000000000000 : ℝ)^4087
        have hw : |(5483253181/10000000000 : ℝ)|=(5483253181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_6 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257384613/10000000000 : ℝ)*x 0 + (5483253179/10000000000 : ℝ)*x 1 + (-668759621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257384613/10000000000 : ℝ)^5111 ≤ (44751589327011/100000000000000 : ℝ)^4087 := by
    have hnat : (5257384613 : ℕ)^5111*100000000000000^4087 ≤ 44751589327011^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257384613 10000000000 44751589327011 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483253179/10000000000 : ℝ)^5111 ≤ (47168732655441/100000000000000 : ℝ)^4087 := by
    have hnat : (5483253179 : ℕ)^5111*100000000000000^4087 ≤ 47168732655441^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483253179 10000000000 47168732655441 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668759621/5000000000 : ℝ)^5111 ≤ (4039839005207/50000000000000 : ℝ)^4087 := by
    have hnat : (668759621 : ℕ)^5111*50000000000000^4087 ≤ 4039839005207^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668759621 5000000000 4039839005207 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257384613/10000000000 : ℝ), (5483253179/10000000000 : ℝ), (-668759621/5000000000 : ℝ)] ![(44751589327011/100000000000000 : ℝ), (47168732655441/100000000000000 : ℝ), (4039839005207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257384613/10000000000 : ℝ)|^5111 ≤ (44751589327011/100000000000000 : ℝ)^4087
        have hw : |(5257384613/10000000000 : ℝ)|=(5257384613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483253179/10000000000 : ℝ)|^5111 ≤ (47168732655441/100000000000000 : ℝ)^4087
        have hw : |(5483253179/10000000000 : ℝ)|=(5483253179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668759621/5000000000 : ℝ)|^5111 ≤ (4039839005207/50000000000000 : ℝ)^4087
        have hw : |(-668759621/5000000000 : ℝ)|=(668759621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s2_7 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517125011/1250000000 : ℝ)*x 0 + (2314886121/5000000000 : ℝ)*x 1 + (115055713/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517125011/1250000000 : ℝ)^5111 ≤ (4145299376427/12500000000000 : ℝ)^4087 := by
    have hnat : (517125011 : ℕ)^5111*12500000000000^4087 ≤ 4145299376427^4087*1250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517125011 1250000000 4145299376427 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2314886121/5000000000 : ℝ)^5111 ≤ (1908690094487/5000000000000 : ℝ)^4087 := by
    have hnat : (2314886121 : ℕ)^5111*5000000000000^4087 ≤ 1908690094487^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314886121 5000000000 1908690094487 5000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115055713/312500000 : ℝ)^5111 ≤ (1146552123601/4000000000000 : ℝ)^4087 := by
    have hnat : (115055713 : ℕ)^5111*4000000000000^4087 ≤ 1146552123601^4087*312500000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115055713 312500000 1146552123601 4000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517125011/1250000000 : ℝ), (2314886121/5000000000 : ℝ), (115055713/312500000 : ℝ)] ![(4145299376427/12500000000000 : ℝ), (1908690094487/5000000000000 : ℝ), (1146552123601/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517125011/1250000000 : ℝ)|^5111 ≤ (4145299376427/12500000000000 : ℝ)^4087
        have hw : |(517125011/1250000000 : ℝ)|=(517125011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2314886121/5000000000 : ℝ)|^5111 ≤ (1908690094487/5000000000000 : ℝ)^4087
        have hw : |(2314886121/5000000000 : ℝ)|=(2314886121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115055713/312500000 : ℝ)|^5111 ≤ (1146552123601/4000000000000 : ℝ)^4087
        have hw : |(115055713/312500000 : ℝ)|=(115055713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1686_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4443/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9767/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1729/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4443/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4443/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4443/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4443/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4443/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4443/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9349/100000 : ℝ) ^ (5103/1024 : ℝ) ≤ (37143490185043/5000000000000000000 : ℝ) := by
    have hpowers : (9349/100000 : ℝ)^5103 ≤ (37143490185043/5000000000000000000 : ℝ)^1024 := by
      have hnat : (9349 : ℕ)^5103*5000000000000000000^1024 ≤ 37143490185043^1024*100000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9349 100000 37143490185043 5000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9349/100000 : ℝ)) (X := (37143490185043/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4443/25000 : ℝ) ^ (5103/1024 : ℝ) ≤ (18244714530298693/100000000000000000000 : ℝ) := by
    have hpowers : (4443/25000 : ℝ)^5103 ≤ (18244714530298693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4443 : ℕ)^5103*100000000000000000000^1024 ≤ 18244714530298693^1024*25000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4443 25000 18244714530298693 100000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4443/25000 : ℝ)) (X := (18244714530298693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500037143490185043/2500000000000000000 : ℝ) ≤ (10000029813606193/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (2500037143490185043/2500000000000000000 : ℝ)^1024 ≤ (10000029813606193/10000000000000000 : ℝ)^5103 := by
      have hnat : (2500037143490185043 : ℕ)^1024*10000000000000000^5103 ≤ 10000029813606193^5103*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500037143490185043 2500000000000000000 10000029813606193 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000029813606193/10000000000000000 : ℝ)) (X := (2500037143490185043/2500000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018987584333999553/100000000000000000000 : ℝ) ≤ (10000380987870503/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (100018987584333999553/100000000000000000000 : ℝ)^1024 ≤ (10000380987870503/10000000000000000 : ℝ)^5103 := by
      have hnat : (100018987584333999553 : ℕ)^1024*10000000000000000^5103 ≤ 10000380987870503^5103*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018987584333999553 100000000000000000000 10000380987870503 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000380987870503/10000000000000000 : ℝ)) (X := (100018987584333999553/100000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018244714530298693/50000000000000000000 : ℝ) ≤ (10000732162134813/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (50018244714530298693/50000000000000000000 : ℝ)^1024 ≤ (10000732162134813/10000000000000000 : ℝ)^5103 := by
      have hnat : (50018244714530298693 : ℕ)^1024*10000000000000000^5103 ≤ 10000732162134813^5103*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018244714530298693 50000000000000000000 10000732162134813 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000732162134813/10000000000000000 : ℝ)) (X := (50018244714530298693/50000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(37143490185043/5000000000000000000 : ℝ) ≤ ((84223684863610895259/84230000000000000000 : ℝ)+2*(35117426431/84230000000000 : ℝ)*(9349/100000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (84223684863610895259/84230000000000000000 : ℝ)+2*(35117426431/84230000000000 : ℝ)*(9349/100000 : ℝ)=(10000029813606193/10000000000000000 : ℝ) by norm_num, show 1+2*(37143490185043/5000000000000000000 : ℝ)=(2500037143490185043/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18244714530298693/100000000000000000000 : ℝ)+(37143490185043/5000000000000000000 : ℝ) ≤ ((84223684863610895259/84230000000000000000 : ℝ)+(35117426431/84230000000000 : ℝ)*((4443/25000 : ℝ)+(9349/100000 : ℝ)))^(5103/1024 : ℝ) := by
    rw [show (84223684863610895259/84230000000000000000 : ℝ)+(35117426431/84230000000000 : ℝ)*((4443/25000 : ℝ)+(9349/100000 : ℝ))=(10000380987870503/10000000000000000 : ℝ) by norm_num, show 1+(18244714530298693/100000000000000000000 : ℝ)+(37143490185043/5000000000000000000 : ℝ)=(100018987584333999553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18244714530298693/100000000000000000000 : ℝ) ≤ ((84223684863610895259/84230000000000000000 : ℝ)+2*(35117426431/84230000000000 : ℝ)*(4443/25000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (84223684863610895259/84230000000000000000 : ℝ)+2*(35117426431/84230000000000 : ℝ)*(4443/25000 : ℝ)=(10000732162134813/10000000000000000 : ℝ) by norm_num, show 1+2*(18244714530298693/100000000000000000000 : ℝ)=(50018244714530298693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84223684863610895259/84230000000000000000 : ℝ)*(X 1 0+X 2 0)+(35117426431/84230000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9349/100000 : ℝ)) (hi := (4443/25000 : ℝ)) (c := (84223684863610895259/84230000000000000000 : ℝ)) (alpha := (35117426431/84230000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84223684863610895259/84230000000000000000 : ℝ)*(X 0 1+X 2 1)+(35117426431/84230000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9349/100000 : ℝ)) (hi := (4443/25000 : ℝ)) (c := (84223684863610895259/84230000000000000000 : ℝ)) (alpha := (35117426431/84230000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84223684863610895259/84230000000000000000 : ℝ)*(X 0 2+X 1 2)+(35117426431/84230000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9349/100000 : ℝ)) (hi := (4443/25000 : ℝ)) (c := (84223684863610895259/84230000000000000000 : ℝ)) (alpha := (35117426431/84230000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-60137061/400000000 : ℝ)*X 0 0+(5487170831/10000000000 : ℝ)*X 0 1+(2566771297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675944417/5000000000 : ℝ)*X 1 0+(-84361491/500000000 : ℝ)*X 1 1+(2566771301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070377779/2000000000 : ℝ)*X 2 0+(5133542457/10000000000 : ℝ)*X 2 1+(-1687229929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2068270249/5000000000 : ℝ)*X 0 0+(1835522147/5000000000 : ℝ)*X 0 1+(2320175881/5000000000 : ℝ)*X 0 2+(2068270249/5000000000 : ℝ)*X 1 0+(1835522147/5000000000 : ℝ)*X 1 1+(2320175881/5000000000 : ℝ)*X 1 2+(2068270249/5000000000 : ℝ)*X 2 0+(1835522147/5000000000 : ℝ)*X 2 1+(2320175881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-751797129/5000000000 : ℝ)*X 0 0+(2568701073/5000000000 : ℝ)*X 0 1+(5483253187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257384609/10000000000 : ℝ)*X 1 0+(-1337519243/10000000000 : ℝ)*X 1 1+(5483253181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257384613/10000000000 : ℝ)*X 2 0+(5483253179/10000000000 : ℝ)*X 2 1+(-668759621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((517125011/1250000000 : ℝ)*X 0 0+(2314886121/5000000000 : ℝ)*X 0 1+(115055713/312500000 : ℝ)*X 0 2+(517125011/1250000000 : ℝ)*X 1 0+(2314886121/5000000000 : ℝ)*X 1 1+(115055713/312500000 : ℝ)*X 1 2+(517125011/1250000000 : ℝ)*X 2 0+(2314886121/5000000000 : ℝ)*X 2 1+(115055713/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55359786881832389691184929897/4211500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1985218137/100000000000000 : ℝ)*(base19) + (29100757/1562500000000 : ℝ)*(base23) + (4147747/5000000000000 : ℝ)*(lower2) + (352737621/100000000000000 : ℝ)*(upper3) + (35393637/20000000000000 : ℝ)*(upper5) + (1929772197839187/100000000000000 : ℝ)*(major0) + (1929772197839187/100000000000000 : ℝ)*(major1) + (1929772197839187/100000000000000 : ℝ)*(major2) + (1413923909142199/50000000000000 : ℝ)*(sp0) + (17674146480251/625000000000 : ℝ)*(sp1) + (56557271192197/2000000000000 : ℝ)*(sp2) + (1031670737337199/100000000000000 : ℝ)*(sp3) + (17603773899/100000000000000 : ℝ)*(sp4) + (7798119217/100000000000000 : ℝ)*(sp7) + (32239954233013/3125000000000 : ℝ)*(f.failure) + (2827865422058297/100000000000000 : ℝ)*(f.sum) + (2890656913811/2105750000000000000000000000 : ℝ)*base66 + (73578114326096285567/8423000000000000000000000000000000 : ℝ)*base68 + (88260542309425285567/8423000000000000000000000000000000 : ℝ)*base70 + (15334759198894285567/8423000000000000000000000000000000 : ℝ)*base72 + (4077124094333/4211500000000000000000000000 : ℝ)*base74 + (34072703068710285567/8423000000000000000000000000000000 : ℝ)*base76 + (101256453976024285567/8423000000000000000000000000000000 : ℝ)*base78 + (88242721220830285567/8423000000000000000000000000000000 : ℝ)*base80 + (16980626244593/4211500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (183131/39062500000000000000 : ℝ)*base89 + (183131/39062500000000000000 : ℝ)*base91 + (183131/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57700839952843781778368098527/4211500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1973155801/100000000000000 : ℝ)*(base19) + (17021233/800000000000 : ℝ)*(base23) + (147883521/50000000000000 : ℝ)*(upper3) + (2717623/4000000000000 : ℝ)*(lower4) + (144261811/50000000000000 : ℝ)*(upper5) + (1973140835346917/100000000000000 : ℝ)*(major0) + (1973140835346917/100000000000000 : ℝ)*(major1) + (1973140835346917/100000000000000 : ℝ)*(major2) + (16977542589/100000000000000 : ℝ)*(sp1) + (4565230183/25000000000000 : ℝ)*(sp2) + (90356790729987/3125000000000 : ℝ)*(sp4) + (1445699176330597/50000000000000 : ℝ)*(sp5) + (2891396914784727/100000000000000 : ℝ)*(sp6) + (8241124301887/781250000000 : ℝ)*(sp7) + (8241124301887/781250000000 : ℝ)*(f.failure) + (90356790729987/3125000000000 : ℝ)*(f.sum) + (6806896164677/4211500000000000000000000000 : ℝ)*base66 + (130704131885405433497/8423000000000000000000000000000000 : ℝ)*base68 + (42353841250589433497/8423000000000000000000000000000000 : ℝ)*base70 + (49255899769977433497/8423000000000000000000000000000000 : ℝ)*base72 + (12064602288029/2105750000000000000000000000 : ℝ)*base74 + (168207279047321433497/8423000000000000000000000000000000 : ℝ)*base76 + (29441318025214433497/8423000000000000000000000000000000 : ℝ)*base78 + (115590308299644433497/8423000000000000000000000000000000 : ℝ)*base80 + (4921310429833/2105750000000000000000000000 : ℝ)*base81 + (222051/39062500000000000000 : ℝ)*base89 + (222051/39062500000000000000 : ℝ)*base91 + (222051/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1686_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4443/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1686_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1686_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1686_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1686_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1686_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1686_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
