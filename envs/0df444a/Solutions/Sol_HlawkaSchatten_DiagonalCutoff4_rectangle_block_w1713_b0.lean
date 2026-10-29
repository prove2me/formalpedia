-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1713_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:42.145479+00:00
-- url     : https://prove2.me/submissions/c5277c37-befa-469a-bbc7-4dad5c441800

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
theorem support_rectangle_w1713_s0_0 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1327805609/10000000000 : ℝ)*x 0 + (5691889813/10000000000 : ℝ)*x 1 + (620418939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327805609/10000000000 : ℝ)^5327 ≤ (8212279852601/100000000000000 : ℝ)^4303 := by
    have hnat : (1327805609 : ℕ)^5327*100000000000000^4303 ≤ 8212279852601^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327805609 10000000000 8212279852601 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5691889813/10000000000 : ℝ)^5327 ≤ (6221914293393/12500000000000 : ℝ)^4303 := by
    have hnat : (5691889813 : ℕ)^5327*12500000000000^4303 ≤ 6221914293393^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691889813 10000000000 6221914293393 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (620418939/1250000000 : ℝ)^5327 ≤ (42012405786229/100000000000000 : ℝ)^4303 := by
    have hnat : (620418939 : ℕ)^5327*100000000000000^4303 ≤ 42012405786229^4303*1250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620418939 1250000000 42012405786229 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1327805609/10000000000 : ℝ), (5691889813/10000000000 : ℝ), (620418939/1250000000 : ℝ)] ![(8212279852601/100000000000000 : ℝ), (6221914293393/12500000000000 : ℝ), (42012405786229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1327805609/10000000000 : ℝ)|^5327 ≤ (8212279852601/100000000000000 : ℝ)^4303
        have hw : |(-1327805609/10000000000 : ℝ)|=(1327805609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5691889813/10000000000 : ℝ)|^5327 ≤ (6221914293393/12500000000000 : ℝ)^4303
        have hw : |(5691889813/10000000000 : ℝ)|=(5691889813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(620418939/1250000000 : ℝ)|^5327 ≤ (42012405786229/100000000000000 : ℝ)^4303
        have hw : |(620418939/1250000000 : ℝ)|=(620418939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_1 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675273377/1250000000 : ℝ)*x 0 + (-1721924107/10000000000 : ℝ)*x 1 + (124083783/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675273377/1250000000 : ℝ)^5327 ≤ (46658230916437/100000000000000 : ℝ)^4303 := by
    have hnat : (675273377 : ℕ)^5327*100000000000000^4303 ≤ 46658230916437^4303*1250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675273377 1250000000 46658230916437 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1721924107/10000000000 : ℝ)^5327 ≤ (5664682647719/50000000000000 : ℝ)^4303 := by
    have hnat : (1721924107 : ℕ)^5327*50000000000000^4303 ≤ 5664682647719^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721924107 10000000000 5664682647719 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124083783/250000000 : ℝ)^5327 ≤ (42012403774289/100000000000000 : ℝ)^4303 := by
    have hnat : (124083783 : ℕ)^5327*100000000000000^4303 ≤ 42012403774289^4303*250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124083783 250000000 42012403774289 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675273377/1250000000 : ℝ), (-1721924107/10000000000 : ℝ), (124083783/250000000 : ℝ)] ![(46658230916437/100000000000000 : ℝ), (5664682647719/50000000000000 : ℝ), (42012403774289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675273377/1250000000 : ℝ)|^5327 ≤ (46658230916437/100000000000000 : ℝ)^4303
        have hw : |(675273377/1250000000 : ℝ)|=(675273377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1721924107/10000000000 : ℝ)|^5327 ≤ (5664682647719/50000000000000 : ℝ)^4303
        have hw : |(-1721924107/10000000000 : ℝ)|=(1721924107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124083783/250000000 : ℝ)|^5327 ≤ (42012403774289/100000000000000 : ℝ)^4303
        have hw : |(124083783/250000000 : ℝ)|=(124083783/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_2 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701093367/5000000000 : ℝ)*x 0 + (1240837871/2500000000 : ℝ)*x 1 + (-344384853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701093367/5000000000 : ℝ)^5327 ≤ (46658227901217/100000000000000 : ℝ)^4303 := by
    have hnat : (2701093367 : ℕ)^5327*100000000000000^4303 ≤ 46658227901217^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701093367 5000000000 46658227901217 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240837871/2500000000 : ℝ)^5327 ≤ (42012405492821/100000000000000 : ℝ)^4303 := by
    have hnat : (1240837871 : ℕ)^5327*100000000000000^4303 ≤ 42012405492821^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240837871 2500000000 42012405492821 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344384853/2000000000 : ℝ)^5327 ≤ (11329366582383/100000000000000 : ℝ)^4303 := by
    have hnat : (344384853 : ℕ)^5327*100000000000000^4303 ≤ 11329366582383^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344384853 2000000000 11329366582383 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701093367/5000000000 : ℝ), (1240837871/2500000000 : ℝ), (-344384853/2000000000 : ℝ)] ![(46658227901217/100000000000000 : ℝ), (42012405492821/100000000000000 : ℝ), (11329366582383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701093367/5000000000 : ℝ)|^5327 ≤ (46658227901217/100000000000000 : ℝ)^4303
        have hw : |(2701093367/5000000000 : ℝ)|=(2701093367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1240837871/2500000000 : ℝ)|^5327 ≤ (42012405492821/100000000000000 : ℝ)^4303
        have hw : |(1240837871/2500000000 : ℝ)|=(1240837871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344384853/2000000000 : ℝ)|^5327 ≤ (11329366582383/100000000000000 : ℝ)^4303
        have hw : |(-344384853/2000000000 : ℝ)|=(344384853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_3 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1009265097/2500000000 : ℝ)*x 0 + (612172299/2000000000 : ℝ)*x 1 + (1296880919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009265097/2500000000 : ℝ)^5327 ≤ (3253263277089/10000000000000 : ℝ)^4303 := by
    have hnat : (1009265097 : ℕ)^5327*10000000000000^4303 ≤ 3253263277089^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009265097 2500000000 3253263277089 10000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (612172299/2000000000 : ℝ)^5327 ≤ (23093411541339/100000000000000 : ℝ)^4303 := by
    have hnat : (612172299 : ℕ)^5327*100000000000000^4303 ≤ 23093411541339^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612172299 2000000000 23093411541339 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296880919/2500000000 : ℝ)^5327 ≤ (2773372230339/6250000000000 : ℝ)^4303 := by
    have hnat : (1296880919 : ℕ)^5327*6250000000000^4303 ≤ 2773372230339^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296880919 2500000000 2773372230339 6250000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1009265097/2500000000 : ℝ), (612172299/2000000000 : ℝ), (1296880919/2500000000 : ℝ)] ![(3253263277089/10000000000000 : ℝ), (23093411541339/100000000000000 : ℝ), (2773372230339/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1009265097/2500000000 : ℝ)|^5327 ≤ (3253263277089/10000000000000 : ℝ)^4303
        have hw : |(1009265097/2500000000 : ℝ)|=(1009265097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(612172299/2000000000 : ℝ)|^5327 ≤ (23093411541339/100000000000000 : ℝ)^4303
        have hw : |(612172299/2000000000 : ℝ)|=(612172299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296880919/2500000000 : ℝ)|^5327 ≤ (2773372230339/6250000000000 : ℝ)^4303
        have hw : |(1296880919/2500000000 : ℝ)|=(1296880919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_4 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-332357433/2500000000 : ℝ)*x 0 + (1245298919/2500000000 : ℝ)*x 1 + (5673454553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332357433/2500000000 : ℝ)^5327 ≤ (4112358527359/50000000000000 : ℝ)^4303 := by
    have hnat : (332357433 : ℕ)^5327*50000000000000^4303 ≤ 4112358527359^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332357433 2500000000 4112358527359 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1245298919/2500000000 : ℝ)^5327 ≤ (8439894425121/20000000000000 : ℝ)^4303 := by
    have hnat : (1245298919 : ℕ)^5327*20000000000000^4303 ≤ 8439894425121^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245298919 2500000000 8439894425121 20000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673454553/10000000000 : ℝ)^5327 ≤ (49575810807477/100000000000000 : ℝ)^4303 := by
    have hnat : (5673454553 : ℕ)^5327*100000000000000^4303 ≤ 49575810807477^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673454553 10000000000 49575810807477 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332357433/2500000000 : ℝ), (1245298919/2500000000 : ℝ), (5673454553/10000000000 : ℝ)] ![(4112358527359/50000000000000 : ℝ), (8439894425121/20000000000000 : ℝ), (49575810807477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332357433/2500000000 : ℝ)|^5327 ≤ (4112358527359/50000000000000 : ℝ)^4303
        have hw : |(-332357433/2500000000 : ℝ)|=(332357433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1245298919/2500000000 : ℝ)|^5327 ≤ (8439894425121/20000000000000 : ℝ)^4303
        have hw : |(1245298919/2500000000 : ℝ)|=(1245298919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673454553/10000000000 : ℝ)|^5327 ≤ (49575810807477/100000000000000 : ℝ)^4303
        have hw : |(5673454553/10000000000 : ℝ)|=(5673454553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_5 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650613941/1250000000 : ℝ)*x 0 + (-505910401/5000000000 : ℝ)*x 1 + (5673454109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650613941/1250000000 : ℝ)^5327 ≤ (22279079696177/50000000000000 : ℝ)^4303 := by
    have hnat : (650613941 : ℕ)^5327*50000000000000^4303 ≤ 22279079696177^4303*1250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650613941 1250000000 22279079696177 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505910401/5000000000 : ℝ)^5327 ≤ (5866034588891/100000000000000 : ℝ)^4303 := by
    have hnat : (505910401 : ℕ)^5327*100000000000000^4303 ≤ 5866034588891^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505910401 5000000000 5866034588891 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673454109/10000000000 : ℝ)^5327 ≤ (49575806004433/100000000000000 : ℝ)^4303 := by
    have hnat : (5673454109 : ℕ)^5327*100000000000000^4303 ≤ 49575806004433^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673454109 10000000000 49575806004433 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650613941/1250000000 : ℝ), (-505910401/5000000000 : ℝ), (5673454109/10000000000 : ℝ)] ![(22279079696177/50000000000000 : ℝ), (5866034588891/100000000000000 : ℝ), (49575806004433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650613941/1250000000 : ℝ)|^5327 ≤ (22279079696177/50000000000000 : ℝ)^4303
        have hw : |(650613941/1250000000 : ℝ)|=(650613941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505910401/5000000000 : ℝ)|^5327 ≤ (5866034588891/100000000000000 : ℝ)^4303
        have hw : |(-505910401/5000000000 : ℝ)|=(505910401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673454109/10000000000 : ℝ)|^5327 ≤ (49575806004433/100000000000000 : ℝ)^4303
        have hw : |(5673454109/10000000000 : ℝ)|=(5673454109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_6 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204911233/10000000000 : ℝ)*x 0 + (177295451/312500000 : ℝ)*x 1 + (-1011820751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204911233/10000000000 : ℝ)^5327 ≤ (22279078132967/50000000000000 : ℝ)^4303 := by
    have hnat : (5204911233 : ℕ)^5327*50000000000000^4303 ≤ 22279078132967^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204911233 10000000000 22279078132967 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177295451/312500000 : ℝ)^5327 ≤ (2478790474927/5000000000000 : ℝ)^4303 := by
    have hnat : (177295451 : ℕ)^5327*5000000000000^4303 ≤ 2478790474927^4303*312500000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177295451 312500000 2478790474927 5000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011820751/10000000000 : ℝ)^5327 ≤ (733254277857/12500000000000 : ℝ)^4303 := by
    have hnat : (1011820751 : ℕ)^5327*12500000000000^4303 ≤ 733254277857^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011820751 10000000000 733254277857 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204911233/10000000000 : ℝ), (177295451/312500000 : ℝ), (-1011820751/10000000000 : ℝ)] ![(22279078132967/50000000000000 : ℝ), (2478790474927/5000000000000 : ℝ), (733254277857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204911233/10000000000 : ℝ)|^5327 ≤ (22279078132967/50000000000000 : ℝ)^4303
        have hw : |(5204911233/10000000000 : ℝ)|=(5204911233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177295451/312500000 : ℝ)|^5327 ≤ (2478790474927/5000000000000 : ℝ)^4303
        have hw : |(177295451/312500000 : ℝ)|=(177295451/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011820751/10000000000 : ℝ)|^5327 ≤ (733254277857/12500000000000 : ℝ)^4303
        have hw : |(-1011820751/10000000000 : ℝ)|=(1011820751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s0_7 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4041798457/10000000000 : ℝ)*x 0 + (1283858589/2500000000 : ℝ)*x 1 + (1557337199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041798457/10000000000 : ℝ)^5327 ≤ (16289953656053/50000000000000 : ℝ)^4303 := by
    have hnat : (4041798457 : ℕ)^5327*50000000000000^4303 ≤ 16289953656053^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041798457 10000000000 16289953656053 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283858589/2500000000 : ℝ)^5327 ≤ (43823011548781/100000000000000 : ℝ)^4303 := by
    have hnat : (1283858589 : ℕ)^5327*100000000000000^4303 ≤ 43823011548781^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283858589 2500000000 43823011548781 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557337199/5000000000 : ℝ)^5327 ≤ (2949635140491/12500000000000 : ℝ)^4303 := by
    have hnat : (1557337199 : ℕ)^5327*12500000000000^4303 ≤ 2949635140491^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557337199 5000000000 2949635140491 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041798457/10000000000 : ℝ), (1283858589/2500000000 : ℝ), (1557337199/5000000000 : ℝ)] ![(16289953656053/50000000000000 : ℝ), (43823011548781/100000000000000 : ℝ), (2949635140491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041798457/10000000000 : ℝ)|^5327 ≤ (16289953656053/50000000000000 : ℝ)^4303
        have hw : |(4041798457/10000000000 : ℝ)|=(4041798457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283858589/2500000000 : ℝ)|^5327 ≤ (43823011548781/100000000000000 : ℝ)^4303
        have hw : |(1283858589/2500000000 : ℝ)|=(1283858589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1557337199/5000000000 : ℝ)|^5327 ≤ (2949635140491/12500000000000 : ℝ)^4303
        have hw : |(1557337199/5000000000 : ℝ)|=(1557337199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1713_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5451/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5319/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5319 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5319*1^1024 ≤ 0^1024*1^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5319/1024 : ℝ) ≤ (856970578495542053/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5319 ≤ (856970578495542053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5319*100000000000000000000^1024 ≤ 856970578495542053^1024*5^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 856970578495542053 100000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (856970578495542053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5319 := by
      have hnat : (1 : ℕ)^1024*1^5319 ≤ 1^5319*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100856970578495542053/100000000000000000000 : ℝ) ≤ (2504110346039191/2500000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (100856970578495542053/100000000000000000000 : ℝ)^1024 ≤ (2504110346039191/2500000000000000 : ℝ)^5319 := by
      have hnat : (100856970578495542053 : ℕ)^1024*2500000000000000^5319 ≤ 2504110346039191^5319*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100856970578495542053 100000000000000000000 2504110346039191 2500000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504110346039191/2500000000000000 : ℝ)) (X := (100856970578495542053/100000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50856970578495542053/50000000000000000000 : ℝ) ≤ (1254110346039191/1250000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (50856970578495542053/50000000000000000000 : ℝ)^1024 ≤ (1254110346039191/1250000000000000 : ℝ)^5319 := by
      have hnat : (50856970578495542053 : ℕ)^1024*1250000000000000^5319 ≤ 1254110346039191^5319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50856970578495542053 50000000000000000000 1254110346039191 1250000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254110346039191/1250000000000000 : ℝ)) (X := (50856970578495542053/50000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4110346039191/1000000000000000 : ℝ)*(0 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4110346039191/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(856970578495542053/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4110346039191/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5319/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4110346039191/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2504110346039191/2500000000000000 : ℝ) by norm_num, show 1+(856970578495542053/100000000000000000000 : ℝ)+(0 : ℝ)=(100856970578495542053/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(856970578495542053/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4110346039191/1000000000000000 : ℝ)*(2/5 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4110346039191/1000000000000000 : ℝ)*(2/5 : ℝ)=(1254110346039191/1250000000000000 : ℝ) by norm_num, show 1+2*(856970578495542053/100000000000000000000 : ℝ)=(50856970578495542053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4110346039191/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4110346039191/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4110346039191/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4110346039191/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4110346039191/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4110346039191/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1327805609/10000000000 : ℝ)*X 0 0+(5691889813/10000000000 : ℝ)*X 0 1+(620418939/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675273377/1250000000 : ℝ)*X 1 0+(-1721924107/10000000000 : ℝ)*X 1 1+(124083783/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701093367/5000000000 : ℝ)*X 2 0+(1240837871/2500000000 : ℝ)*X 2 1+(-344384853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1009265097/2500000000 : ℝ)*X 0 0+(612172299/2000000000 : ℝ)*X 0 1+(1296880919/2500000000 : ℝ)*X 0 2+(1009265097/2500000000 : ℝ)*X 1 0+(612172299/2000000000 : ℝ)*X 1 1+(1296880919/2500000000 : ℝ)*X 1 2+(1009265097/2500000000 : ℝ)*X 2 0+(612172299/2000000000 : ℝ)*X 2 1+(1296880919/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-332357433/2500000000 : ℝ)*X 0 0+(1245298919/2500000000 : ℝ)*X 0 1+(5673454553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650613941/1250000000 : ℝ)*X 1 0+(-505910401/5000000000 : ℝ)*X 1 1+(5673454109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5204911233/10000000000 : ℝ)*X 2 0+(177295451/312500000 : ℝ)*X 2 1+(-1011820751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4041798457/10000000000 : ℝ)*X 0 0+(1283858589/2500000000 : ℝ)*X 0 1+(1557337199/5000000000 : ℝ)*X 0 2+(4041798457/10000000000 : ℝ)*X 1 0+(1283858589/2500000000 : ℝ)*X 1 1+(1557337199/5000000000 : ℝ)*X 1 2+(4041798457/10000000000 : ℝ)*X 2 0+(1283858589/2500000000 : ℝ)*X 2 1+(1557337199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (196790949007195924495581/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3973891/4000000000000 : ℝ)*(base1) + (742848137/50000000000000 : ℝ)*(base19) + (353510977/25000000000000 : ℝ)*(base23) + (51170539/20000000000000 : ℝ)*(upper3) + (176514029/100000000000000 : ℝ)*(upper5) + (460712154542097/50000000000000 : ℝ)*(major0) + (460712154542097/50000000000000 : ℝ)*(major1) + (460712154542097/50000000000000 : ℝ)*(major2) + (17157723884741/1250000000000 : ℝ)*(sp0) + (68631109748707/5000000000000 : ℝ)*(sp1) + (686311133313253/50000000000000 : ℝ)*(sp2) + (94044467887551/20000000000000 : ℝ)*(sp3) + (5869238409/100000000000000 : ℝ)*(sp4) + (447265001/20000000000000 : ℝ)*(sp7) + (235112337555017/50000000000000 : ℝ)*(f.failure) + (274524736134083/20000000000000 : ℝ)*(f.sum) + (9608486601473/25000000000000000000000000000 : ℝ)*base66 + (96466260126473/50000000000000000000000000000 : ℝ)*base68 + (236781124026473/50000000000000000000000000000 : ℝ)*base70 + (9012598073527/50000000000000000000000000000 : ℝ)*base71 + (5783658198527/25000000000000000000000000000 : ℝ)*base73 + (239965512823527/50000000000000000000000000000 : ℝ)*base75 + (95097660126473/50000000000000000000000000000 : ℝ)*base78 + (344461700873527/50000000000000000000000000000 : ℝ)*base79 + (12164310676473/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8366099/5000000000000000000000 : ℝ)*base90 + (8366099/5000000000000000000000 : ℝ)*base92 + (8366099/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46662777620981181/12500000000000000000000 : ℝ) := by norm_num
    linear_combination (1444400841/100000000000000 : ℝ)*(base19) + (1587858347/100000000000000 : ℝ)*(base23) + (106549847/100000000000000 : ℝ)*(upper2) + (108836769/50000000000000 : ℝ)*(upper3) + (117773379/50000000000000 : ℝ)*(upper5) + (242426103578797/25000000000000 : ℝ)*(major0) + (242426103578797/25000000000000 : ℝ)*(major1) + (242426103578797/25000000000000 : ℝ)*(major2) + (4831910217/100000000000000 : ℝ)*(sp1) + (1075189847/20000000000000 : ℝ)*(sp2) + (361136386624297/25000000000000 : ℝ)*(sp4) + (144453927018613/10000000000000 : ℝ)*(sp5) + (722269291344803/50000000000000 : ℝ)*(sp6) + (49486315769911/10000000000000 : ℝ)*(sp7) + (49486315769911/10000000000000 : ℝ)*(f.failure) + (361136386624297/25000000000000 : ℝ)*(f.sum) + (13224377041773/12500000000000000000000000000 : ℝ)*base66 + (15050437566773/25000000000000000000000000000 : ℝ)*base68 + (58757949966773/25000000000000000000000000000 : ℝ)*base70 + (66206059083227/25000000000000000000000000000 : ℝ)*base71 + (51023547620727/12500000000000000000000000000 : ℝ)*base73 + (50044141116773/25000000000000000000000000000 : ℝ)*base76 + (136252530316773/25000000000000000000000000000 : ℝ)*base78 + (53069826333227/25000000000000000000000000000 : ℝ)*base79 + (32773063645727/12500000000000000000000000000 : ℝ)*base81 + (4100717/1000000000000000000000 : ℝ)*base90 + (4100717/1000000000000000000000 : ℝ)*base92 + (4100717/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1713_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5451/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1713_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1713_s1_0 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1397912967/10000000000 : ℝ)*x 0 + (1096409451/2000000000 : ℝ)*x 1 + (1281751439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1397912967/10000000000 : ℝ)^5327 ≤ (8752397714929/100000000000000 : ℝ)^4303 := by
    have hnat : (1397912967 : ℕ)^5327*100000000000000^4303 ≤ 8752397714929^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397912967 10000000000 8752397714929 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096409451/2000000000 : ℝ)^5327 ≤ (23756807344151/50000000000000 : ℝ)^4303 := by
    have hnat : (1096409451 : ℕ)^5327*50000000000000^4303 ≤ 23756807344151^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096409451 2000000000 23756807344151 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281751439/2500000000 : ℝ)^5327 ≤ (21866993787593/50000000000000 : ℝ)^4303 := by
    have hnat : (1281751439 : ℕ)^5327*50000000000000^4303 ≤ 21866993787593^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281751439 2500000000 21866993787593 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1397912967/10000000000 : ℝ), (1096409451/2000000000 : ℝ), (1281751439/2500000000 : ℝ)] ![(8752397714929/100000000000000 : ℝ), (23756807344151/50000000000000 : ℝ), (21866993787593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1397912967/10000000000 : ℝ)|^5327 ≤ (8752397714929/100000000000000 : ℝ)^4303
        have hw : |(-1397912967/10000000000 : ℝ)|=(1397912967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096409451/2000000000 : ℝ)|^5327 ≤ (23756807344151/50000000000000 : ℝ)^4303
        have hw : |(1096409451/2000000000 : ℝ)|=(1096409451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281751439/2500000000 : ℝ)|^5327 ≤ (21866993787593/50000000000000 : ℝ)^4303
        have hw : |(1281751439/2500000000 : ℝ)|=(1281751439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_1 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346292377/10000000000 : ℝ)*x 0 + (-1582474387/10000000000 : ℝ)*x 1 + (5127004749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346292377/10000000000 : ℝ)^5327 ≤ (11515331983177/25000000000000 : ℝ)^4303 := by
    have hnat : (5346292377 : ℕ)^5327*25000000000000^4303 ≤ 11515331983177^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346292377 10000000000 11515331983177 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1582474387/10000000000 : ℝ)^5327 ≤ (5102347555679/50000000000000 : ℝ)^4303 := by
    have hnat : (1582474387 : ℕ)^5327*50000000000000^4303 ≤ 5102347555679^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582474387 10000000000 5102347555679 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127004749/10000000000 : ℝ)^5327 ≤ (109334942353/250000000000 : ℝ)^4303 := by
    have hnat : (5127004749 : ℕ)^5327*250000000000^4303 ≤ 109334942353^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127004749 10000000000 109334942353 250000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346292377/10000000000 : ℝ), (-1582474387/10000000000 : ℝ), (5127004749/10000000000 : ℝ)] ![(11515331983177/25000000000000 : ℝ), (5102347555679/50000000000000 : ℝ), (109334942353/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346292377/10000000000 : ℝ)|^5327 ≤ (11515331983177/25000000000000 : ℝ)^4303
        have hw : |(5346292377/10000000000 : ℝ)|=(5346292377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1582474387/10000000000 : ℝ)|^5327 ≤ (5102347555679/50000000000000 : ℝ)^4303
        have hw : |(-1582474387/10000000000 : ℝ)|=(1582474387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127004749/10000000000 : ℝ)|^5327 ≤ (109334942353/250000000000 : ℝ)^4303
        have hw : |(5127004749/10000000000 : ℝ)|=(5127004749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_2 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673145509/5000000000 : ℝ)*x 0 + (1281751473/2500000000 : ℝ)*x 1 + (-1582474691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673145509/5000000000 : ℝ)^5327 ≤ (46061313437831/100000000000000 : ℝ)^4303 := by
    have hnat : (2673145509 : ℕ)^5327*100000000000000^4303 ≤ 46061313437831^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673145509 5000000000 46061313437831 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281751473/2500000000 : ℝ)^5327 ≤ (8746797802271/20000000000000 : ℝ)^4303 := by
    have hnat : (1281751473 : ℕ)^5327*20000000000000^4303 ≤ 8746797802271^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281751473 2500000000 8746797802271 20000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1582474691/10000000000 : ℝ)^5327 ≤ (5102348769119/50000000000000 : ℝ)^4303 := by
    have hnat : (1582474691 : ℕ)^5327*50000000000000^4303 ≤ 5102348769119^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582474691 10000000000 5102348769119 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673145509/5000000000 : ℝ), (1281751473/2500000000 : ℝ), (-1582474691/10000000000 : ℝ)] ![(46061313437831/100000000000000 : ℝ), (8746797802271/20000000000000 : ℝ), (5102348769119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673145509/5000000000 : ℝ)|^5327 ≤ (46061313437831/100000000000000 : ℝ)^4303
        have hw : |(2673145509/5000000000 : ℝ)|=(2673145509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281751473/2500000000 : ℝ)|^5327 ≤ (8746797802271/20000000000000 : ℝ)^4303
        have hw : |(1281751473/2500000000 : ℝ)|=(1281751473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1582474691/10000000000 : ℝ)|^5327 ≤ (5102348769119/50000000000000 : ℝ)^4303
        have hw : |(-1582474691/10000000000 : ℝ)|=(1582474691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_3 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (512281077/1250000000 : ℝ)*x 0 + (3600602193/10000000000 : ℝ)*x 1 + (4636994969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512281077/1250000000 : ℝ)^5327 ≤ (6628831132763/20000000000000 : ℝ)^4303 := by
    have hnat : (512281077 : ℕ)^5327*20000000000000^4303 ≤ 6628831132763^4303*1250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512281077 1250000000 6628831132763 20000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3600602193/10000000000 : ℝ)^5327 ≤ (2823606535219/10000000000000 : ℝ)^4303 := by
    have hnat : (3600602193 : ℕ)^5327*10000000000000^4303 ≤ 2823606535219^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3600602193 10000000000 2823606535219 10000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4636994969/10000000000 : ℝ)^5327 ≤ (19309889482221/50000000000000 : ℝ)^4303 := by
    have hnat : (4636994969 : ℕ)^5327*50000000000000^4303 ≤ 19309889482221^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636994969 10000000000 19309889482221 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512281077/1250000000 : ℝ), (3600602193/10000000000 : ℝ), (4636994969/10000000000 : ℝ)] ![(6628831132763/20000000000000 : ℝ), (2823606535219/10000000000000 : ℝ), (19309889482221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512281077/1250000000 : ℝ)|^5327 ≤ (6628831132763/20000000000000 : ℝ)^4303
        have hw : |(512281077/1250000000 : ℝ)|=(512281077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3600602193/10000000000 : ℝ)|^5327 ≤ (2823606535219/10000000000000 : ℝ)^4303
        have hw : |(3600602193/10000000000 : ℝ)|=(3600602193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4636994969/10000000000 : ℝ)|^5327 ≤ (19309889482221/50000000000000 : ℝ)^4303
        have hw : |(4636994969/10000000000 : ℝ)|=(4636994969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_4 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1398100643/10000000000 : ℝ)*x 0 + (5131250603/10000000000 : ℝ)*x 1 + (5477733117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1398100643/10000000000 : ℝ)^5327 ≤ (8753852416599/100000000000000 : ℝ)^4303 := by
    have hnat : (1398100643 : ℕ)^5327*100000000000000^4303 ≤ 8753852416599^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398100643 10000000000 8753852416599 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131250603/10000000000 : ℝ)^5327 ≤ (43778817853709/100000000000000 : ℝ)^4303 := by
    have hnat : (5131250603 : ℕ)^5327*100000000000000^4303 ≤ 43778817853709^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131250603 10000000000 43778817853709 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477733117/10000000000 : ℝ)^5327 ≤ (23733664858213/50000000000000 : ℝ)^4303 := by
    have hnat : (5477733117 : ℕ)^5327*50000000000000^4303 ≤ 23733664858213^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477733117 10000000000 23733664858213 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1398100643/10000000000 : ℝ), (5131250603/10000000000 : ℝ), (5477733117/10000000000 : ℝ)] ![(8753852416599/100000000000000 : ℝ), (43778817853709/100000000000000 : ℝ), (23733664858213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1398100643/10000000000 : ℝ)|^5327 ≤ (8753852416599/100000000000000 : ℝ)^4303
        have hw : |(-1398100643/10000000000 : ℝ)|=(1398100643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131250603/10000000000 : ℝ)|^5327 ≤ (43778817853709/100000000000000 : ℝ)^4303
        have hw : |(5131250603/10000000000 : ℝ)|=(5131250603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477733117/10000000000 : ℝ)|^5327 ≤ (23733664858213/50000000000000 : ℝ)^4303
        have hw : |(5477733117/10000000000 : ℝ)|=(5477733117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_5 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656402271/1250000000 : ℝ)*x 0 + (-1231746483/10000000000 : ℝ)*x 1 + (1369433191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656402271/1250000000 : ℝ)^5327 ≤ (22524718503097/50000000000000 : ℝ)^4303 := by
    have hnat : (656402271 : ℕ)^5327*50000000000000^4303 ≤ 22524718503097^4303*1250000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656402271 1250000000 22524718503097 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1231746483/10000000000 : ℝ)^5327 ≤ (7483237046993/100000000000000 : ℝ)^4303 := by
    have hnat : (1231746483 : ℕ)^5327*100000000000000^4303 ≤ 7483237046993^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231746483 10000000000 7483237046993 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369433191/2500000000 : ℝ)^5327 ≤ (1186683148239/2500000000000 : ℝ)^4303 := by
    have hnat : (1369433191 : ℕ)^5327*2500000000000^4303 ≤ 1186683148239^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369433191 2500000000 1186683148239 2500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656402271/1250000000 : ℝ), (-1231746483/10000000000 : ℝ), (1369433191/2500000000 : ℝ)] ![(22524718503097/50000000000000 : ℝ), (7483237046993/100000000000000 : ℝ), (1186683148239/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656402271/1250000000 : ℝ)|^5327 ≤ (22524718503097/50000000000000 : ℝ)^4303
        have hw : |(656402271/1250000000 : ℝ)|=(656402271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1231746483/10000000000 : ℝ)|^5327 ≤ (7483237046993/100000000000000 : ℝ)^4303
        have hw : |(-1231746483/10000000000 : ℝ)|=(1231746483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369433191/2500000000 : ℝ)|^5327 ≤ (1186683148239/2500000000000 : ℝ)^4303
        have hw : |(1369433191/2500000000 : ℝ)|=(1369433191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_6 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312804603/2500000000 : ℝ)*x 0 + (2738866201/5000000000 : ℝ)*x 1 + (-38492083/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312804603/2500000000 : ℝ)^5327 ≤ (4504943959757/10000000000000 : ℝ)^4303 := by
    have hnat : (1312804603 : ℕ)^5327*10000000000000^4303 ≤ 4504943959757^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312804603 2500000000 4504943959757 10000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738866201/5000000000 : ℝ)^5327 ≤ (741676906971/1562500000000 : ℝ)^4303 := by
    have hnat : (2738866201 : ℕ)^5327*1562500000000^4303 ≤ 741676906971^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738866201 5000000000 741676906971 1562500000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38492083/312500000 : ℝ)^5327 ≤ (3741619174069/50000000000000 : ℝ)^4303 := by
    have hnat : (38492083 : ℕ)^5327*50000000000000^4303 ≤ 3741619174069^4303*312500000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38492083 312500000 3741619174069 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312804603/2500000000 : ℝ), (2738866201/5000000000 : ℝ), (-38492083/312500000 : ℝ)] ![(4504943959757/10000000000000 : ℝ), (741676906971/1562500000000 : ℝ), (3741619174069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312804603/2500000000 : ℝ)|^5327 ≤ (4504943959757/10000000000000 : ℝ)^4303
        have hw : |(1312804603/2500000000 : ℝ)|=(1312804603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738866201/5000000000 : ℝ)|^5327 ≤ (741676906971/1562500000000 : ℝ)^4303
        have hw : |(2738866201/5000000000 : ℝ)|=(2738866201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38492083/312500000 : ℝ)|^5327 ≤ (3741619174069/50000000000000 : ℝ)^4303
        have hw : |(-38492083/312500000 : ℝ)|=(38492083/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s1_7 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (819758549/2000000000 : ℝ)*x 0 + (2312301301/5000000000 : ℝ)*x 1 + (1806596449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819758549/2000000000 : ℝ)^5327 ≤ (33149603558999/100000000000000 : ℝ)^4303 := by
    have hnat : (819758549 : ℕ)^5327*100000000000000^4303 ≤ 33149603558999^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819758549 2000000000 33149603558999 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2312301301/5000000000 : ℝ)^5327 ≤ (38492046715611/100000000000000 : ℝ)^4303 := by
    have hnat : (2312301301 : ℕ)^5327*100000000000000^4303 ≤ 38492046715611^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312301301 5000000000 38492046715611 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1806596449/5000000000 : ℝ)^5327 ≤ (14179174859353/50000000000000 : ℝ)^4303 := by
    have hnat : (1806596449 : ℕ)^5327*50000000000000^4303 ≤ 14179174859353^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806596449 5000000000 14179174859353 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819758549/2000000000 : ℝ), (2312301301/5000000000 : ℝ), (1806596449/5000000000 : ℝ)] ![(33149603558999/100000000000000 : ℝ), (38492046715611/100000000000000 : ℝ), (14179174859353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819758549/2000000000 : ℝ)|^5327 ≤ (33149603558999/100000000000000 : ℝ)^4303
        have hw : |(819758549/2000000000 : ℝ)|=(819758549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2312301301/5000000000 : ℝ)|^5327 ≤ (38492046715611/100000000000000 : ℝ)^4303
        have hw : |(2312301301/5000000000 : ℝ)|=(2312301301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1806596449/5000000000 : ℝ)|^5327 ≤ (14179174859353/50000000000000 : ℝ)^4303
        have hw : |(1806596449/5000000000 : ℝ)|=(1806596449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1713_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5451/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (489/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4341/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5451/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5451/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5451/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5451/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5451/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5451/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6137/100000 : ℝ) ^ (5319/1024 : ℝ) ≤ (25305034729327/50000000000000000000 : ℝ) := by
    have hpowers : (6137/100000 : ℝ)^5319 ≤ (25305034729327/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6137 : ℕ)^5319*50000000000000000000^1024 ≤ 25305034729327^1024*100000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6137 100000 25305034729327 50000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6137/100000 : ℝ)) (X := (25305034729327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5451/25000 : ℝ) ^ (5319/1024 : ℝ) ≤ (3665512238733733/10000000000000000000 : ℝ) := by
    have hpowers : (5451/25000 : ℝ)^5319 ≤ (3665512238733733/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5451 : ℕ)^5319*10000000000000000000^1024 ≤ 3665512238733733^1024*25000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5451 25000 3665512238733733 10000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5451/25000 : ℝ)) (X := (3665512238733733/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000025305034729327/25000000000000000000 : ℝ) ≤ (2000000389732581/2000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (25000025305034729327/25000000000000000000 : ℝ)^1024 ≤ (2000000389732581/2000000000000000 : ℝ)^5319 := by
      have hnat : (25000025305034729327 : ℕ)^1024*2000000000000000^5319 ≤ 2000000389732581^5319*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000025305034729327 25000000000000000000 2000000389732581 2000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000389732581/2000000000000000 : ℝ)) (X := (25000025305034729327/25000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252294108278549749/6250000000000000000 : ℝ) ≤ (10000706544483277/10000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (6252294108278549749/6250000000000000000 : ℝ)^1024 ≤ (10000706544483277/10000000000000000 : ℝ)^5319 := by
      have hnat : (6252294108278549749 : ℕ)^1024*10000000000000000^5319 ≤ 10000706544483277^5319*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252294108278549749 6250000000000000000 10000706544483277 10000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706544483277/10000000000000000 : ℝ)) (X := (6252294108278549749/6250000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003665512238733733/5000000000000000000 : ℝ) ≤ (10001411140303649/10000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (5003665512238733733/5000000000000000000 : ℝ)^1024 ≤ (10001411140303649/10000000000000000 : ℝ)^5319 := by
      have hnat : (5003665512238733733 : ℕ)^1024*10000000000000000^5319 ≤ 10001411140303649^5319*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003665512238733733 5000000000000000000 10001411140303649 10000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001411140303649/10000000000000000 : ℝ)) (X := (5003665512238733733/5000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25305034729327/50000000000000000000 : ℝ) ≤ ((156661382320602486707/156670000000000000000 : ℝ)+2*(176148955093/391675000000000 : ℝ)*(6137/100000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (156661382320602486707/156670000000000000000 : ℝ)+2*(176148955093/391675000000000 : ℝ)*(6137/100000 : ℝ)=(2000000389732581/2000000000000000 : ℝ) by norm_num, show 1+2*(25305034729327/50000000000000000000 : ℝ)=(25000025305034729327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3665512238733733/10000000000000000000 : ℝ)+(25305034729327/50000000000000000000 : ℝ) ≤ ((156661382320602486707/156670000000000000000 : ℝ)+(176148955093/391675000000000 : ℝ)*((5451/25000 : ℝ)+(6137/100000 : ℝ)))^(5319/1024 : ℝ) := by
    rw [show (156661382320602486707/156670000000000000000 : ℝ)+(176148955093/391675000000000 : ℝ)*((5451/25000 : ℝ)+(6137/100000 : ℝ))=(10000706544483277/10000000000000000 : ℝ) by norm_num, show 1+(3665512238733733/10000000000000000000 : ℝ)+(25305034729327/50000000000000000000 : ℝ)=(6252294108278549749/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3665512238733733/10000000000000000000 : ℝ) ≤ ((156661382320602486707/156670000000000000000 : ℝ)+2*(176148955093/391675000000000 : ℝ)*(5451/25000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (156661382320602486707/156670000000000000000 : ℝ)+2*(176148955093/391675000000000 : ℝ)*(5451/25000 : ℝ)=(10001411140303649/10000000000000000 : ℝ) by norm_num, show 1+2*(3665512238733733/10000000000000000000 : ℝ)=(5003665512238733733/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (156661382320602486707/156670000000000000000 : ℝ)*(X 1 0+X 2 0)+(176148955093/391675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (6137/100000 : ℝ)) (hi := (5451/25000 : ℝ)) (c := (156661382320602486707/156670000000000000000 : ℝ)) (alpha := (176148955093/391675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (156661382320602486707/156670000000000000000 : ℝ)*(X 0 1+X 2 1)+(176148955093/391675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (6137/100000 : ℝ)) (hi := (5451/25000 : ℝ)) (c := (156661382320602486707/156670000000000000000 : ℝ)) (alpha := (176148955093/391675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (156661382320602486707/156670000000000000000 : ℝ)*(X 0 2+X 1 2)+(176148955093/391675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (6137/100000 : ℝ)) (hi := (5451/25000 : ℝ)) (c := (156661382320602486707/156670000000000000000 : ℝ)) (alpha := (176148955093/391675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1397912967/10000000000 : ℝ)*X 0 0+(1096409451/2000000000 : ℝ)*X 0 1+(1281751439/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346292377/10000000000 : ℝ)*X 1 0+(-1582474387/10000000000 : ℝ)*X 1 1+(5127004749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673145509/5000000000 : ℝ)*X 2 0+(1281751473/2500000000 : ℝ)*X 2 1+(-1582474691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((512281077/1250000000 : ℝ)*X 0 0+(3600602193/10000000000 : ℝ)*X 0 1+(4636994969/10000000000 : ℝ)*X 0 2+(512281077/1250000000 : ℝ)*X 1 0+(3600602193/10000000000 : ℝ)*X 1 1+(4636994969/10000000000 : ℝ)*X 1 2+(512281077/1250000000 : ℝ)*X 2 0+(3600602193/10000000000 : ℝ)*X 2 1+(4636994969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1398100643/10000000000 : ℝ)*X 0 0+(5131250603/10000000000 : ℝ)*X 0 1+(5477733117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656402271/1250000000 : ℝ)*X 1 0+(-1231746483/10000000000 : ℝ)*X 1 1+(1369433191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1312804603/2500000000 : ℝ)*X 2 0+(2738866201/5000000000 : ℝ)*X 2 1+(-38492083/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((819758549/2000000000 : ℝ)*X 0 0+(2312301301/5000000000 : ℝ)*X 0 1+(1806596449/5000000000 : ℝ)*X 0 2+(819758549/2000000000 : ℝ)*X 1 0+(2312301301/5000000000 : ℝ)*X 1 1+(1806596449/5000000000 : ℝ)*X 1 2+(819758549/2000000000 : ℝ)*X 2 0+(2312301301/5000000000 : ℝ)*X 2 1+(1806596449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91770036274337726148742093389/7833500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1180535157/100000000000000 : ℝ)*(base19) + (590085599/100000000000000 : ℝ)*(base23) + (88860801/100000000000000 : ℝ)*(lower2) + (190507971/100000000000000 : ℝ)*(upper3) + (31192583/20000000000000 : ℝ)*(lower4) + (1890735992903691/100000000000000 : ℝ)*(major0) + (1890735992903691/100000000000000 : ℝ)*(major1) + (1890735992903691/100000000000000 : ℝ)*(major2) + (704145324641749/25000000000000 : ℝ)*(sp0) + (56331660032911/2000000000000 : ℝ)*(sp1) + (2816583592095109/100000000000000 : ℝ)*(sp2) + (964886212284623/100000000000000 : ℝ)*(sp3) + (180225857/6250000000000 : ℝ)*(sp4) + (30020989/2500000000000 : ℝ)*(sp7) + (964887413124183/100000000000000 : ℝ)*(f.failure) + (704146045545177/25000000000000 : ℝ)*(f.sum) + (902714082443/1223984375000000000000000000 : ℝ)*base65 + (1135398885238935537/15667000000000000000000000000000000 : ℝ)*base67 + (84811934504514935537/15667000000000000000000000000000000 : ℝ)*base69 + (182692136305357935537/15667000000000000000000000000000000 : ℝ)*base71 + (54998578054463/78335000000000000000000000000 : ℝ)*base74 + (88518939878624935537/15667000000000000000000000000000000 : ℝ)*base75 + (46476257768846064463/15667000000000000000000000000000000 : ℝ)*base78 + (62988346042065064463/15667000000000000000000000000000000 : ℝ)*base80 + (67089436791493/19583750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (48836301/10000000000000000000000 : ℝ)*base90 + (48836301/10000000000000000000000 : ℝ)*base92 + (48836301/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11568698274602272938251845101/3916750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131469487/12500000000000 : ℝ)*(base19) + (741973071/50000000000000 : ℝ)*(base23) + (158370603/100000000000000 : ℝ)*(upper2) + (126332351/100000000000000 : ℝ)*(upper3) + (220086047/100000000000000 : ℝ)*(upper5) + (968716674753127/50000000000000 : ℝ)*(major0) + (968716674753127/50000000000000 : ℝ)*(major1) + (968716674753127/50000000000000 : ℝ)*(major2) + (1763608283/25000000000000 : ℝ)*(sp1) + (1715252343/25000000000000 : ℝ)*(sp2) + (1443074209500953/50000000000000 : ℝ)*(sp4) + (2886140312812879/100000000000000 : ℝ)*(sp5) + (360767509255799/12500000000000 : ℝ)*(sp6) + (988718181555681/100000000000000 : ℝ)*(sp7) + (988718181555681/100000000000000 : ℝ)*(f.failure) + (1443074209500953/50000000000000 : ℝ)*(f.sum) + (338039746223157/78335000000000000000000000000 : ℝ)*base66 + (66680291910031417211/7833500000000000000000000000000000 : ℝ)*base68 + (68284148237241417211/7833500000000000000000000000000000 : ℝ)*base70 + (86058988305114917211/7833500000000000000000000000000000 : ℝ)*base72 + (425886850434047/78335000000000000000000000000 : ℝ)*base74 + (91660020557978417211/7833500000000000000000000000000000 : ℝ)*base76 + (53886566951408917211/7833500000000000000000000000000000 : ℝ)*base78 + (60414777309046417211/7833500000000000000000000000000000 : ℝ)*base80 + (155020450848701/39167500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (137125093/10000000000000000000000 : ℝ)*base89 + (137125093/10000000000000000000000 : ℝ)*base91 + (137125093/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1713_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5451/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (489/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4341/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1713_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1713_s2_0 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-700593801/5000000000 : ℝ)*x 0 + (1367148309/2500000000 : ℝ)*x 1 + (5138264707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (700593801/5000000000 : ℝ)^5327 ≤ (17144114281/195312500000 : ℝ)^4303 := by
    have hnat : (700593801 : ℕ)^5327*195312500000^4303 ≤ 17144114281^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700593801 5000000000 17144114281 195312500000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367148309/2500000000 : ℝ)^5327 ≤ (94738599183/200000000000 : ℝ)^4303 := by
    have hnat : (1367148309 : ℕ)^5327*200000000000^4303 ≤ 94738599183^4303*2500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367148309 2500000000 94738599183 200000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138264707/10000000000 : ℝ)^5327 ≤ (43852913887747/100000000000000 : ℝ)^4303 := by
    have hnat : (5138264707 : ℕ)^5327*100000000000000^4303 ≤ 43852913887747^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138264707 10000000000 43852913887747 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-700593801/5000000000 : ℝ), (1367148309/2500000000 : ℝ), (5138264707/10000000000 : ℝ)] ![(17144114281/195312500000 : ℝ), (94738599183/200000000000 : ℝ), (43852913887747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-700593801/5000000000 : ℝ)|^5327 ≤ (17144114281/195312500000 : ℝ)^4303
        have hw : |(-700593801/5000000000 : ℝ)|=(700593801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367148309/2500000000 : ℝ)|^5327 ≤ (94738599183/200000000000 : ℝ)^4303
        have hw : |(1367148309/2500000000 : ℝ)|=(1367148309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138264707/10000000000 : ℝ)|^5327 ≤ (43852913887747/100000000000000 : ℝ)^4303
        have hw : |(5138264707/10000000000 : ℝ)|=(5138264707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_1 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267132071/500000000 : ℝ)*x 0 + (-786222859/5000000000 : ℝ)*x 1 + (5138264743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267132071/500000000 : ℝ)^5327 ≤ (5752798821381/12500000000000 : ℝ)^4303 := by
    have hnat : (267132071 : ℕ)^5327*12500000000000^4303 ≤ 5752798821381^4303*500000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267132071 500000000 5752798821381 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786222859/5000000000 : ℝ)^5327 ≤ (2531173783861/25000000000000 : ℝ)^4303 := by
    have hnat : (786222859 : ℕ)^5327*25000000000000^4303 ≤ 2531173783861^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786222859 5000000000 2531173783861 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138264743/10000000000 : ℝ)^5327 ≤ (10963228567027/25000000000000 : ℝ)^4303 := by
    have hnat : (5138264743 : ℕ)^5327*25000000000000^4303 ≤ 10963228567027^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138264743 10000000000 10963228567027 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267132071/500000000 : ℝ), (-786222859/5000000000 : ℝ), (5138264743/10000000000 : ℝ)] ![(5752798821381/12500000000000 : ℝ), (2531173783861/25000000000000 : ℝ), (10963228567027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267132071/500000000 : ℝ)|^5327 ≤ (5752798821381/12500000000000 : ℝ)^4303
        have hw : |(267132071/500000000 : ℝ)|=(267132071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-786222859/5000000000 : ℝ)|^5327 ≤ (2531173783861/25000000000000 : ℝ)^4303
        have hw : |(-786222859/5000000000 : ℝ)|=(786222859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138264743/10000000000 : ℝ)|^5327 ≤ (10963228567027/25000000000000 : ℝ)^4303
        have hw : |(5138264743/10000000000 : ℝ)|=(5138264743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_2 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342641637/10000000000 : ℝ)*x 0 + (2569132349/5000000000 : ℝ)*x 1 + (-98277843/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342641637/10000000000 : ℝ)^5327 ≤ (46022392885159/100000000000000 : ℝ)^4303 := by
    have hnat : (5342641637 : ℕ)^5327*100000000000000^4303 ≤ 46022392885159^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342641637 10000000000 46022392885159 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569132349/5000000000 : ℝ)^5327 ≤ (43852913792657/100000000000000 : ℝ)^4303 := by
    have hnat : (2569132349 : ℕ)^5327*100000000000000^4303 ≤ 43852913792657^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569132349 5000000000 43852913792657 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98277843/625000000 : ℝ)^5327 ≤ (5062346651047/50000000000000 : ℝ)^4303 := by
    have hnat : (98277843 : ℕ)^5327*50000000000000^4303 ≤ 5062346651047^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98277843 625000000 5062346651047 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342641637/10000000000 : ℝ), (2569132349/5000000000 : ℝ), (-98277843/625000000 : ℝ)] ![(46022392885159/100000000000000 : ℝ), (43852913792657/100000000000000 : ℝ), (5062346651047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342641637/10000000000 : ℝ)|^5327 ≤ (46022392885159/100000000000000 : ℝ)^4303
        have hw : |(5342641637/10000000000 : ℝ)|=(5342641637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569132349/5000000000 : ℝ)|^5327 ≤ (43852913792657/100000000000000 : ℝ)^4303
        have hw : |(2569132349/5000000000 : ℝ)|=(2569132349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98277843/625000000 : ℝ)|^5327 ≤ (5062346651047/50000000000000 : ℝ)^4303
        have hw : |(-98277843/625000000 : ℝ)|=(98277843/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_3 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (256299253/625000000 : ℝ)*x 0 + (3636448039/10000000000 : ℝ)*x 1 + (287543971/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256299253/625000000 : ℝ)^5327 ≤ (16584791141291/50000000000000 : ℝ)^4303 := by
    have hnat : (256299253 : ℕ)^5327*50000000000000^4303 ≤ 16584791141291^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256299253 625000000 16584791141291 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3636448039/10000000000 : ℝ)^5327 ≤ (7146119132153/25000000000000 : ℝ)^4303 := by
    have hnat : (3636448039 : ℕ)^5327*25000000000000^4303 ≤ 7146119132153^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3636448039 10000000000 7146119132153 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287543971/625000000 : ℝ)^5327 ≤ (9561485294969/25000000000000 : ℝ)^4303 := by
    have hnat : (287543971 : ℕ)^5327*25000000000000^4303 ≤ 9561485294969^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287543971 625000000 9561485294969 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256299253/625000000 : ℝ), (3636448039/10000000000 : ℝ), (287543971/625000000 : ℝ)] ![(16584791141291/50000000000000 : ℝ), (7146119132153/25000000000000 : ℝ), (9561485294969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256299253/625000000 : ℝ)|^5327 ≤ (16584791141291/50000000000000 : ℝ)^4303
        have hw : |(256299253/625000000 : ℝ)|=(256299253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3636448039/10000000000 : ℝ)|^5327 ≤ (7146119132153/25000000000000 : ℝ)^4303
        have hw : |(3636448039/10000000000 : ℝ)|=(3636448039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287543971/625000000 : ℝ)|^5327 ≤ (9561485294969/25000000000000 : ℝ)^4303
        have hw : |(287543971/625000000 : ℝ)|=(287543971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_4 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1401337629/10000000000 : ℝ)*x 0 + (5141942103/10000000000 : ℝ)*x 1 + (341553803/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1401337629/10000000000 : ℝ)^5327 ≤ (8778950035043/100000000000000 : ℝ)^4303 := by
    have hnat : (1401337629 : ℕ)^5327*100000000000000^4303 ≤ 8778950035043^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401337629 10000000000 8778950035043 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141942103/10000000000 : ℝ)^5327 ≤ (21945885508293/50000000000000 : ℝ)^4303 := by
    have hnat : (5141942103 : ℕ)^5327*50000000000000^4303 ≤ 21945885508293^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141942103 10000000000 21945885508293 50000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341553803/625000000 : ℝ)^5327 ≤ (47329278935711/100000000000000 : ℝ)^4303 := by
    have hnat : (341553803 : ℕ)^5327*100000000000000^4303 ≤ 47329278935711^4303*625000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341553803 625000000 47329278935711 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1401337629/10000000000 : ℝ), (5141942103/10000000000 : ℝ), (341553803/625000000 : ℝ)] ![(8778950035043/100000000000000 : ℝ), (21945885508293/50000000000000 : ℝ), (47329278935711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1401337629/10000000000 : ℝ)|^5327 ≤ (8778950035043/100000000000000 : ℝ)^4303
        have hw : |(-1401337629/10000000000 : ℝ)|=(1401337629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141942103/10000000000 : ℝ)|^5327 ≤ (21945885508293/50000000000000 : ℝ)^4303
        have hw : |(5141942103/10000000000 : ℝ)|=(5141942103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341553803/625000000 : ℝ)|^5327 ≤ (47329278935711/100000000000000 : ℝ)^4303
        have hw : |(341553803/625000000 : ℝ)|=(341553803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_5 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254215453/10000000000 : ℝ)*x 0 + (-622924689/5000000000 : ℝ)*x 1 + (5464860807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254215453/10000000000 : ℝ)^5327 ≤ (45081271517457/100000000000000 : ℝ)^4303 := by
    have hnat : (5254215453 : ℕ)^5327*100000000000000^4303 ≤ 45081271517457^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254215453 10000000000 45081271517457 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622924689/5000000000 : ℝ)^5327 ≤ (1517889992943/20000000000000 : ℝ)^4303 := by
    have hnat : (622924689 : ℕ)^5327*20000000000000^4303 ≤ 1517889992943^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622924689 5000000000 1517889992943 20000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464860807/10000000000 : ℝ)^5327 ≤ (47329278496123/100000000000000 : ℝ)^4303 := by
    have hnat : (5464860807 : ℕ)^5327*100000000000000^4303 ≤ 47329278496123^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464860807 10000000000 47329278496123 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254215453/10000000000 : ℝ), (-622924689/5000000000 : ℝ), (5464860807/10000000000 : ℝ)] ![(45081271517457/100000000000000 : ℝ), (1517889992943/20000000000000 : ℝ), (47329278496123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254215453/10000000000 : ℝ)|^5327 ≤ (45081271517457/100000000000000 : ℝ)^4303
        have hw : |(5254215453/10000000000 : ℝ)|=(5254215453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-622924689/5000000000 : ℝ)|^5327 ≤ (1517889992943/20000000000000 : ℝ)^4303
        have hw : |(-622924689/5000000000 : ℝ)|=(622924689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464860807/10000000000 : ℝ)|^5327 ≤ (47329278496123/100000000000000 : ℝ)^4303
        have hw : |(5464860807/10000000000 : ℝ)|=(5464860807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_6 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105084309/200000000 : ℝ)*x 0 + (2732430397/5000000000 : ℝ)*x 1 + (-1245849403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105084309/200000000 : ℝ)^5327 ≤ (5635158935699/12500000000000 : ℝ)^4303 := by
    have hnat : (105084309 : ℕ)^5327*12500000000000^4303 ≤ 5635158935699^4303*200000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105084309 200000000 5635158935699 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732430397/5000000000 : ℝ)^5327 ≤ (47329278356741/100000000000000 : ℝ)^4303 := by
    have hnat : (2732430397 : ℕ)^5327*100000000000000^4303 ≤ 47329278356741^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732430397 5000000000 47329278356741 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245849403/10000000000 : ℝ)^5327 ≤ (1897362538313/25000000000000 : ℝ)^4303 := by
    have hnat : (1245849403 : ℕ)^5327*25000000000000^4303 ≤ 1897362538313^4303*10000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245849403 10000000000 1897362538313 25000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105084309/200000000 : ℝ), (2732430397/5000000000 : ℝ), (-1245849403/10000000000 : ℝ)] ![(5635158935699/12500000000000 : ℝ), (47329278356741/100000000000000 : ℝ), (1897362538313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105084309/200000000 : ℝ)|^5327 ≤ (5635158935699/12500000000000 : ℝ)^4303
        have hw : |(105084309/200000000 : ℝ)|=(105084309/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732430397/5000000000 : ℝ)|^5327 ≤ (47329278356741/100000000000000 : ℝ)^4303
        have hw : |(2732430397/5000000000 : ℝ)|=(2732430397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1245849403/10000000000 : ℝ)|^5327 ≤ (1897362538313/25000000000000 : ℝ)^4303
        have hw : |(-1245849403/10000000000 : ℝ)|=(1245849403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1713_s2_7 (p : ℝ) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2050612971/5000000000 : ℝ)*x 0 + (183598753/400000000 : ℝ)*x 1 + (729468617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050612971/5000000000 : ℝ)^5327 ≤ (414674589637/1250000000000 : ℝ)^4303 := by
    have hnat : (2050612971 : ℕ)^5327*1250000000000^4303 ≤ 414674589637^4303*5000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050612971 5000000000 414674589637 1250000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183598753/400000000 : ℝ)^5327 ≤ (38135497173951/100000000000000 : ℝ)^4303 := by
    have hnat : (183598753 : ℕ)^5327*100000000000000^4303 ≤ 38135497173951^4303*400000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183598753 400000000 38135497173951 100000000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729468617/2000000000 : ℝ)^5327 ≤ (3586316954063/12500000000000 : ℝ)^4303 := by
    have hnat : (729468617 : ℕ)^5327*12500000000000^4303 ≤ 3586316954063^4303*2000000000^5327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729468617 2000000000 3586316954063 12500000000000 5327 4303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5327/1024 : ℝ)) 5327 4303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2050612971/5000000000 : ℝ), (183598753/400000000 : ℝ), (729468617/2000000000 : ℝ)] ![(414674589637/1250000000000 : ℝ), (38135497173951/100000000000000 : ℝ), (3586316954063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2050612971/5000000000 : ℝ)|^5327 ≤ (414674589637/1250000000000 : ℝ)^4303
        have hw : |(2050612971/5000000000 : ℝ)|=(2050612971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183598753/400000000 : ℝ)|^5327 ≤ (38135497173951/100000000000000 : ℝ)^4303
        have hw : |(183598753/400000000 : ℝ)|=(183598753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(729468617/2000000000 : ℝ)|^5327 ≤ (3586316954063/12500000000000 : ℝ)^4303
        have hw : |(729468617/2000000000 : ℝ)|=(729468617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1713_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4341/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (401/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4341/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (489/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4341/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (489/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4341/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (489/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4341/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (489/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4341/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (489/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4341/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (489/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (489/5000 : ℝ) ^ (5319/1024 : ℝ) ≤ (569483084602147/100000000000000000000 : ℝ) := by
    have hpowers : (489/5000 : ℝ)^5319 ≤ (569483084602147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (489 : ℕ)^5319*100000000000000000000^1024 ≤ 569483084602147^1024*5000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        489 5000 569483084602147 100000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (489/5000 : ℝ)) (X := (569483084602147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4341/25000 : ℝ) ^ (5319/1024 : ℝ) ≤ (11232734979763489/100000000000000000000 : ℝ) := by
    have hpowers : (4341/25000 : ℝ)^5319 ≤ (11232734979763489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4341 : ℕ)^5319*100000000000000000000^1024 ≤ 11232734979763489^1024*25000^5319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4341 25000 11232734979763489 100000000000000000000 5319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4341/25000 : ℝ)) (X := (11232734979763489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000569483084602147/50000000000000000000 : ℝ) ≤ (2000004385395729/2000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (50000569483084602147/50000000000000000000 : ℝ)^1024 ≤ (2000004385395729/2000000000000000 : ℝ)^5319 := by
      have hnat : (50000569483084602147 : ℕ)^1024*2000000000000000^5319 ≤ 2000004385395729^5319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000569483084602147 50000000000000000000 2000004385395729 2000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000004385395729/2000000000000000 : ℝ)) (X := (50000569483084602147/50000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002950554516091409/25000000000000000000 : ℝ) ≤ (5000113601198167/5000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (25002950554516091409/25000000000000000000 : ℝ)^1024 ≤ (5000113601198167/5000000000000000 : ℝ)^5319 := by
      have hnat : (25002950554516091409 : ℕ)^1024*5000000000000000^5319 ≤ 5000113601198167^5319*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002950554516091409 25000000000000000000 5000113601198167 5000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000113601198167/5000000000000000 : ℝ)) (X := (25002950554516091409/25000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011232734979763489/50000000000000000000 : ℝ) ≤ (10000432477814023/10000000000000000 : ℝ) ^ (5319/1024 : ℝ) := by
    have hpowers : (50011232734979763489/50000000000000000000 : ℝ)^1024 ≤ (10000432477814023/10000000000000000 : ℝ)^5319 := by
      have hnat : (50011232734979763489 : ℕ)^1024*10000000000000000^5319 ≤ 10000432477814023^5319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011232734979763489 50000000000000000000 10000432477814023 10000000000000000 1024 5319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000432477814023/10000000000000000 : ℝ)) (X := (50011232734979763489/50000000000000000000 : ℝ)) (by norm_num) 5319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(569483084602147/100000000000000000000 : ℝ) ≤ ((631967925891967057/632000000000000000 : ℝ)+2*(205275417689/758400000000000 : ℝ)*(489/5000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (631967925891967057/632000000000000000 : ℝ)+2*(205275417689/758400000000000 : ℝ)*(489/5000 : ℝ)=(2000004385395729/2000000000000000 : ℝ) by norm_num, show 1+2*(569483084602147/100000000000000000000 : ℝ)=(50000569483084602147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11232734979763489/100000000000000000000 : ℝ)+(569483084602147/100000000000000000000 : ℝ) ≤ ((631967925891967057/632000000000000000 : ℝ)+(205275417689/758400000000000 : ℝ)*((4341/25000 : ℝ)+(489/5000 : ℝ)))^(5319/1024 : ℝ) := by
    rw [show (631967925891967057/632000000000000000 : ℝ)+(205275417689/758400000000000 : ℝ)*((4341/25000 : ℝ)+(489/5000 : ℝ))=(5000113601198167/5000000000000000 : ℝ) by norm_num, show 1+(11232734979763489/100000000000000000000 : ℝ)+(569483084602147/100000000000000000000 : ℝ)=(25002950554516091409/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11232734979763489/100000000000000000000 : ℝ) ≤ ((631967925891967057/632000000000000000 : ℝ)+2*(205275417689/758400000000000 : ℝ)*(4341/25000 : ℝ))^(5319/1024 : ℝ) := by
    rw [show (631967925891967057/632000000000000000 : ℝ)+2*(205275417689/758400000000000 : ℝ)*(4341/25000 : ℝ)=(10000432477814023/10000000000000000 : ℝ) by norm_num, show 1+2*(11232734979763489/100000000000000000000 : ℝ)=(50011232734979763489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (631967925891967057/632000000000000000 : ℝ)*(X 1 0+X 2 0)+(205275417689/758400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (489/5000 : ℝ)) (hi := (4341/25000 : ℝ)) (c := (631967925891967057/632000000000000000 : ℝ)) (alpha := (205275417689/758400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (631967925891967057/632000000000000000 : ℝ)*(X 0 1+X 2 1)+(205275417689/758400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (489/5000 : ℝ)) (hi := (4341/25000 : ℝ)) (c := (631967925891967057/632000000000000000 : ℝ)) (alpha := (205275417689/758400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (631967925891967057/632000000000000000 : ℝ)*(X 0 2+X 1 2)+(205275417689/758400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5319/1024 : ℝ)) (lo := (489/5000 : ℝ)) (hi := (4341/25000 : ℝ)) (c := (631967925891967057/632000000000000000 : ℝ)) (alpha := (205275417689/758400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-700593801/5000000000 : ℝ)*X 0 0+(1367148309/2500000000 : ℝ)*X 0 1+(5138264707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267132071/500000000 : ℝ)*X 1 0+(-786222859/5000000000 : ℝ)*X 1 1+(5138264743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5342641637/10000000000 : ℝ)*X 2 0+(2569132349/5000000000 : ℝ)*X 2 1+(-98277843/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((256299253/625000000 : ℝ)*X 0 0+(3636448039/10000000000 : ℝ)*X 0 1+(287543971/625000000 : ℝ)*X 0 2+(256299253/625000000 : ℝ)*X 1 0+(3636448039/10000000000 : ℝ)*X 1 1+(287543971/625000000 : ℝ)*X 1 2+(256299253/625000000 : ℝ)*X 2 0+(3636448039/10000000000 : ℝ)*X 2 1+(287543971/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1401337629/10000000000 : ℝ)*X 0 0+(5141942103/10000000000 : ℝ)*X 0 1+(341553803/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254215453/10000000000 : ℝ)*X 1 0+(-622924689/5000000000 : ℝ)*X 1 1+(5464860807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105084309/200000000 : ℝ)*X 2 0+(2732430397/5000000000 : ℝ)*X 2 1+(-1245849403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2050612971/5000000000 : ℝ)*X 0 0+(183598753/400000000 : ℝ)*X 0 1+(729468617/2000000000 : ℝ)*X 0 2+(2050612971/5000000000 : ℝ)*X 1 0+(183598753/400000000 : ℝ)*X 1 1+(729468617/2000000000 : ℝ)*X 1 2+(2050612971/5000000000 : ℝ)*X 2 0+(183598753/400000000 : ℝ)*X 2 1+(729468617/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1713_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (427338380741210361935515347/31600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (345168429/20000000000000 : ℝ)*(base19) + (213476311/12500000000000 : ℝ)*(base23) + (470791/625000000000 : ℝ)*(lower2) + (234520191/100000000000000 : ℝ)*(upper3) + (297169041/100000000000000 : ℝ)*(upper5) + (2032202837973343/100000000000000 : ℝ)*(major0) + (2032202837973343/100000000000000 : ℝ)*(major1) + (2032202837973343/100000000000000 : ℝ)*(major2) + (1513652541178861/50000000000000 : ℝ)*(sp0) + (1513661100245041/50000000000000 : ℝ)*(sp1) + (151366110926087/5000000000000 : ℝ)*(sp2) + (64817208032593/6250000000000 : ℝ)*(sp3) + (3768794901/20000000000000 : ℝ)*(sp4) + (5970314083/100000000000000 : ℝ)*(sp7) + (1037081298835571/100000000000000 : ℝ)*(f.failure) + (756830981583057/25000000000000 : ℝ)*(f.sum) + (51382781107993/37920000000000000000000000000 : ℝ)*base66 + (1127677105566902153/189600000000000000000000000000000 : ℝ)*base67 + (340293256358102153/189600000000000000000000000000000 : ℝ)*base69 + (722153774181302153/189600000000000000000000000000000 : ℝ)*base71 + (44461903136807/37920000000000000000000000000 : ℝ)*base73 + (98443054770902153/189600000000000000000000000000000 : ℝ)*base75 + (97163177642697847/189600000000000000000000000000000 : ℝ)*base78 + (1111097343057897847/189600000000000000000000000000000 : ℝ)*base80 + (31976583369433/37920000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (18019263/10000000000000000000000 : ℝ)*base89 + (18019263/10000000000000000000000 : ℝ)*base91 + (18019263/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3418667242034168091140967/1264000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (322260997/100000000000000 : ℝ)*(base19) + (177750923/50000000000000 : ℝ)*(base23) + (38488291/100000000000000 : ℝ)*(upper3) + (20115107/100000000000000 : ℝ)*(lower4) + (60503047/100000000000000 : ℝ)*(upper5) + (83152414343877/4000000000000 : ℝ)*(major0) + (83152414343877/4000000000000 : ℝ)*(major1) + (83152414343877/4000000000000 : ℝ)*(major2) + (726929027/25000000000000 : ℝ)*(sp1) + (339140749/12500000000000 : ℝ)*(sp2) + (193547150325153/6250000000000 : ℝ)*(sp4) + (756042767389/24414062500 : ℝ)*(sp5) + (309675133657461/10000000000000 : ℝ)*(sp6) + (106086622183667/10000000000000 : ℝ)*(sp7) + (106086622183667/10000000000000 : ℝ)*(f.failure) + (193547150325153/6250000000000 : ℝ)*(f.sum) + (4696738198011/2528000000000000000000000000 : ℝ)*base65 + (16748305679494511/2528000000000000000000000000000 : ℝ)*base68 + (723202965625489/2528000000000000000000000000000 : ℝ)*base69 + (8243219874758511/2528000000000000000000000000000 : ℝ)*base72 + (16487330034117/2528000000000000000000000000 : ℝ)*base74 + (16010430278918511/2528000000000000000000000000000 : ℝ)*base76 + (2736778842694511/2528000000000000000000000000000 : ℝ)*base78 + (6623553317369489/2528000000000000000000000000000 : ℝ)*base79 + (9836652086917/2528000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9052351/1000000000000000000000 : ℝ)*base89 + (9052351/1000000000000000000000 : ℝ)*base91 + (9052351/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1713_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4341/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1713_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1713_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1713_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1713_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1713_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5319/1024 : ℝ) ≤ p) (hpb : p ≤ (5327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195954053/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (401/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1713_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
